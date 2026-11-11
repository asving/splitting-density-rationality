#!/usr/bin/env python3
"""Statement text of every declaration, for toolchain-independent statement-preservation checks.

`tools/StmtDump.lean` compares kernel-term hashes, which change whenever Lean or Mathlib changes.
This tool compares source text instead: for a theorem or lemma, the signature up to the proof's
`:=`; for a def, abbrev, structure, inductive or instance, the whole declaration. A port to a new
toolchain that only repairs proofs leaves every statement text unchanged.

  tools/stmt_text.py dump OUT.json         record the statements of the working tree
  tools/stmt_text.py compare REF.json [--allow REWRITES.json]
                                           compare the working tree with a recorded reference.
                                           Differences in whitespace only are counted separately.
                                           REWRITES.json lists accepted rewrites as
                                           {"file::name": {"old": ..., "new": ..., "reason": ...}};
                                           a listed rewrite must match both texts exactly.
                                           Exit code 1 if any other statement changed or was removed.

Run from the repository root. The parser is line-based and knows only this codebase's conventions
(declarations start in column 0; `namespace`/`section`/`end` on their own lines).
"""
import json, os, re, sys

IDENT = r"[^\W\d][\w'!?]*(?:\.[\w'!?]+)*"

def split_comments(lines):
    """For each line: (state at line start, list of (kind, text)) with kind in {None, 'com', 'doc'}
    describing the block-comment structure (line comments are left to the tokenizer)."""
    segs_all, starts = [], []
    kind = None  # None | 'com' | 'doc'
    for line in lines:
        starts.append(kind)
        segs = []
        i = 0
        cur = 0
        while i < len(line):
            if kind is None:
                j = line.find('/-', i)
                k = line.find('--', i)
                q = line.find('"', i)
                cands = [x for x in (j, k, q) if x != -1]
                if not cands:
                    break
                first = min(cands)
                if first == q and q != j:
                    m = re.match(r'"(?:\\.|[^"\\])*"', line[q:])
                    i = q + (len(m.group(0)) if m else 1)
                    continue
                if first == k and (j == -1 or k < j):
                    break  # the rest of the line is a line comment
                if j > cur:
                    segs.append((None, line[cur:j]))
                kind = 'doc' if line.startswith('/--', j) or line.startswith('/-!', j) else 'com'
                cur = j
                i = j + 2
            else:
                e = line.find('-/', i)
                if e == -1:
                    break
                segs.append((kind, line[cur:e + 2]))
                kind = None
                cur = e + 2
                i = e + 2
        if cur < len(line):
            segs.append((kind, line[cur:]))
        segs_all.append(segs)
    return segs_all, starts


class Decl:
    pass


DECL_LINE_RE = re.compile(
    r'^(?P<attrs>(?:@\[[^\]]*\]\s*)*)(?P<mods>(?:(?:private|noncomputable|protected|local|scoped)\s+)*)'
    r'(?P<kw>theorem|lemma|def|abbrev|structure|inductive|instance)\b\s*(?P<rest>.*)$')


def parse_file(root, rel):
    """Return (lines, decls, module_title)."""
    text = open(os.path.join(root, rel), encoding='utf-8').read()
    lines = text.split('\n')
    if lines and lines[-1] == '':
        lines = lines[:-1]
    segs, in_block = split_comments(lines)
    stack = []  # entries: ('namespace', name) | ('section', name)
    decls = []
    title = None
    for idx, line in enumerate(lines):
        if in_block[idx] is not None:
            continue
        s = line
        m = re.match(r'^namespace\s+(\S+)', s)
        if m:
            stack.append(('namespace', m.group(1)))
            continue
        m = re.match(r'^(?:noncomputable\s+)?section\b\s*(\S*)', s)
        if m:
            stack.append(('section', m.group(1)))
            continue
        m = re.match(r'^end\b\s*(\S*)', s)
        if m:
            if stack:
                stack.pop()
            continue
        m = DECL_LINE_RE.match(s)
        if not m:
            continue
        kw = m.group('kw')
        rest = m.group('rest')
        nm = re.match(IDENT, rest)
        nsname = '.'.join(x[1] for x in stack if x[0] == 'namespace')
        d = Decl()
        d.kind = kw
        d.private = 'private' in m.group('mods').split()
        d.file = rel
        d.decl_line = idx + 1
        d.namespace = nsname
        if kw == 'instance' and (nm is None or nm.group(0) in ()):
            d.short = 'instance@L%d' % (idx + 1)
        elif nm is None:
            d.short = '%s@L%d' % (kw, idx + 1)
        else:
            d.short = nm.group(0)
        if d.short.startswith('_root_.'):
            d.name = d.short[len('_root_.'):]
        else:
            d.name = (nsname + '.' if nsname else '') + d.short
        decls.append(d)
    return lines, segs, decls


CMD_START = re.compile(
    r'^(?:@\[|/--|/-!|/-|--|theorem\b|lemma\b|def\b|abbrev\b|structure\b|inductive\b|instance\b|'
    r'private\b|noncomputable\b|protected\b|namespace\b|section\b|end\b|variable\b|open\b|omit\b|'
    r'include\b|local\b|scoped\b|attribute\b|set_option\b|macro\b|notation\b|#|import\b|universe\b)')

def cut_statement(text, fix_let=False):
    """Signature of a theorem: the text before the first ` :=` at bracket depth 0."""
    depth = 0
    i = 0
    line_start = 0
    while i < len(text):
        ch = text[i]
        if ch in '([{⟨':
            depth += 1
        elif ch in ')]}⟩':
            depth -= 1
        elif ch == '\n':
            line_start = i + 1
        elif ch == ':' and text.startswith(':=', i) and depth == 0:
            if fix_let and re.match(r'\s*(letI|haveI|let|have)\b', text[line_start:i]):
                i += 2
                continue
            return text[:i].rstrip()
        i += 1
    return text.rstrip()

def annotate(lines, segs, starts, decls, fix_let=False):
    """Fill line_start, line_end, docstring, statement, section_variables on each Decl."""
    n = len(lines)
    # --- section variables: scopes follow section/namespace/end
    scopes = [[]]
    var_at = {}
    i = 0
    decl_lines = {d.decl_line: d for d in decls}
    while i < n:
        line = lines[i]
        if starts[i] is None:
            if re.match(r'^namespace\b', line) or re.match(r'^(?:noncomputable\s+)?section\b', line):
                scopes.append([])
            elif re.match(r'^end\b', line):
                if len(scopes) > 1:
                    scopes.pop()
            elif line.startswith('variable'):
                j = i + 1
                while j < n and lines[j].startswith((' ', '\t')) and lines[j].strip() != '':
                    j += 1
                scopes[-1].append('\n'.join(lines[i:j]))
                i = j
                continue
            if (i + 1) in decl_lines:
                var_at[i + 1] = '\n'.join(v for sc in scopes for v in sc)
        i += 1
    for d in decls:
        k = d.decl_line - 1
        # docstring: the doc comment ending on the line just above the declaration (attributes may intervene)
        s = k - 1
        while s >= 0 and lines[s].startswith('@['):
            s -= 1
        d.docstring = ''
        d.line_start = d.decl_line
        if s >= 0 and lines[s].rstrip().endswith('-/'):
            t = s
            while t >= 0 and not lines[t].startswith('/--') and not (starts[t] is None and '/--' in lines[t]):
                t -= 1
            if t >= 0 and lines[t].startswith('/--'):
                body = '\n'.join(lines[t:s + 1])
                body = body[3:]
                body = body[:body.rindex('-/')]
                d.docstring = body.strip()
                d.line_start = t + 1
        # extent: up to the line before the next command at column 0 (trailing blank lines dropped)
        e = k + 1
        while e < n:
            if starts[e] is None and CMD_START.match(lines[e]):
                break
            if starts[e] is None and lines[e] != '' and not lines[e].startswith((' ', '\t')):
                break
            e += 1
        e -= 1
        while e > k and lines[e].strip() == '':
            e -= 1
        d.line_end = e + 1
        full = '\n'.join(lines[k:e + 1])
        if d.kind in ('theorem', 'lemma'):
            d.statement = cut_statement(full, fix_let)
        else:
            d.statement = full
        d.section_variables = var_at.get(d.decl_line, '')
    return decls


def dump(repo='.'):
    out = {}
    for top in ('SurfaceBlowup', 'Tests'):
        for dp, dn, fn in os.walk(os.path.join(repo, top)):
            for f in sorted(fn):
                if not f.endswith('.lean'):
                    continue
                rel = os.path.relpath(os.path.join(dp, f), repo)
                lines, segs, decls = parse_file(repo, rel)
                _, starts = split_comments(lines)
                annotate(lines, segs, starts, decls, True)
                for d in decls:
                    out.setdefault(rel + '::' + d.name, []).append(
                        {'kind': d.kind, 'private': d.private, 'statement': d.statement})
    return out


def norm(text):
    """Collapse every run of whitespace to one space (line breaks and indentation do not matter)."""
    return re.sub(r'\s+', ' ', text).strip()


def main(argv):
    if len(argv) == 3 and argv[1] == 'dump':
        d = dump()
        json.dump(d, open(argv[2], 'w', encoding='utf-8'), ensure_ascii=False, indent=0, sort_keys=True)
        print('recorded %d declarations in %s' % (len(d), argv[2]))
        return 0
    if len(argv) in (3, 5) and argv[1] == 'compare' and (len(argv) == 3 or argv[3] == '--allow'):
        ref = json.load(open(argv[2], encoding='utf-8'))
        allow = json.load(open(argv[4], encoding='utf-8')) if len(argv) == 5 else {}
        cur = dump()
        removed = sorted(k for k in ref if k not in cur)
        added = sorted(k for k in cur if k not in ref)
        changed = sorted(k for k in ref if k in cur and ref[k] != cur[k])
        def texts(v):
            return [(x['kind'], x['private'], norm(x['statement'])) for x in v]
        white = [k for k in changed if texts(ref[k]) == texts(cur[k])]
        other = [k for k in changed if k not in white]
        allowed, bad = [], []
        for k in other:
            a = allow.get(k)
            ok = (a is not None and len(ref[k]) == 1 and len(cur[k]) == 1
                  and norm(ref[k][0]['statement']) == norm(a['old']) and norm(cur[k][0]['statement']) == norm(a['new']))
            (allowed if ok else bad).append(k)
        npub = sum(1 for k in ref if not ref[k][0]['private'])
        print('reference: %d declarations (%d public); working tree: %d' % (len(ref), npub, len(cur)))
        print('statement text identical: %d; whitespace-only differences: %d; listed rewrites: %d; other changes: %d; removed: %d; added: %d'
              % (len(ref) - len(removed) - len(changed), len(white), len(allowed), len(bad), len(removed), len(added)))
        for label, ks, table in (('WHITESPACE', white, ref), ('LISTED', allowed, ref), ('CHANGED', bad, ref),
                                 ('REMOVED', removed, ref), ('ADDED', added, cur)):
            for k in ks:
                print('%s %s %s %s' % (label, 'private' if table[k][0]['private'] else 'public', table[k][0]['kind'], k))
        return 1 if (bad or removed) else 0
    print(__doc__)
    return 2


if __name__ == '__main__':
    sys.exit(main(sys.argv))
