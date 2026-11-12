"""Tokenizer and declaration parser for the Lean sources, as the site highlights and links them.

Text level only: nothing here runs Lean. The rules are a reconstruction of the original generator's
(see README.md). `test_identity.sh` checks them against that generator's last output.
"""
import os
import re

KW = {'abbrev', 'at', 'attribute', 'by', 'calc', 'def', 'deriving', 'do', 'else', 'end', 'from',
      'fun', 'have', 'if', 'import', 'in', 'include', 'inductive', 'instance', 'lemma', 'let',
      'local', 'macro', 'match', 'namespace', 'noncomputable', 'notation', 'obtain', 'omit', 'open',
      'private', 'scoped', 'section', 'set_option', 'show', 'structure', 'suffices', 'then',
      'theorem', 'this', 'variable', 'where', 'with'}
TAC = {'abel', 'all_goals', 'apply', 'by_cases', 'by_contra', 'cases', 'change', 'choose',
       'classical', 'congr', 'constructor', 'convert', 'decide', 'dsimp', 'erw', 'exact',
       'exact_mod_cast', 'exacts', 'exfalso', 'ext', 'field_simp', 'filter_upwards', 'fin_cases',
       'first', 'funext', 'gcongr', 'generalize', 'haveI', 'induction', 'infer_instance',
       'interval_cases', 'intro', 'intros', 'left', 'letI', 'lift', 'linarith',
       'linear_combination', 'nlinarith', 'norm_cast', 'norm_num', 'omega', 'positivity',
       'push_cast', 'rcases', 'refine', 'repeat', 'replace', 'rfl', 'right', 'ring', 'ring_nf',
       'rintro', 'rw', 'rwa', 'simp', 'simp_all', 'simp_rw', 'simpa', 'split_ifs', 'subst', 'symm',
       'tauto', 'trans', 'trivial', 'try', 'unfold', 'zify'}
SORT = {'Prop', 'Type'}

IDENT = r"[^\W\d][\w'!?]*(?:\.[\w'!?]+)*"
TOKEN_RE = re.compile(
    r'(?P<com>--.*$)|(?P<str>"(?:\\.|[^"\\])*")|(?P<attr>@\[[^\]]*\])|(?P<id>' + IDENT +
    r')|(?P<num>\d+(?:\.\d+)?)|(?P<other>.)', re.S)
DECL_LINE_RE = re.compile(
    r'^(?P<attrs>(?:@\[[^\]]*\]\s*)*)'
    r'(?P<mods>(?:(?:private|noncomputable|protected|local|scoped)\s+)*)'
    r'(?P<kw>theorem|lemma|def|abbrev|structure|inductive|instance)\b\s*(?P<rest>.*)$')


def split_comments(lines):
    """Block-comment structure of a file.

    Returns (segs, starts). `segs[i]` is the list of (kind, text) pieces of line i, with kind in
    {None, 'com', 'doc'}. `starts[i]` is the kind that is open when line i begins. Line comments
    are left to the tokenizer.
    """
    segs_all, starts = [], []
    kind = None
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


def tokenize_code(text):
    """Tokens (class, text) of a piece of code outside block comments. Class None is plain text."""
    toks = []
    for m in TOKEN_RE.finditer(text):
        kind = m.lastgroup
        t = m.group(0)
        if kind == 'id':
            if t in KW:
                toks.append(('kw', t))
            elif t in TAC:
                toks.append(('tac', t))
            elif t in SORT:
                toks.append(('sort', t))
            else:
                toks.append(('ident', t))
        elif kind == 'other':
            toks.append((None, t))
        else:
            toks.append((kind, t))
    return toks


class Decl:
    """A top-level declaration. `declinfo.annotate` fills the fields after `decl_line`."""
    __slots__ = ('name', 'short', 'kind', 'private', 'file', 'decl_line', 'namespace',
                 'line_start', 'line_end', 'docstring', 'statement', 'section_variables')

    def __repr__(self):
        return '<Decl %s %s:%s>' % (self.name, self.file, self.decl_line)


def parse_file(root, rel):
    """Return (lines, segs, decls) for the Lean file `rel` under `root`."""
    with open(os.path.join(root, rel), encoding='utf-8') as f:
        lines = f.read().split('\n')
    if lines and lines[-1] == '':
        lines = lines[:-1]
    segs, in_block = split_comments(lines)
    stack = []  # ('namespace', name) or ('section', name)
    decls = []
    for idx, line in enumerate(lines):
        if in_block[idx] is not None:
            continue
        m = re.match(r'^namespace\s+(\S+)', line)
        if m:
            stack.append(('namespace', m.group(1)))
            continue
        m = re.match(r'^(?:noncomputable\s+)?section\b\s*(\S*)', line)
        if m:
            stack.append(('section', m.group(1)))
            continue
        if re.match(r'^end\b', line):
            if stack:
                stack.pop()
            continue
        m = DECL_LINE_RE.match(line)
        if not m:
            continue
        nm = re.match(IDENT, m.group('rest'))
        d = Decl()
        d.kind = m.group('kw')
        d.private = 'private' in m.group('mods').split()
        d.file = rel
        d.decl_line = idx + 1
        d.namespace = '.'.join(x[1] for x in stack if x[0] == 'namespace')
        # an anonymous declaration is named after its line
        d.short = nm.group(0) if nm else '%s@L%d' % (d.kind, idx + 1)
        if d.short.startswith('_root_.'):
            d.name = d.short[len('_root_.'):]
        else:
            d.name = (d.namespace + '.' if d.namespace else '') + d.short
        decls.append(d)
    return lines, segs, decls
