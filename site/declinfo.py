"""Extent, docstring, statement and section variables of each declaration.

These are the per-declaration fields of `data/paper_lean_map.json`.
"""
import re

CMD_START = re.compile(
    r'^(?:@\[|/--|/-!|/-|--|theorem\b|lemma\b|def\b|abbrev\b|structure\b|inductive\b|instance\b|'
    r'private\b|noncomputable\b|protected\b|namespace\b|section\b|end\b|variable\b|open\b|omit\b|'
    r'include\b|local\b|scoped\b|attribute\b|set_option\b|macro\b|notation\b|#|import\b|universe\b)')


def cut_statement(text, original=False):
    """Signature of a theorem: the text before the `:=` that starts the proof.

    That is the first ` :=` at bracket depth 0 that is not the `:=` of a `letI`, `haveI`, `let` or
    `have` line of the statement. The original generator did not make this exception and cut
    `main_field_form_ramified` short. `original=True` reproduces that.
    """
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
            if not original and re.match(r'\s*(letI|haveI|let|have)\b', text[line_start:i]):
                i += 2
                continue
            return text[:i].rstrip()
        i += 1
    return text.rstrip()


def annotate(lines, starts, decls, original=False):
    """Fill line_start, line_end, docstring, statement, section_variables on each Decl."""
    n = len(lines)
    # section variables: scopes follow namespace / section / end
    scopes = [[]]
    var_at = {}
    decl_lines = {d.decl_line for d in decls}
    i = 0
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
        # docstring: the doc comment that ends on the line above (attribute lines may intervene)
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
                body = '\n'.join(lines[t:s + 1])[3:]
                d.docstring = body[:body.rindex('-/')].strip()
                d.line_start = t + 1
        # extent: up to the line before the next command in column 0, trailing blank lines dropped
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
        d.statement = cut_statement(full, original) if d.kind in ('theorem', 'lemma') else full
        d.section_variables = var_at.get(d.decl_line, '')
