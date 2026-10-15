#!/usr/bin/env python3
"""Lines per top-level declaration of the SurfaceBlowup sources (and Tests/).

usage: tools/longest_decls.py [OUT.tsv]   (default logs/longest_decls.tsv)

A declaration starts at its keyword line (theorem/lemma/def/instance/abbrev/structure/class/
inductive/example/opaque/axiom, after attributes and modifiers on the same line) and runs to the
line before the next top-level command, docstring, comment block, attribute line or section
header. Docstrings and leading attribute lines are NOT counted; trailing blank lines are dropped.
Output: tab-separated `lines  file  start_line  name`, sorted by lines descending.
"""
import glob
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
KW = (r'(?:theorem|lemma|def|instance|abbrev|structure|class|inductive|example|opaque|axiom)')
MODS = r'(?:(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable |nonrec |partial |unsafe )*)'
DECL = re.compile(r'^' + MODS + r'(?:' + KW + r')\b\s*([^\s:({\[]*)')
# any line at column 0 that is not a continuation starts a new top-level item
BOUNDARY = re.compile(r'^(?:/--|/-!|/-|--|@\[|open |namespace |end\b|section\b|variable |'
                      r'universe |set_option |noncomputable section|omit |include |'
                      r'attribute |#|local |scoped |notation|macro|syntax|elab|private |'
                      r'protected |noncomputable |' + KW + r'\b)')


def decls(path):
    lines = open(path, encoding='utf-8').read().split('\n')
    out, cur = [], None
    for i, line in enumerate(lines, 1):
        m = DECL.match(line)
        if m or (cur and BOUNDARY.match(line)):
            if cur:
                out.append(cur)
                cur = None
        if m:
            cur = [i, i, m.group(1) or '(anonymous)']
        elif cur is not None and line.strip():
            cur[1] = i
    if cur:
        out.append(cur)
    return out


def main():
    out = sys.argv[1] if len(sys.argv) > 1 else os.path.join(ROOT, 'logs/longest_decls.tsv')
    rows = []
    files = sorted(glob.glob(os.path.join(ROOT, 'SurfaceBlowup/**/*.lean'), recursive=True))
    files += sorted(glob.glob(os.path.join(ROOT, 'Tests/**/*.lean'), recursive=True))
    for f in files:
        rel = os.path.relpath(f, os.path.join(ROOT, 'SurfaceBlowup'))
        if rel.startswith('..'):
            rel = os.path.relpath(f, ROOT)
        for start, end, name in decls(f):
            rows.append((end - start + 1, rel, start, name))
    rows.sort(key=lambda r: (-r[0], r[1], r[2]))
    with open(out, 'w') as fh:
        for r in rows:
            fh.write('\t'.join(map(str, r)) + '\n')
    for r in rows[:15]:
        print('\t'.join(map(str, r)))


if __name__ == '__main__':
    main()
