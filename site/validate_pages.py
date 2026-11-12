#!/usr/bin/env python3
"""Compare every published Lean page with the raw file next to it, line by line.

It needs only the site folder. For each line it checks the declaration that the page records
(`data-decl`) and the highlighted HTML (classes and identifier links). A Lean page is one long line
of HTML, so `git diff` does not say where two versions differ. This does.

usage: python3 -I site/validate_pages.py SITE_DIR [MAX_SHOWN]     (exit status 1 on a mismatch)
"""
import json
import os
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import leanpage
import pagelib


def main(site, max_shown=12):
    with open(os.path.join(site, 'data', 'config.json'), encoding='utf-8') as f:
        dirs = json.load(f)['lean_dirs']
    files = pagelib.lean_files(site, dirs)
    index = leanpage.Index(os.path.join(site, 'lean'), files)
    total = bad = 0
    for rel in files:
        published = pagelib.read_page(os.path.join(site, 'lean', rel[:-5] + '.html'))
        mine = leanpage.render_lines(index, rel)
        decl_at = {d.decl_line: d.name for d in index.files[rel][2]}
        if len(published) != len(mine):
            bad += 1
            print('%s: the page has %d lines, the raw file %d' % (rel, len(published), len(mine)))
        for line, h in zip(published, mine):
            total += 1
            if line['html'] != h or line['decl'] != decl_at.get(line['n']):
                bad += 1
                if bad <= max_shown:
                    print('--- %s line %d' % (rel, line['n']))
                    print('  page: %s %s' % (line['decl'], line['html'][:400]))
                    print('  mine: %s %s' % (decl_at.get(line['n']), h[:400]))
    print('Lean pages: %d, lines: %d, mismatches: %d' % (len(files), total, bad))
    return 1 if bad else 0


if __name__ == '__main__':
    if len(sys.argv) not in (2, 3):
        sys.exit(__doc__)
    sys.exit(main(sys.argv[1], int(sys.argv[2]) if len(sys.argv) > 2 else 12))
