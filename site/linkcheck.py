#!/usr/bin/env python3
"""Check the internal links of a site folder.

For every `href` and `src` of every HTML page: the target file exists, and a fragment names an
`id` of the target page. A line range `#L10-L20` is checked by its first line. External links are
counted, not fetched.

usage: python3 -I site/linkcheck.py SITE_DIR      (exit status 1 if a link is broken)
"""
import html
import os
import re
import sys


def check(site):
    """Return {'pages', 'internal_links_checked', 'broken': [(page, href, reason)], 'external_links'}."""
    pages = sorted(os.path.join(dp, f) for dp, _, fn in os.walk(site) for f in fn if f.endswith('.html'))
    ids = {}

    def page_ids(p):
        if p not in ids:
            with open(p, encoding='utf-8') as f:
                ids[p] = set(re.findall(r'\sid="([^"]*)"', f.read()))
        return ids[p]

    checked = 0
    broken = []
    external = set()
    for p in pages:
        with open(p, encoding='utf-8') as f:
            text = f.read()
        for h in re.findall(r'(?:href|src)="([^"]*)"', text):
            h = html.unescape(h)
            if h.startswith(('http://', 'https://', 'mailto:')):
                external.add(h)
                continue
            checked += 1
            path, _, frag = h.partition('#')
            target = os.path.normpath(os.path.join(os.path.dirname(p), path)) if path else p
            if not os.path.exists(target):
                broken.append((os.path.relpath(p, site), h, 'missing file'))
            elif frag and target.endswith('.html'):
                first = frag.split('-L')[0] if re.match(r'L\d+-L\d+$', frag) else frag
                if first not in page_ids(target):
                    broken.append((os.path.relpath(p, site), h, 'missing anchor'))
    return {'pages': len(pages), 'internal_links_checked': checked, 'broken': broken,
            'external_links': len(external)}


def summary(r):
    return 'pages: %d, internal links checked: %d, broken: %d, external links: %d' % (
        r['pages'], r['internal_links_checked'], len(r['broken']), r['external_links'])


if __name__ == '__main__':
    if len(sys.argv) != 2:
        sys.exit(__doc__)
    result = check(sys.argv[1])
    print(summary(result))
    for b in result['broken']:
        print('  ', b)
    sys.exit(1 if result['broken'] else 0)
