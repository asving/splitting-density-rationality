#!/usr/bin/env python3
"""Rebuild the derived parts of the companion site from this repository.

usage: python3 -I site/refresh.py REPO SITE_DIR [--rev REV] [--identity]

REPO      a clone of this repository. The Lean sources are read from REV (default HEAD) with
          `git archive`, so uncommitted changes in the working tree are ignored.
SITE_DIR  the site folder: `claude/splitting-type-density` in a clone of the site repository.

It rewrites, in SITE_DIR: the raw files and pages under `lean/`, the main block of
`lean/index.html`, the table body of `lean/decls.html`, the Lean panels of `index.html`, the
statement blocks, the map table and the axiom log of `formalization.html`,
`data/paper_lean_map.json`, the footer line of every page, the `refresh` record of
`data/validation.json` and `lean_commit` in `data/config.json`. Everything else is hand-written
and is left alone. A file is written only if its content changes, and a second run changes
nothing. The pages are written together at the end, so a run that stops with an error before that
leaves the folder as it was. README.md in this directory says what each part is derived from.

--identity  Behave like the original generator: cut statements the way it did, and write neither
            the footer line nor the bookkeeping (commit, link check, axiom log). `test_identity.sh`
            uses it to compare this reconstruction with the original's last output.

Standard library only. Exit status 1 if the link check finds a broken link.
"""
import argparse
import datetime
import html
import io
import json
import os
import re
import subprocess
import sys
import tarfile
import tempfile

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import leanindex
import leanpage
import linkcheck
import mapbuild
import p2m
import panels

HERE = os.path.dirname(os.path.abspath(__file__))
MAIN_THEOREMS = ['SurfaceBlowup.main_dvr', 'SurfaceBlowup.main_field_form',
                 'SurfaceBlowup.main_field_form_ramified', 'SurfaceBlowup.recip_main']
# listed on lean/index.html when the sources contain them (from v1.2.0 on)
COROLLARIES_V1_2 = ['SurfaceBlowup.universal_type_laws', 'SurfaceBlowup.reciprocity_ringHom']

FINEPRINT_RE = re.compile(r'<p class="fineprint">.*?</p>', re.S)
FINEPRINT = (
    '<p class="fineprint">This site was first generated on 2026-10-17 by a generator that no longer exists. '
    'Since 2026-11-11 the scripts in the <code>site/</code> directory of the Lean repository rebuild the Lean pages, '
    'the Lean panels and the tables. They reproduce the 2026-10-17 pages byte for byte from the v1.1.0 sources. '
    'The paper text is kept in the paper page itself. The Lean sources shown are commit <code>%s</code> of the '
    'public repository, on Lean <code>%s</code>. Mathematics typeset with KaTeX (vendored).</p>')
VALIDATION_NOTE = (
    'Written by site/refresh.py of the Lean repository. The records above this one are older and were not re-run: '
    'the checks of the original generator on 2026-10-17 (KaTeX, links, a browser self-test) and the record of the '
    'update of 2026-11-11. This record is the check of the internal links of the pages as they are now.')
FOOTER_RE = re.compile(r'<footer class="site-footer">.*?</footer>', re.S)
ASIDE_OPEN = '<aside class="lean-panel" aria-label="Lean formalization">'
ASIDE_RE = re.compile(re.escape(ASIDE_OPEN) + r'(.*?)</aside>', re.S)
ENTRY_RE = re.compile(r'<div class="lp-entry [^"]*" data-entry="([^"]*)">')
BLOCK_RE = re.compile(r'<div class="main-thm"><p><a href="lean/[^"]*"><code>([^<]*)</code></a> — .*?</pre></div>', re.S)
AXIOM_LINE_RE = re.compile(r"'.*' (depends on axioms: \[.*\]|does not depend on any axioms)$")


def git(repo, *args):
    r = subprocess.run(['git', '-C', repo] + list(args), stdout=subprocess.PIPE, stderr=subprocess.PIPE)
    if r.returncode != 0:
        sys.exit('git %s failed: %s' % (' '.join(args), r.stderr.decode('utf-8', 'replace').strip()))
    return r.stdout


def export(repo, rev, paths, dest):
    """Write the files of `paths` at revision `rev` into `dest`."""
    with tarfile.open(fileobj=io.BytesIO(git(repo, 'archive', '--format=tar', rev, '--', *paths))) as tar:
        for m in tar:
            if not m.isfile():
                continue
            assert not os.path.isabs(m.name) and '..' not in m.name.split('/'), m.name
            target = os.path.join(dest, m.name)
            os.makedirs(os.path.dirname(target), exist_ok=True)
            with open(target, 'wb') as f:
                f.write(tar.extractfile(m).read())


def read(path):
    with open(path, encoding='utf-8') as f:
        return f.read()


def read_json(path):
    with open(path, encoding='utf-8') as f:
        return json.load(f)


class Site:
    """The site folder. Changes are staged in memory and written by `flush`, so a run that stops
    half way writes nothing. `flush` writes a file only when its content changes, and remembers
    which did."""

    def __init__(self, root):
        self.root = root
        self.staged = {}  # relative path -> bytes, or None for a file to remove
        self.changed = []

    def path(self, rel):
        return os.path.join(self.root, rel)

    def read(self, rel):
        if self.staged.get(rel) is not None:
            return self.staged[rel].decode('utf-8')
        return read(self.path(rel))

    def write(self, rel, data):
        self.staged[rel] = data.encode('utf-8') if isinstance(data, str) else data

    def remove(self, rel):
        self.staged[rel] = None

    def flush(self):
        for rel, data in self.staged.items():
            p = self.path(rel)
            if data is None:
                os.remove(p)
                d = os.path.dirname(p)
                while d != self.root and not os.listdir(d):  # drop directories left empty
                    os.rmdir(d)
                    d = os.path.dirname(d)
            else:
                if os.path.exists(p):
                    with open(p, 'rb') as f:
                        if f.read() == data:
                            continue
                os.makedirs(os.path.dirname(p), exist_ok=True)
                with open(p, 'wb') as f:
                    f.write(data)
            self.changed.append(rel)
        self.staged = {}


def between(s, start, end, what):
    """(i, j) with s[i:j] the text after the first `start` and before the next `end`."""
    i = s.find(start)
    j = s.find(end, i + len(start)) if i != -1 else -1
    if j == -1:
        sys.exit('cannot find %s' % what)
    return i + len(start), j


def refresh(repo, src, site_dir, commit, identity):
    site = Site(site_dir)
    cfg = read_json(site.path('data/config.json'))
    curation = read_json(site.path('data/curation.json'))
    old_map_text = site.read('data/paper_lean_map.json')
    old_map = json.loads(old_map_text)
    notes = []

    files = sorted(os.path.relpath(os.path.join(dp, f), src)
                   for top in cfg['lean_dirs'] for dp, _, fn in os.walk(os.path.join(src, top))
                   for f in fn if f.endswith('.lean'))
    toolchain = read(os.path.join(src, 'lean-toolchain')).strip().split(':')[1]
    mathlib_rev = re.search(r'"([0-9a-f]{40})"', read(os.path.join(src, 'lakefile.lean'))).group(1)[:7]
    index = leanpage.Index(src, files, original=identity)
    links = p2m.Links(read_json(site.path('data/prove2me_nodes.json')), site.read('lean/decls.html'),
                      cfg['prove2me']['url_template'])

    # ---- the map
    new_map = mapbuild.build_map(index, links, curation, old_map)
    if not identity:
        sources = dict(new_map['sources'])
        sources['lean_root'] = '%s (commit %s)' % (cfg['lean_artifact_url'], commit)
        sources['lean_files'] = len(files)
        for key, cfg_key in (('paper', 'paper'), ('prove2me_catalog', 'prove2me_nodes')):
            if cfg_key in cfg:
                sources[key] = cfg[cfg_key]
        new_map['sources'] = sources
        new_map['prove2me'] = cfg['prove2me']
    entries = {e['id']: e for e in new_map['entries']}

    def dump_map():
        return json.dumps(new_map, indent=1, ensure_ascii=False)

    if dump_map() != old_map_text:
        new_map['generated'] = datetime.datetime.utcnow().strftime('%Y-%m-%dT%H:%M:%SZ')
    site.write('data/paper_lean_map.json', dump_map())

    # ---- footer line
    fineprint = FINEPRINT % (commit, toolchain)

    def refoot(page, rel):
        if identity:
            return page
        if len(FINEPRINT_RE.findall(page)) != 1:
            sys.exit('%s: expected exactly one <p class="fineprint">' % rel)
        return FINEPRINT_RE.sub(lambda m: fineprint, page)

    # ---- lean/: sources index, declaration index, raw files and pages
    s = site.read('lean/index.html')
    i = s.index('<main')
    j = s.index('</main>') + len('</main>')
    corollaries = [n for n in COROLLARIES_V1_2 if n in index.public]
    lean_index = refoot(s[:i] + leanindex.index_main(index, new_map, cfg['lean_root_files'], MAIN_THEOREMS,
                                                     corollaries, toolchain, mathlib_rev) + s[j:], 'lean/index.html')
    site.write('lean/index.html', lean_index)

    s = site.read('lean/decls.html')
    i, j = between(s, '<tbody>', '</tbody>', 'the table body of lean/decls.html')
    site.write('lean/decls.html', refoot(s[:i] + leanindex.decls_tbody(index, new_map, links) + s[j:], 'lean/decls.html'))

    template = read(os.path.join(HERE, 'lean_page_template.html'))
    footer = FOOTER_RE.search(lean_index).group(0)
    expected = set()
    for rel in files:
        with open(os.path.join(src, rel), 'rb') as f:
            site.write('lean/' + rel, f.read())
        site.write('lean/' + rel[:-5] + '.html', leanpage.page_html(index, rel, new_map, template, footer))
        expected.update(('lean/' + rel, 'lean/' + rel[:-5] + '.html'))
    for top in cfg['lean_dirs']:  # pages and raw files of sources that no longer exist
        for dp, _, fn in os.walk(site.path('lean/' + top)):
            for f in fn:
                rel = os.path.relpath(os.path.join(dp, f), site_dir)
                if rel not in expected:
                    site.remove(rel)
    for f in cfg['lean_root_files']:
        with open(os.path.join(src, f), 'rb') as fh:
            site.write('lean/' + f, fh.read())

    # ---- the paper page: each panel is rebuilt from the entries it lists
    def panel(m):
        ids = ENTRY_RE.findall(m.group(1))
        return ASIDE_OPEN + ''.join(panels.entry_block(index, entries[html.unescape(i)]) for i in ids) + '</aside>'

    s, n_panels = ASIDE_RE.subn(panel, site.read('index.html'))
    site.write('index.html', refoot(s, 'index.html'))

    # ---- the formalization page
    s = site.read('formalization.html')

    def block(m):
        name = 'SurfaceBlowup.' + html.unescape(m.group(1))
        if name not in index.public:
            sys.exit('formalization.html shows the statement of %s, which is not in the sources' % name)
        return mapbuild.statement_block(index, name)

    s = BLOCK_RE.sub(block, s)
    # map table: the first cell of a row carries the paper position, which nothing else records
    k = s.index('<h2 id="map">')
    i, j = (k + x for x in between(s[k:], '<tbody>', '</tbody>', 'the map table of formalization.html'))
    rows = s[i:j].split('</tr>')[:-1]
    if len(rows) != len(old_map['entries']):
        sys.exit('the map table of formalization.html and data/paper_lean_map.json have different lengths')
    sort_keys = {}
    for row, e in zip(rows, old_map['entries']):
        m = re.match(r'<tr class="[^"]*"><td data-sort="(\d+)"><a href="index.html#([^"]*)">', row)
        if not m or m.group(2) != leanpage.entry_anchor(e):
            sys.exit('the map table of formalization.html does not match data/paper_lean_map.json at entry ' + e['id'])
        sort_keys[e['id']] = m.group(1)
    s = s[:i] + mapbuild.map_rows(new_map, sort_keys) + s[j:]
    # the coverage table is hand-written: say so when the curation has moved away from it
    st = new_map['stats']
    lab = st['labelled_statements']['by_relation']
    m = re.search(r'<table class="data stats">.*?<tbody>(.*?)</tbody>', s, re.S)
    want = [st['total'], st['exact'], st['partial'], st['not_formalized'], st['labelled_statements']['total'],
            lab['exact'] + lab['definition'], lab['specialization'] + lab['covered'] + lab['check'], lab['none']]
    if not m or [int(x) for x in re.findall(r'<td class="num">(\d+)</td>', m.group(1))] != want:
        notes.append('the coverage table in section 5 of formalization.html does not show the current counts %s; '
                     'edit it by hand' % want)
    # axiom log: the output of the release check, if it was run in REPO
    log = os.path.join(repo, 'logs', 'release_axioms.log')
    if not identity and os.path.exists(log):
        lines = [l for l in read(log).split('\n') if l.strip()]
        if lines and all(AXIOM_LINE_RE.match(l) for l in lines):
            a = s.index('<h2 id="certificates">')
            b = s.index('<h2 ', a + 1)
            i, j = between(s[a:b], '<pre class="log">', '</pre>', 'the axiom log of formalization.html')
            s = s[:a + i] + leanpage.esca('\n'.join(lines)) + s[a + j:]
        else:
            notes.append('logs/release_axioms.log is not a clean axiom listing; the axiom log of formalization.html was left as it is')
    site.write('formalization.html', refoot(s, 'formalization.html'))

    print('%d Lean files at commit %s (Lean %s, Mathlib %s), %d panels' % (
        len(files), commit, toolchain, mathlib_rev, n_panels))
    if identity:
        site.flush()
        return site, notes, None

    # ---- footer line of every other page
    for dp, _, fn in os.walk(site_dir):
        for f in fn:
            rel = os.path.relpath(os.path.join(dp, f), site_dir)
            if f.endswith('.html') and rel not in site.staged:
                site.write(rel, refoot(site.read(rel), rel))

    # ---- bookkeeping
    if 'lean_commit' in cfg:
        text, n = re.subn(r'("lean_commit": ")[^"]*(")', lambda m: m.group(1) + commit + m.group(2),
                          site.read('data/config.json'))
        assert n == 1, 'data/config.json: lean_commit'
        site.write('data/config.json', text)
    site.flush()
    check = linkcheck.check(site_dir)
    val = read_json(site.path('data/validation.json'))
    val['refresh'] = {
        'note': VALIDATION_NOTE, 'lean_commit': commit, 'lean_toolchain': toolchain,
        'links': {'pages': check['pages'], 'internal_links_checked': check['internal_links_checked'],
                  'broken': len(check['broken']), 'external_links': check['external_links']},
    }
    site.write('data/validation.json', json.dumps(val, indent=1, ensure_ascii=False))
    site.flush()
    return site, notes, check


def main():
    ap = argparse.ArgumentParser(description='Rebuild the derived parts of the companion site.')
    ap.add_argument('repo', metavar='REPO', help='clone of the Lean repository')
    ap.add_argument('site', metavar='SITE_DIR', help='the site folder')
    ap.add_argument('--rev', default='HEAD', help='revision of REPO to read the sources from (default HEAD)')
    ap.add_argument('--identity', action='store_true', help='behave like the original generator (for test_identity.sh)')
    args = ap.parse_args()
    for f in ('data/config.json', 'data/curation.json', 'index.html', 'formalization.html', 'lean/decls.html'):
        if not os.path.exists(os.path.join(args.site, f)):
            sys.exit('%s is not the site folder: %s is missing' % (args.site, f))
    commit = git(args.repo, 'rev-parse', '--short', args.rev + '^{commit}').decode().strip()
    cfg = read_json(os.path.join(args.site, 'data', 'config.json'))
    with tempfile.TemporaryDirectory() as src:
        export(args.repo, args.rev, cfg['lean_dirs'] + cfg['lean_root_files'], src)
        site, notes, check = refresh(args.repo, src, args.site, commit, args.identity)
    for n in notes:
        print('NOTE: ' + n)
    if check is not None:
        print('links: ' + linkcheck.summary(check))
        for b in check['broken']:
            print('  broken:', b)
    print('files changed: %d' % len(site.changed))
    for rel in site.changed[:40]:
        print('  ' + rel)
    if len(site.changed) > 40:
        print('  ... and %d more' % (len(site.changed) - 40))
    sys.exit(1 if check is not None and check['broken'] else 0)


if __name__ == '__main__':
    main()
