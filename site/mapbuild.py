"""`data/paper_lean_map.json`, and the parts of formalization.html that follow from it."""
import re

from leanpage import REL_CLASS, DeclName, disp, entry_anchor, esc, esca
from panels import REL_TEXT, code_html

REL_ORDER = ['exact', 'definition', 'specialization', 'covered', 'check', 'none']
CURATED = ('kind', 'relation', 'confidence', 'summary', 'label', 'title', 'anchor')
NUMBERED = ('theorem', 'lemma', 'proposition', 'corollary', 'example', 'remark')


def lean_item(index, links, name, role):
    cands = [d for d in index.decls if d.name == name]
    if not cands:
        raise SystemExit('data/curation.json names a declaration that is not in the sources: ' + name)
    d = cands[0]
    return {
        'name': name, 'role': role, 'kind': 'theorem' if d.kind == 'lemma' else d.kind,
        'private': d.private, 'file': d.file, 'line_start': d.line_start, 'line_end': d.line_end,
        'decl_line': d.decl_line, 'docstring': d.docstring, 'statement': d.statement,
        'section_variables': d.section_variables, 'prove2me': links.records(d),
    }


def build_map(index, links, curation, old_map):
    """The new map. Entries and their order come from the curation, declaration fields from the
    sources, Prove2Me records from `links`. Everything else is carried over from `old_map`: the
    fields that the original generator computed from the paper source (label, title, anchor and
    paper line of the numbered statements, the list of displays) and the key order."""
    old = {e['id']: e for e in old_map['entries']}
    entries = []
    for c in curation['entries']:
        o = old.get(c['id'])
        if o is None:
            raise SystemExit('entry %s of data/curation.json is not in data/paper_lean_map.json. '
                             'New entries are not supported (see site/README.md).' % c['id'])
        e = {}
        for k in o:
            if k == 'lean':
                e['lean'] = [lean_item(index, links, nm, role) for nm, role in c['lean']]
            elif k in CURATED and k in c:
                e[k] = c[k]
            else:
                e[k] = o[k]
        entries.append(e)
    names = sorted({d['name'] for e in entries for d in e['lean']})
    new = dict(old_map)
    new['about'] = curation['_about']
    new['stats'] = stats(entries)
    new['entries'] = entries
    new['reverse_index'] = {
        nm: [{'id': e['id'], 'label': e['label']} for e in entries if any(d['name'] == nm for d in e['lean'])]
        for nm in names}
    return new


def stats(entries):
    def by_relation(es):
        return {r: sum(1 for e in es if e['relation'] == r) for r in REL_ORDER}

    br = by_relation(entries)
    numbered = [e for e in entries if e['kind'] in NUMBERED]
    return {
        'total': len(entries), 'with_lean_counterpart': len(entries) - br['none'],
        'exact': br['exact'] + br['definition'],
        'partial': br['specialization'] + br['covered'] + br['check'],
        'not_formalized': br['none'], 'by_relation': br,
        'labelled_statements': {'total': len(numbered), 'by_relation': by_relation(numbered)},
    }


def map_rows(mapdata, sort_keys):
    """Rows of the map table. `sort_keys[id]` is the paper position of an entry, which only the
    existing table records."""
    out = []
    for e in mapdata['entries']:
        rc = REL_CLASS[e['relation']]
        a = e['anchor']
        m = re.search(r'(\d+)\.', a.get('eq') or a.get('statement') or e['id'])
        sec = m.group(1) if m else None
        decls = []
        for d in e['lean']:
            rng = '#L%d-L%d' % (d['line_start'], d['line_end']) if d['line_end'] != d['line_start'] else '#L%d' % d['line_start']
            decls.append('<a href="lean/%s%s"><code>%s</code></a>' % (esca(d['file'][:-5] + '.html'), rng, esc(disp(d['name']))))
        seen = []
        for d in e['lean']:
            for p in d['prove2me']:
                if p['node'] not in [x['node'] for x in seen]:
                    seen.append(p)
        p2m = ', '.join('<a class="ext" href="%s" rel="noopener">%s</a>' % (esca(p['url']), esc(p['node'])) for p in seen)
        title = ' <span class="lp-title">%s</span>' % esca(e['title']) if e.get('title') else ''
        out.append('<tr class="tr-%s"><td data-sort="%s"><a href="index.html#%s">%s</a>%s</td><td>%s</td><td data-sort="%s">%s</td><td data-sort="%d"><span class="rel %s">%s</span></td><td>%s</td><td class="decls">%s</td><td>%s</td></tr>' % (
            rc[4:], sort_keys[e['id']], entry_anchor(e), esc(e['label']), title, e['kind'],
            sec if sec else '99', sec if sec else '—', REL_ORDER.index(e['relation']), rc, REL_TEXT[e['relation']],
            e['confidence'], ' '.join(decls), p2m))
    return ''.join(out)


def statement_block(index, name):
    """A `<div class="main-thm">` block of formalization.html for the public theorem `name`."""
    d = index.public[name]
    return '<div class="main-thm"><p><a href="lean/%s#L%d-L%d"><code>%s</code></a> — %s:%d–%d</p><pre class="lean">%s</pre></div>' % (
        d.file[:-5] + '.html', d.line_start, d.line_end, esc(disp(name)), esc(d.file), d.line_start, d.line_end,
        code_html(index, d.statement, d.file, 'lean/', DeclName(d.kind, d.short)))
