"""Lean panels of the paper page, and the snippet renderers they share with the formalization page."""
import re

import leansrc
from leanpage import REL_CLASS, DeclName, disp, entry_anchor, esc, esca, highlight

REL_TEXT = {'exact': 'exact', 'definition': 'definition', 'specialization': 'specialization',
            'covered': 'covered by lemmas', 'check': 'instances checked', 'none': 'not formalized'}
LPE = {'rel-ok': 'lpe-ok', 'rel-part': 'lpe-part', 'rel-no': 'lpe-no'}


def doc_html(doc):
    """A docstring as HTML: `code`, **bold**, a blank line is a paragraph break. A single newline
    becomes a space, and the indentation of continuation lines is kept."""
    out = []
    for p in re.split(r'\n\s*\n', doc):
        buf = []
        for part in re.split(r'(`[^`]*`)', p.replace('\n', ' ')):
            if part.startswith('`') and part.endswith('`') and len(part) >= 2:
                buf.append('<code>%s</code>' % esc(part[1:-1]))
            else:
                buf.append(esc(part))
        out.append(re.sub(r'\*\*(.+?)\*\*', lambda m: '<strong>%s</strong>' % m.group(1), ''.join(buf)))
    return '<br><br>'.join(out)


def code_html(index, text, rel, prefix, dn=None):
    """Highlighted code from the file `rel`. Identifier links start with `prefix`, the path from
    the page to the `lean/` folder."""
    lines = text.split('\n')
    segs, _ = leansrc.split_comments(lines)

    def link(tgt):
        return '%s%s#L%d' % (prefix, tgt.file[:-5] + '.html', tgt.decl_line)

    return '\n'.join(highlight(index, rel, sg, link, dn) for sg in segs)


def decl_name(index, d):
    """DeclName for a declaration given as an item of the map."""
    src = index.public.get(d['name']) or next(
        (x for x in index.decls if x.name == d['name'] and x.file == d['file']), None)
    if src is None:
        return DeclName(d['kind'], d['name'].split('.')[-1])
    return DeclName(src.kind, src.short)


def decl_block(index, d, prefix='lean/', open_=True):
    page = prefix + d['file'][:-5] + '.html'
    if d['line_end'] != d['line_start']:
        rng = '#L%d-L%d' % (d['line_start'], d['line_end'])
        span = '%d–%d' % (d['line_start'], d['line_end'])
    else:
        rng = '#L%d' % d['line_start']
        span = '%d' % d['line_start']
    flags = ''
    if d['private']:
        flags += ' <span class="flag">private</span>'
    if d['file'].startswith('Tests/'):
        flags += ' <span class="flag">test</span>'
    links = ['<a href="%s%s">%s:%s</a>' % (esca(page), rng, esc(d['file']), span),
             '<a href="%s%s">raw</a>' % (prefix, esca(d['file']))]
    for p in d['prove2me']:
        links.append('<a class="ext" href="%s" rel="noopener" title="%s">Prove2Me %s</a>' % (
            esca(p['url']), esca(p['theorem_name']), esc(p['node'])))
    out = ['<div class="lp-decl"><div class="lp-decl-head"><a class="lp-name" href="%s%s"><code>%s</code></a>%s <span class="lp-kind">%s</span></div>' % (
        esca(page), rng, esc(disp(d['name'])), flags, d['kind'])]
    out.append('<div class="lp-role">%s</div>' % esca(d['role']))
    out.append('<div class="lp-links">%s</div>' % ' · '.join(links))
    if d['docstring']:
        out.append('<div class="lp-doc">%s</div>' % doc_html(d['docstring']))
    if d['section_variables']:
        out.append('<details class="lp-vars"><summary>section variables in scope</summary><pre class="lean">%s</pre></details>' % (
            code_html(index, d['section_variables'], d['file'], prefix)))
    out.append('<details class="lp-stmt"%s><summary>Lean statement</summary><pre class="lean">%s</pre></details></div>' % (
        ' open' if open_ else '', code_html(index, d['statement'], d['file'], prefix, decl_name(index, d))))
    return ''.join(out)


def entry_block(index, e, prefix='lean/'):
    """The panel of one map entry. The statements of its first two declarations start open."""
    rc = REL_CLASS[e['relation']]
    title = ' <span class="lp-title">(%s)</span>' % esca(e['title']) if e.get('title') else ''
    out = ['<div class="lp-entry %s" data-entry="%s"><div class="lp-head"><a class="lp-label" href="#%s">%s</a>%s <span class="rel %s">%s</span> <span class="conf">confidence: %s</span></div>' % (
        LPE[rc], esca(e['id']), entry_anchor(e), esc(e['label']), title, rc, REL_TEXT[e['relation']], e['confidence'])]
    out.append('<p class="lp-summary">%s</p>' % esc(e['summary']))
    for i, d in enumerate(e['lean']):
        out.append(decl_block(index, d, prefix, open_=i < 2))
    out.append('</div>')
    return ''.join(out)
