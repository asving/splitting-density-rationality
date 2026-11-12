"""Highlighted Lean pages with line anchors, identifier links and paper chips."""
import html
import os
import re

import declinfo
import leansrc

REL_CLASS = {'exact': 'rel-ok', 'definition': 'rel-ok', 'specialization': 'rel-part',
             'covered': 'rel-part', 'check': 'rel-part', 'none': 'rel-no'}


def esc(t):
    return html.escape(t, quote=False)


def esca(t):
    return html.escape(t, quote=True)


def relname(name):
    """Name relative to the root namespaces of the codebase (nested namespaces are kept)."""
    for pre in ('SurfaceBlowup.Tests.', 'SurfaceBlowup.'):
        if name.startswith(pre):
            return name[len(pre):]
    return name


def disp(name):
    """Name as the site shows it: without the leading `SurfaceBlowup.`."""
    return name[len('SurfaceBlowup.'):] if name.startswith('SurfaceBlowup.') else name


def entry_anchor(e):
    """Anchor of a map entry on the paper page."""
    a = e['anchor']
    if 'statement' in a:
        return a['statement']
    if 'eq' in a:
        return 'eq-' + a['eq']
    return e['id']


class Index:
    """All declarations of the codebase, for identifier links.

    A public declaration is linked from everywhere, by its full name or its relative name. A
    private one is linked only from its own file. A public name wins over a private one.
    """

    def __init__(self, root, files, original=False):
        self.files = {}    # rel -> (lines, segs, decls)
        self.public = {}
        self.private = {}  # rel -> {name: Decl}
        self.decls = []
        for rel in files:
            lines, segs, decls = leansrc.parse_file(root, rel)
            _, starts = leansrc.split_comments(lines)
            declinfo.annotate(lines, starts, decls, original)
            self.files[rel] = (lines, segs, decls)
            for d in decls:
                self.decls.append(d)
                if '@' in d.short:
                    continue
                table = self.private.setdefault(rel, {}) if d.private else self.public
                for key in (d.name, relname(d.name)):
                    table.setdefault(key, d)

    def resolve(self, tok, rel):
        return self.public.get(tok) or self.private.get(rel, {}).get(tok)


class DeclName:
    """The name of the declaration being rendered. Its first occurrence after the declaration
    keyword gets class `dn` instead of a link. Anonymous declarations have no name to mark."""

    def __init__(self, kw, short):
        self.kw, self.short = kw, short
        self.seen_kw = False
        self.pending = '@' not in short


def highlight(index, rel, segs, link, dn=None):
    """Inner HTML of one source line, given as its comment segments.

    `link(target)` gives the href of an identifier that resolves to the declaration `target`.
    """
    parts = []
    for kind, text in segs:
        if kind is not None:
            parts.append('<span class="%s">%s</span>' % (kind, esc(text)))
            continue
        plain = []

        def flush():
            if plain:
                parts.append(esc(''.join(plain)))
                del plain[:]

        for cls, t in leansrc.tokenize_code(text):
            if cls is None:
                plain.append(t)
            elif cls == 'ident':
                if dn is not None and dn.pending and dn.seen_kw and t == dn.short:
                    flush()
                    parts.append('<span class="dn">%s</span>' % esc(t))
                    dn.pending = False
                    continue
                tgt = index.resolve(t, rel)
                if tgt is not None:
                    flush()
                    parts.append('<a class="id" href="%s">%s</a>' % (esca(link(tgt)), esc(t)))
                else:
                    plain.append(t)
            else:
                flush()
                if cls == 'kw' and dn is not None and t == dn.kw:
                    dn.seen_kw = True
                parts.append('<span class="%s">%s</span>' % (cls, esc(t)))
        flush()
    return ''.join(parts)


def render_lines(index, rel):
    """Inner HTML of every line of the file `rel` (the content of its `<span class="lc">`)."""
    lines, segs, decls = index.files[rel]
    decl_at = {d.decl_line: d for d in decls}
    here = os.path.dirname(rel) or '.'

    def link(tgt):
        return '%s#L%d' % (os.path.relpath(tgt.file[:-5] + '.html', here), tgt.decl_line)

    out = []
    for n, (line, sg) in enumerate(zip(lines, segs), 1):
        if line == '':
            out.append(' ')
            continue
        d = decl_at.get(n)
        out.append(highlight(index, rel, sg, link, DeclName(d.kind, d.short) if d else None))
    return out


def module_title(lines):
    """First `# ` heading of the module docstring."""
    inside = False
    for l in lines:
        if l.startswith('/-!'):
            inside = True
            continue
        if inside:
            if l.startswith('# '):
                return l[2:].strip()
            if '-/' in l:
                inside = False
    return None


def page_pre(index, rel, mapdata):
    """The `<pre class="lean lean-src">` block of a Lean page."""
    lines, segs, decls = index.files[rel]
    decl_at = {d.decl_line: d for d in decls}
    ent = {e['id']: e for e in mapdata['entries']}
    up = '../' * (rel.count('/') + 1)
    out = ['<pre class="lean lean-src">']
    for n, h in enumerate(render_lines(index, rel), 1):
        d = decl_at.get(n)
        attr = ' data-decl="%s"' % esca(d.name) if d is not None else ''
        chips = ''
        if d is not None:
            for x in mapdata['reverse_index'].get(d.name, []):
                e = ent[x['id']]
                chips += '<a class="paper-chip %s" href="%sindex.html#%s" title="%s">%s</a>' % (
                    REL_CLASS[e['relation']], up, entry_anchor(e), esca(e['summary'][:200]), esc(x['label']))
        out.append('<span class="ln" id="L%d"%s><a class="lnum" href="#L%d">%d</a><span class="lc">%s</span>%s</span>'
                   % (n, attr, n, n, h, chips))
    out.append('</pre>')
    return ''.join(out)


def page_html(index, rel, mapdata, template, footer):
    """A whole Lean page. `template` is the text of lean_page_template.html and `footer` the
    `<footer>` element shared by all pages of the site."""
    lines, segs, decls = index.files[rel]
    depth = rel.count('/') + 1
    parts = rel.split('/')
    npub = sum(1 for d in decls if not d.private)
    values = {
        'REL': esc(rel),
        'UP': '../' * depth,
        'LEANUP': '../' * (depth - 1),
        'CRUMBS': esc(' / '.join(parts)),
        'TITLE': esc(module_title(lines) or parts[-1]),
        'META': '%d lines · %d public declarations' % (len(lines), npub),  # never the singular
        'RAW': esca(parts[-1]),
        'PRE': page_pre(index, rel, mapdata),
        'FOOTER': footer,
    }
    return re.sub(r'\{([A-Z]+)\}', lambda m: values[m.group(1)], template)
