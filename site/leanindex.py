"""Main block of `lean/index.html` (the sources index) and table body of `lean/decls.html`."""
import os

from leanpage import disp, entry_anchor, esc, esca, module_title, relname


def decl_link(index, name):
    d = index.public[name]
    return '<a href="%s#L%d">%s</a>' % (d.file[:-5] + '.html', d.decl_line, relname(name))


def index_main(index, mapdata, root_files, main_theorems, corollaries, toolchain, mathlib_rev):
    """`<main>` of lean/index.html. `corollaries` may be empty."""
    rev = mapdata['reverse_index']
    files = list(index.files)
    nlines = sum(len(index.files[f][0]) for f in files)
    out = ['<main class="doc-page"><h1>Lean sources</h1><p>The unified Lean 4 / Mathlib codebase (namespace <code>SurfaceBlowup</code>), %d files, %d lines, syntax-highlighted with line anchors; every identifier defined in the codebase links to its definition. Lines carrying a coloured chip are cited by the <a href="../formalization.html">paper ↔ Lean map</a>. Raw files sit next to the pages (same path, <code>.lean</code>). Root files: %s.</p>' % (
        len(files), nlines, ' · '.join('<a href="%s">%s</a>' % (esca(f), esc(f)) for f in root_files))]
    cor = ''
    if corollaries:
        cor = 'Corollaries added in v1.2: %s. ' % ', '.join(decl_link(index, n) for n in corollaries)
    out.append('<p>Toolchain: Lean <code>%s</code>, Mathlib <code>%s</code> (pinned in <code>lakefile.lean</code>). Main theorems: %s; trust boundary: <a href="SurfaceBlowup/Basic.html">Basic.lean</a>. %s<a href="decls.html">Declaration index</a> (reverse map Lean → paper).</p>' % (
        esc(toolchain), esc(mathlib_rev), ', '.join(decl_link(index, n) for n in main_theorems), cor))
    groups = {}
    for f in files:
        groups.setdefault(os.path.dirname(f), []).append(f)
    for g in sorted(groups):
        out.append('<h2>%s/</h2><div class="table-wrap"><table class="sortable data"><thead><tr><th>file</th><th>title</th><th class="num">lines</th><th class="num">public decls</th><th class="num">cited by the paper map</th></tr></thead><tbody>' % esc(g))
        for f in sorted(groups[g]):
            lines, segs, decls = index.files[f]
            npub = sum(1 for d in decls if not d.private)
            ncited = sum(1 for d in decls if d.name in rev)
            out.append('<tr><td><a href="%s">%s</a></td><td>%s</td><td class="num">%d</td><td class="num">%d</td><td class="num">%d</td></tr>' % (
                esca(f[:-5] + '.html'), esc(os.path.basename(f)), esc(module_title(lines) or ''), len(lines), npub, ncited))
        out.append('</tbody></table></div>')
    out.append('</main>')
    return ''.join(out)


def decls_tbody(index, mapdata, links):
    """Rows of the declaration index: every public declaration, and the private ones that the map
    cites. `links` is a p2m.Links."""
    ent = {e['id']: e for e in mapdata['entries']}
    rev = mapdata['reverse_index']
    rows = []
    for d in index.decls:
        cited = rev.get(d.name, [])
        if d.private and not cited:
            continue
        name = disp(d.name)
        paper = ', '.join('<a href="../index.html#%s">%s</a>' % (entry_anchor(ent[x['id']]), esc(x['label'])) for x in cited)
        row = '<tr%s><td><a href="%s#L%d"><code>%s</code></a>%s</td><td>%s</td><td>%s</td><td>%s</td><td>%s</td></tr>' % (
            ' class="mapped"' if cited else '', esca(d.file[:-5] + '.html'), d.decl_line, esc(name),
            ' <span class="flag">private</span>' if d.private else '', 'theorem' if d.kind == 'lemma' else d.kind,
            esc(d.file[len('SurfaceBlowup/'):] if d.file.startswith('SurfaceBlowup/') else d.file), paper, links.cell(d))
        rows.append((name.casefold(), name, d.file, d.decl_line, row))
    rows.sort(key=lambda r: r[:4])
    return ''.join(r[4] for r in rows)
