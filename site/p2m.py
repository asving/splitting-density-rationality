"""Prove2Me links of the declarations.

Two inputs, both in the site folder. `data/prove2me_nodes.json` is the snapshot of the public tree
`TypeDensity`: node label, theorem name, kind, source and the id of the public page. The Prove2Me
column of `lean/decls.html` says which nodes belong to which declaration. The original generator
filled that column from the Prove2Me catalog of the original workspace, which no longer exists, so
the column is carried over row by row. A declaration that has no row yet gets the node of the same
name, if it is a public theorem.
"""
import html
import re

from leanpage import disp, esca

ROW_RE = re.compile(
    r'<tr(?: class="mapped")?><td><a href="([^"#]*)#L\d+"><code>(.*?)</code></a>'
    r'(?: <span class="flag">private</span>)?</td>(?:<td>.*?</td>){3}<td>(.*?)</td>$', re.S)


class Links:
    def __init__(self, nodes, decls_html, url_template):
        self.nodes = nodes['nodes']
        self.url_template = url_template
        self.by_name = {v['theorem_name']: k for k, v in self.nodes.items() if v['kind'] == 'theorem'}
        self.rows = {}  # (displayed name, page) -> node labels
        body = decls_html[decls_html.index('<tbody>') + 7:decls_html.index('</tbody>')]
        for r in body.split('</tr>')[:-1]:
            m = ROW_RE.match(r)
            assert m, 'unexpected row in lean/decls.html: ' + r[:200]
            self.rows[(html.unescape(m.group(2)), m.group(1))] = re.findall(r'>([A-Z]\d+)</a>', m.group(3))

    def labels(self, d):
        """Node labels of the declaration `d` (a leansrc.Decl)."""
        key = (disp(d.name), d.file[:-5] + '.html')
        if key in self.rows:
            return self.rows[key]
        if d.kind in ('theorem', 'lemma') and not d.private:
            label = self.by_name.get('TypeDensity.' + disp(d.name))
            return [label] if label else []
        return []

    def url(self, label):
        return self.url_template.replace('{theorem_id}', self.nodes[label]['theorem_id'])

    def cell(self, d):
        """The Prove2Me cell of the declaration index."""
        return ', '.join('<a class="ext" href="%s" rel="noopener">%s</a>' % (esca(self.url(k)), k)
                         for k in self.labels(d))

    def records(self, d):
        """The `prove2me` list of a declaration in data/paper_lean_map.json."""
        out = []
        for k in self.labels(d):
            v = self.nodes[k]
            out.append({'node': k, 'theorem_name': v['theorem_name'], 'kind': v['kind'],
                        'theorem_id': v['theorem_id'], 'status': v['status'], 'url': self.url(k),
                        'blueprint_source': v['source']})
        return out
