"""Read a published Lean page back into lines of tokens. Used by validate_pages.py."""
import html
import os
import re

LINE_RE = re.compile(
    r'<span class="ln" id="L(\d+)"( data-decl="([^"]*)")?><a class="lnum" href="#L\d+">\d+</a>'
    r'<span class="lc">(.*?)</span>(<a class="paper-chip[^>]*>.*?</a>)*</span>(?=<span class="ln"|</pre>)', re.S)
TOK_RE = re.compile(r'<span class="([a-z]+)">(.*?)</span>|<a class="id" href="([^"]*)">(.*?)</a>|([^<]+)', re.S)
PRE = '<pre class="lean lean-src">'


def read_page(path):
    """Lines of a Lean page: dicts with the line number `n`, the declaration name `decl` (or
    None), the inner HTML `html` and its tokens `toks` as (class, text, href)."""
    with open(path, encoding='utf-8') as f:
        s = f.read()
    i = s.index(PRE) + len(PRE)
    body = s[i:s.index('</pre>', i) + len('</pre>')]
    lines = []
    pos = 0
    for m in LINE_RE.finditer(body):
        assert m.start() == pos, (path, m.group(1), body[pos:pos + 200])
        pos = m.end()
        inner = m.group(4)
        toks = []
        p = 0
        for t in TOK_RE.finditer(inner):
            assert t.start() == p, (path, m.group(1), inner[p:p + 120])
            p = t.end()
            if t.group(1):
                toks.append((t.group(1), html.unescape(t.group(2)), None))
            elif t.group(3) is not None:
                toks.append(('id', html.unescape(t.group(4)), t.group(3)))
            else:
                toks.append((None, html.unescape(t.group(5)), None))
        assert p == len(inner), (path, m.group(1), inner[p:p + 120])
        lines.append({'n': int(m.group(1)), 'decl': html.unescape(m.group(3)) if m.group(3) else None,
                      'html': inner, 'toks': toks})
    assert body[pos:] == '</pre>', (path, body[pos:pos + 200])
    return lines


def lean_files(site, dirs):
    """Lean files that have a page under SITE/lean, as paths relative to SITE/lean."""
    out = []
    for top in dirs:
        for dp, _, fn in os.walk(os.path.join(site, 'lean', top)):
            out += [os.path.relpath(os.path.join(dp, f), os.path.join(site, 'lean'))[:-5] + '.lean'
                    for f in fn if f.endswith('.html')]
    return sorted(out)
