import sys, re, html, pathlib
# usage: absinfo.py FILE [FILE...]: print title, authors, versions, abstract, comments of arXiv abs pages
for f in sys.argv[1:]:
    t = pathlib.Path(f).read_text(errors='replace')
    def g(p):
        m = re.search(p, t, re.S)
        return html.unescape(re.sub(r'<[^>]+>', '', m.group(1))).strip() if m else None
    title = g(r'<h1 class="title mathjax">(.*?)</h1>')
    auth = g(r'<div class="authors">(.*?)</div>')
    abst = g(r'<blockquote class="abstract mathjax">(.*?)</blockquote>')
    com = g(r'<td class="tablecell comments mathjax">(.*?)</td>')
    jr = g(r'<td class="tablecell jref">(.*?)</td>')
    vers = re.findall(r'<strong>\[(v\d+)\]</strong>\s*(.*?)\s*\(', t)
    print('##', f)
    print(title, '|', re.sub(r'\s+', ' ', auth or ''))
    print('versions', vers, '| comments', com, '| jref', jr)
    print(re.sub(r'\s+', ' ', abst or '')[:1500])
    print()
