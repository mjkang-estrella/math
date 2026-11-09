"""Convert an (untrusted) HTML body (ar5iv / arXiv HTML) to plain text, using math alttext.
Refuses to overwrite. usage: html2txt.py IN.body OUT.txt"""
import html.parser
import os
import sys

src, dst = sys.argv[1], sys.argv[2]
if os.path.exists(dst):
    raise SystemExit('refusing to overwrite ' + dst)


class P(html.parser.HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.out = []
        self.skip = 0
        self.math = 0

    def handle_starttag(self, tag, attrs):
        a = dict(attrs)
        if tag in ('script', 'style'):
            self.skip += 1
        if tag == 'math':
            if self.math == 0:
                self.out.append(' $' + (a.get('alttext') or '') + '$ ')
            self.math += 1
        if tag in ('p', 'div', 'br', 'li', 'h1', 'h2', 'h3', 'h4', 'h5', 'h6', 'tr', 'section'):
            self.out.append('\n')

    def handle_endtag(self, tag):
        if tag in ('script', 'style') and self.skip:
            self.skip -= 1
        if tag == 'math' and self.math:
            self.math -= 1

    def handle_data(self, d):
        if not self.skip and not self.math:
            self.out.append(d)


p = P()
p.feed(open(src, encoding='utf-8', errors='replace').read())
text = ''.join(p.out)
lines = [' '.join(l.split()) for l in text.splitlines()]
text = '\n'.join(l for l in lines if l)
with open(dst, 'x', encoding='utf-8') as f:
    f.write(text)
print(len(text))
