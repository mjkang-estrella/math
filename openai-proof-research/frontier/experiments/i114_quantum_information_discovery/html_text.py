"""Deterministic offline HTML-to-text view; run with -B. No writes."""
from html.parser import HTMLParser
class Parser(HTMLParser):
    def __init__(self):
        super().__init__(); self.out=[]; self.math=0; self.skip=0
    def handle_starttag(self,t,a):
        d=dict(a)
        if t in ['script','style']: self.skip+=1
        if t=='math': self.math+=1; self.out.append(' $'+d.get('alttext','')+'$ ')
        if t in ['p','div','section','h1','h2','h3','h4','li','tr']: self.out.append('\n')
    def handle_endtag(self,t):
        if t=='math': self.math-=1
        if t in ['script','style']: self.skip-=1
    def handle_data(self,d):
        if not self.math and not self.skip: self.out.append(d)
def convert(s):
    p=Parser();p.feed(s)
    return '\n'.join(x.strip() for x in ''.join(p.out).splitlines() if x.strip())+'\n'
