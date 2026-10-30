from html.parser import HTMLParser
from pathlib import Path
import sys
class Extract(HTMLParser):
    def __init__(self):super().__init__();self.out=[];self.skip=0
    def handle_starttag(self,t,a):
        a=dict(a)
        if t=='math':self.out.append(' '+a.get('alttext','')+' ');self.skip+=1
        elif t in ['script','style']:self.skip+=1
        elif not self.skip and t in ['p','div','section','h1','h2','h3','li','tr']:self.out.append('\n')
    def handle_endtag(self,t):
        if t in ['math','script','style']:self.skip=max(0,self.skip-1)
    def handle_data(self,d):
        if not self.skip:self.out.append(d)
for s in sys.argv[1:]:
    p=Path(s);e=Extract();e.feed(p.read_text());p.with_suffix('.txt').write_text(''.join(e.out))
