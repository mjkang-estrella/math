from pathlib import Path
from html.parser import HTMLParser
class P(HTMLParser):
 def __init__(self):super().__init__();self.a=[];self.m=0
 def handle_starttag(self,t,a):
  if t=='math':self.m+=1;self.a.append(dict(a).get('alttext',''))
  if t in ['p','div','section','h1','h2','h3','li']:self.a.append('\n')
 def handle_endtag(self,t):
  if t=='math':self.m-=1
 def handle_data(self,s):
  if not self.m:self.a.append(s)
L=Path(__file__).resolve().parent
for f in (L/'sources').glob('*.html'):
 p=P();p.feed(f.read_text());f.with_suffix('.txt').write_text(''.join(p.a))
