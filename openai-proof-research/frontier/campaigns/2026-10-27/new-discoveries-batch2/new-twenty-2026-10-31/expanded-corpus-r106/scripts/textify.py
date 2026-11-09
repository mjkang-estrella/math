from html.parser import HTMLParser
from pathlib import Path
class P(HTMLParser):
 def __init__(self):super().__init__();self.s=[];self.math=0
 def handle_starttag(self,t,a):
  d=dict(a)
  if t=='math':self.s.append(' '+d.get('alttext','')+' ');self.math+=1
  elif t in ['p','h1','h2','h3','h4','h5','figure','table']:self.s.append('\n')
 def handle_endtag(self,t):
  if t=='math':self.math-=1
  elif t in ['p','h1','h2','h3','h4','h5','figure','table']:self.s.append('\n')
 def handle_data(self,d):
  if not self.math:self.s.append(d)
for p in Path('sources').glob('*.html'):
 s=P();s.feed(p.read_text());p.with_suffix('.txt').write_text(''.join(s.s))
