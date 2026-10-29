from html.parser import HTMLParser
from pathlib import Path
class P(HTMLParser):
 def __init__(self):super().__init__();self.a=[];self.math=0;self.ann=False
 def handle_starttag(self,t,a):
  if t=='math':self.math+=1
  if t=='annotation':self.ann=True
  if t in ('p','h1','h2','h3','h6','li','tr'):self.a.append('\n')
 def handle_endtag(self,t):
  if t=='math':self.math-=1
  if t=='annotation':self.ann=False
 def handle_data(self,d):
  if not self.math or self.ann:self.a.append(d)
for f in Path('sources').glob('*.html'):
 p=P();p.feed(f.read_text());f.with_suffix('.txt').write_text(''.join(p.a))
