from pathlib import Path
from html.parser import HTMLParser
class Read(HTMLParser):
 def __init__(self):super().__init__();self.s=[];self.skip=0
 def handle_starttag(self,t,a):
  if t=='math':self.s.append(dict(a).get('alttext',''));self.skip+=1
  elif t in ['p','h1','h2','h3','h4','section','div','li']:self.s.append('\n')
 def handle_endtag(self,t):
  if t=='math':self.skip-=1
 def handle_data(self,d):
  if not self.skip:self.s.append(d)
P=Path(__file__).resolve().parent
for f in (P/'sources').glob('*.html'):
 r=Read();r.feed(f.read_text());f.with_suffix('.txt').write_text(''.join(r.s))
