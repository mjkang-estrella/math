from pathlib import Path
from html.parser import HTMLParser
class Parser(HTMLParser):
 def __init__(self):super().__init__();self.out=[];self.depth=0
 def handle_starttag(self,t,a):
  if t=='math':self.out.append(dict(a).get('alttext',''));self.depth+=1
  if t in ['p','div','section','h1','h2','h3']:self.out.append('\n')
 def handle_endtag(self,t):
  if t=='math':self.depth-=1
 def handle_data(self,s):
  if not self.depth:self.out.append(s)
D=Path(__file__).resolve().parents[1]
for p in (D/'sources').glob('*.html'):
 s=Parser();s.feed(p.read_text());p.with_suffix('.txt').write_text(''.join(s.out))
