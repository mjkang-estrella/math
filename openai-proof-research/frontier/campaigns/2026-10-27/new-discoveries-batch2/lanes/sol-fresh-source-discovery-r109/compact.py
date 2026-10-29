from pathlib import Path
from html.parser import HTMLParser
class Compact(HTMLParser):
 def __init__(self):super().__init__();self.out=[];self.math=0
 def handle_starttag(self,t,a):
  if t=='math':self.math+=1;self.out.append(' $'+dict(a).get('alttext','')+'$ ')
  if not self.math and t in ['p','h1','h2','h3','h4','h5','h6','tr']:self.out.append('\n')
 def handle_endtag(self,t):
  if t=='math':self.math-=1
  if not self.math and t in ['p','h1','h2','h3','h4','h5','h6','tr']:self.out.append('\n')
 def handle_data(self,s):
  if not self.math:self.out.append(s)
P=Path(__file__).resolve().parent
for f in (P/'sources').glob('*-html.html'):
 t=Compact();t.feed(f.read_text());f.with_name(f.stem+'-compact.txt').write_text('\n'.join(' '.join(s.split()) for s in ''.join(t.out).split('\n') if s.strip()))
