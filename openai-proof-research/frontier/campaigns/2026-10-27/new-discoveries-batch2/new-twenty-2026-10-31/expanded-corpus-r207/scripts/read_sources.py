from pathlib import Path
from html.parser import HTMLParser
import re
L=Path(__file__).resolve().parents[1]
class P(HTMLParser):
 def __init__(self): super().__init__();self.out=[];self.skip=0
 def handle_starttag(self,t,a):
  d=dict(a)
  if t in ['script','style']: self.skip+=1
  if t in ['p','div','section','h1','h2','h3','table','tr']: self.out.append('\n')
  if t=='math': self.out.append(' $'+d.get('alttext','')+'$ ');self.skip+=1
 def handle_endtag(self,t):
  if t in ['script','style','math']: self.skip=max(0,self.skip-1)
 def handle_data(self,d):
  if not self.skip:self.out.append(d)
for p in (L/'sources').glob('*/body'):
 if '-html-' not in str(p) and '-abs-' not in str(p):continue
 q=P();q.feed(p.read_text(errors='replace')); t=re.sub(r'\n\s*\n','\n',''.join(q.out));(p.parent/'text.txt').write_text(t)
