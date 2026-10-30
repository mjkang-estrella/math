from pathlib import Path
from html.parser import HTMLParser
class Reader(HTMLParser):
 def __init__(self):super().__init__();self.out=[];self.skip=0
 def handle_starttag(self,t,a):
  if t in ['script','style','nav']:self.skip+=1
  if t in ['p','div','section','li','h1','h2','h3']:self.out.append('\n')
 def handle_endtag(self,t):
  if t in ['script','style','nav']:self.skip-=1
 def handle_data(self,d):
  if not self.skip:self.out.append(d)
L=Path(__file__).resolve().parent
for p in (L/'sources').glob('*.html'):
 s=Reader();s.feed(p.read_text())
 (p.with_suffix('.txt')).write_text(''.join(s.out))
 print(p.name)
