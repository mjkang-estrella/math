from pathlib import Path
from html.parser import HTMLParser
class Parser(HTMLParser):
 def __init__(self):super().__init__();self.parts=[];self.skip=0
 def handle_starttag(self,t,a):
  if t in ('script','style'):self.skip+=1
 def handle_endtag(self,t):
  if t in ('script','style'):self.skip=max(0,self.skip-1)
 def handle_data(self,d):
  if not self.skip:self.parts.append(d)
L=Path(__file__).resolve().parent
for p in (L/'sources').glob('*.html'):
 s=Parser();s.feed(p.read_text())
 (p.with_suffix('.txt')).write_text(' '.join(' '.join(s.parts).split()))
