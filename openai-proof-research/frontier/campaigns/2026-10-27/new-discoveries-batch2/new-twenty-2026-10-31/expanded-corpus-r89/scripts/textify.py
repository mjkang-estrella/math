import pathlib
from html.parser import HTMLParser
class Text(HTMLParser):
 def __init__(self):super().__init__();self.parts=[];self.skip=0
 def handle_starttag(self,t,a):
  if t in ['script','style','annotation']:self.skip+=1
 def handle_endtag(self,t):
  if t in ['script','style','annotation']:self.skip-=1
  if t in ['p','div','section','h2','h3','h4']:self.parts.append('\n')
 def handle_data(self,d):
  if not self.skip:self.parts.append(d)
D=pathlib.Path(__file__).resolve().parents[1]
for p in (D/'sources').glob('*.html'):
 s=Text();s.feed(p.read_text());(p.with_suffix('.txt')).write_text(' '.join(s.parts))
