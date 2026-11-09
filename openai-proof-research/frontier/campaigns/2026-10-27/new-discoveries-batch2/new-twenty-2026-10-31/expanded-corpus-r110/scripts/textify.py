from pathlib import Path
from html.parser import HTMLParser
import re
class Text(HTMLParser):
 def __init__(self):super().__init__();self.out=[];self.math=0;self.skip=0
 def handle_starttag(self,t,a):
  if t=='math':self.math+=1;self.out.append(' $'+dict(a).get('alttext','')+'$ ')
  if t in ['script','style']:self.skip+=1
 def handle_endtag(self,t):
  if t=='math':self.math-=1
  if t in ['script','style']:self.skip-=1
  if t in ['p','div','section','h2','h3','li','tr']:self.out.append('\n')
 def handle_data(self,d):
  if not self.math and not self.skip:self.out.append(d)
D=Path(__file__).resolve().parents[1]
for p in (D/'sources').glob('*.html'):
 s=Text();s.feed(p.read_text());(D/'sources'/p.with_suffix('.txt').name).write_text(re.sub(r'[ \t]+',' ',''.join(s.out)))
