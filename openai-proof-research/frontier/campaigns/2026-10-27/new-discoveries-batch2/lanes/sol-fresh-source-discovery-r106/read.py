from pathlib import Path
from html.parser import HTMLParser
class Reader(HTMLParser):
 def __init__(self):super().__init__();self.rows=[];self.math=0;self.skip=0
 def handle_starttag(self,tag,attrs):
  a=dict(attrs)
  if tag=='math':self.math+=1;self.rows.append(a.get('alttext',''))
  if tag in ['script','style']:self.skip+=1
  if tag in ['p','div','section']:self.rows.append('\n')
 def handle_endtag(self,tag):
  if tag=='math':self.math-=1
  if tag in ['script','style']:self.skip-=1
 def handle_data(self,data):
  if not self.math and not self.skip:self.rows.append(data)
P=Path(__file__).resolve().parent
for name in ['kunisky','mulgund','transport']:
 s=Reader();s.feed((P/'sources'/f'{name}.html').read_text());(P/'sources'/f'{name}.txt').write_text(''.join(s.rows))
