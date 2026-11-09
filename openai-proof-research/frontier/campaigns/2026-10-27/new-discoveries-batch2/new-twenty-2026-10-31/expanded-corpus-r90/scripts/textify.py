from pathlib import Path
from html.parser import HTMLParser
class Text(HTMLParser):
 def __init__(self):super().__init__();self.out=[];self.skip=0;self.math=0
 def handle_starttag(self,tag,attrs):
  a=dict(attrs)
  if tag in ('script','style'):self.skip+=1
  if tag=='math':
   if not self.math:self.out.append(' $'+a.get('alttext','')+'$ ')
   self.math+=1
  if tag in ('p','section','div','h1','h2','h3','h4','li'):self.out.append('\n')
 def handle_endtag(self,tag):
  if tag in ('script','style'):self.skip=max(0,self.skip-1)
  if tag=='math':self.math=max(0,self.math-1)
 def handle_data(self,data):
  if not self.skip and not self.math:self.out.append(data)
D=Path(__file__).resolve().parents[1]
for p in (D/'sources').glob('*.html'):
 s=Text();s.feed(p.read_text());(D/'sources'/(p.stem+('.landing.txt' if p.with_suffix('.pdf').exists() else '.txt'))).write_text(''.join(s.out))
