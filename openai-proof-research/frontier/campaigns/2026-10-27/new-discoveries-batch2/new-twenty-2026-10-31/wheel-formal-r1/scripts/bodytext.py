from html.parser import HTMLParser
from pathlib import Path
class Text(HTMLParser):
 def __init__(self):super().__init__();self.out=[];self.skip=0
 def handle_starttag(self,t,a):
  if t in ['script','style']:self.skip+=1
  if t in ['p','div','section','h1','h2','h3','h4']:self.out.append('\n')
  if t=='math':
   for k,v in a:
    if k=='alttext':self.out.append(' '+v+' ')
 def handle_endtag(self,t):
  if t in ['script','style']:self.skip-=1
 def handle_data(self,d):
  if not self.skip:self.out.append(d)
for p in Path('sources').glob('*.html'):
 q=p.with_suffix('.txt')
 if q.exists():continue
 t=Text();t.feed(p.read_text());q.write_text(''.join(t.out))
