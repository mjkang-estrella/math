from html.parser import HTMLParser
from pathlib import Path
class Parser(HTMLParser):
 def __init__(self):super().__init__();self.out=[];self.skip=0
 def handle_starttag(self,t,a):
  if t=='math':self.out.append(' '+dict(a).get('alttext','')+' ');self.skip+=1
 def handle_endtag(self,t):
  if t=='math':self.skip-=1
 def handle_data(self,d):
  if not self.skip:self.out.append(d)
p=Path(__file__).resolve().parent/'sources'
for f in p.glob('*.html'):
 s=Parser();s.feed(f.read_text());f.with_suffix('.txt').write_text(' '.join(' '.join(s.out).split()))
