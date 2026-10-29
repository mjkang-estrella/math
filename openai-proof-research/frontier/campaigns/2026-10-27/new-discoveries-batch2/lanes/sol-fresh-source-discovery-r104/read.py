from research import P
from html.parser import HTMLParser
class Parser(HTMLParser):
 def __init__(self):super().__init__();self.out=[];self.skip=0
 def handle_starttag(self,t,a):
  if t in ['script','style']:self.skip+=1
  if t in ['p','h1','h2','h3','h4','h5','h6','section','li','div']:self.out.append('\n')
 def handle_endtag(self,t):
  if t in ['script','style']:self.skip-=1
 def handle_data(self,d):
  if not self.skip:self.out.append(d)
for f in (P/'sources').glob('*.html'):
 p=Parser();p.feed(f.read_text());s='\n'.join(' '.join(l.split()) for l in ''.join(p.out).splitlines() if l.strip());f.with_suffix('.txt').write_text(s)
