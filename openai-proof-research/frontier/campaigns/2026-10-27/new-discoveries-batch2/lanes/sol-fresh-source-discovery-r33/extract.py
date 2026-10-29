import resource,signal
resource.setrlimit(resource.RLIMIT_AS,(536870912,536870912));resource.setrlimit(resource.RLIMIT_CPU,(20,20));signal.alarm(25)
from pathlib import Path
from html.parser import HTMLParser
class P(HTMLParser):
 def __init__(self):super().__init__();self.parts=[];self.skip=0
 def handle_starttag(self,t,a):
  if t in ['script','style']:self.skip+=1
 def handle_endtag(self,t):
  if t in ['script','style']:self.skip-=1
 def handle_data(self,x):
  if not self.skip:self.parts.append(x)
b=Path(__file__).resolve().parent
for f in (b/'sources').glob('*.html'):
 p=P();p.feed(f.read_text());f.with_suffix('.txt').write_text(' '.join(p.parts))
