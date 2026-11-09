from html.parser import HTMLParser
from pathlib import Path
import sys
class P(HTMLParser):
 def __init__(self):super().__init__();self.skip=0;self.ss=[]
 def handle_starttag(self,t,a):
  if t in ['script','style']:self.skip+=1
 def handle_endtag(self,t):
  if t in ['script','style']:self.skip=max(0,self.skip-1)
  if t in ['p','div','section']:self.ss.append('\n')
 def handle_data(self,d):
  if not self.skip:self.ss.append(d)
for f in sys.argv[1:]:
 p=P();p.feed(Path(f).read_text(errors='replace'));Path('outputs/'+Path(f).stem+'.txt').write_text(' '.join(p.ss))
