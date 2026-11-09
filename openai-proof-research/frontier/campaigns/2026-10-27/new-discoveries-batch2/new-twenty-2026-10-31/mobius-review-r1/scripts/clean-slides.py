from pathlib import Path
from html.parser import HTMLParser
D=Path(__file__).resolve().parents[1]
class P(HTMLParser):
 def __init__(self):super().__init__();self.skip=0;self.out=[]
 def handle_starttag(self,t,a):
  if t in ['script','style']:self.skip+=1
 def handle_endtag(self,t):
  if t in ['script','style']:self.skip-=1
 def handle_data(self,s):
  if not self.skip and s.strip(): self.out.append(s.strip())
p=P();p.feed((D/'downloads/slides/body').read_text());(D/'downloads/slides/visible.txt').write_text('\n'.join(p.out))
