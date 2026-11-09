from html.parser import HTMLParser
from pathlib import Path
import sys,hashlib,json
L=Path(__file__).resolve().parent
class P(HTMLParser):
 def __init__(self):super().__init__();self.text=[];self.links=[];self.href=None;self.lt=[]
 def handle_starttag(self,t,a):
  if t=='a':self.href=dict(a).get('href');self.lt=[]
 def handle_endtag(self,t):
  if t=='a' and self.href:self.links.append((self.href,' '.join(self.lt)));self.href=None
 def handle_data(self,d):
  self.text.append(d)
  if self.href:self.lt.append(d)
for n in sys.argv[1:]:
 p=L/'current'/n;b=p.read_bytes();h=hashlib.sha256(b).hexdigest();x=P();x.feed(b.decode(errors='replace'));out='\n'.join(x.text);(L/'current'/(n+'.txt')).write_text(out)
 print(n, h)
 if 'search-' in n:
  print(out[-27000:]);print(x.links)
 else:
  print('\n'.join(t for t in out.splitlines() if any(s in t.lower() for s in ['tournament','justice','2018','preprint','publication','next','pdf','download','honesty']))[:13000]); print([a for a in x.links if any(s in str(a).lower() for s in ['publication/','pdf','next','personal','homepage','research','honest','econ'])][:100])
 assert hashlib.sha256(p.read_bytes()).hexdigest()==h
