from pathlib import Path
from html.parser import HTMLParser
import json,hashlib
D=Path(__file__).parent
class P(HTMLParser):
 def __init__(self):super().__init__();self.x=[];self.math=0
 def handle_starttag(self,t,a):
  a=dict(a)
  if t=='math':self.math+=1;self.x.append(' $'+a.get('alttext','')+'$ ')
  if t in ('p','div','section','h1','h2','h3','h4','li'):self.x.append('\n')
 def handle_endtag(self,t):
  if t=='math':self.math-=1
 def handle_data(self,x):
  if not self.math:self.x.append(x)
out=[]
for x in json.loads((D/'retrieval-bindings.json').read_text()):
 if 'error' in x:continue
 p=D/x['path'];b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==x['sha256'] and len(b)==x['size']
 h=P();h.feed(b.decode());p=p.with_suffix('.txt');p.write_text(''.join(h.x));b=p.read_bytes();out.append(dict(path=p.name,size=len(b),sha256=hashlib.sha256(b).hexdigest()))
(D/'derivative-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
