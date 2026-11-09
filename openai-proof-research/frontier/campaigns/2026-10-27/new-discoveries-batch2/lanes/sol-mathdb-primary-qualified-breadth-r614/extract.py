from html.parser import HTMLParser
from pathlib import Path
import json,hashlib
L=Path(__file__).parent
class P(HTMLParser):
 def __init__(self):super().__init__();self.out=[];self.skip=0
 def handle_starttag(self,t,a):
  if t in ['script','style','math']:self.skip+=1
  if t=='math':self.out.append(' '+dict(a).get('alttext','')+' ')
  if t in ['p','div','section','h1','h2','h3','li']:self.out.append('\n')
 def handle_endtag(self,t):
  if t in ['script','style','math']:self.skip-=1
 def handle_data(self,d):
  if not self.skip:self.out.append(d)
r=[]
for s in json.loads((L/'source-provenance.json').read_text()):
 p=L/s['path'];b=p.read_bytes();assert len(b)==s['size'] and hashlib.sha256(b).hexdigest()==s['sha256']
 h=P();h.feed(b.decode());p=p.with_suffix('.txt');p.write_text(''.join(h.out));b=p.read_bytes();r.append({'path':p.name,'size':len(b),'sha256':hashlib.sha256(b).hexdigest(),'source':s['url']})
(L/'derivative-bindings.json').write_text(json.dumps(r,indent=2)+'\n');print(r)
