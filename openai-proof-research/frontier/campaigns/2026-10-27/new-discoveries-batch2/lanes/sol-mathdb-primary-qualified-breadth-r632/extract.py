from pathlib import Path
import json,hashlib
from html.parser import HTMLParser
O=Path(__file__).resolve().parent
class P(HTMLParser):
 def __init__(self):super().__init__();self.a=[];self.skip=0
 def handle_starttag(self,t,a):
  if t in ['script','style']:self.skip+=1
  if t in ['p','div','section','h1','h2','h3','li']:self.a.append('\n')
 def handle_endtag(self,t):
  if t in ['script','style']:self.skip-=1
 def handle_data(self,d):
  if not self.skip:self.a.append(d)
b=[]
for e in json.loads((O/'fetch-provenance.json').read_text()):
 if e.get('status')!=200:continue
 p=O/(e['name']+'.html');d=p.read_bytes();assert hashlib.sha256(d).hexdigest()==e['sha256'] and len(d)==e['size']
 a=P();a.feed(d.decode());p=O/(e['name']+'.txt');p.write_text(''.join(a.a));d=p.read_bytes();b.append({'path':p.name,'sha256':hashlib.sha256(d).hexdigest(),'size':len(d)})
(O/'derivative-bindings.json').write_text(json.dumps(b,indent=2)+'\n')
