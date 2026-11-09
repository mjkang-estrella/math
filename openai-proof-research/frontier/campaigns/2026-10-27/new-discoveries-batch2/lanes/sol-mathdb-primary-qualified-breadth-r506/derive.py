from pathlib import Path
from html.parser import HTMLParser
import json,hashlib
class Parser(HTMLParser):
 def __init__(self):super().__init__();self.out=[];self.skip=0
 def handle_starttag(self,t,a):
  if self.skip:self.skip+=1;return
  if t in ('script','style','math'):
   if t=='math':self.out.append(dict(a).get('alttext',''))
   self.skip=1
  elif t in ('p','h1','h2','h3','h4','section','div','li'):self.out.append('\n')
 def handle_endtag(self,t):
  if self.skip:self.skip-=1
 def handle_data(self,d):
  if not self.skip:self.out.append(d)
O=Path(__file__).parent;log=[]
for e in json.loads((O/'source-bindings.json').read_text()):
 if 'path' not in e:continue
 p=Path(e['path']);b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==e['sha256'] and len(b)==e['size']
 s=Parser();s.feed(b.decode());p=p.with_suffix('.txt');p.write_text(''.join(s.out));b=p.read_bytes();log.append({'path':str(p.resolve()),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b),'derives_from':e['sha256']})
(O/'derivative-bindings.json').write_text(json.dumps(log,indent=2)+'\n')
