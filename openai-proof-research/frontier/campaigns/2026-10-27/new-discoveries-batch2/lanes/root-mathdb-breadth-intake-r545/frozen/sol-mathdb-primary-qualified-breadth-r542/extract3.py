from pathlib import Path
from html.parser import HTMLParser
import json,hashlib
O=Path(__file__).resolve().parent
class P(HTMLParser):
 def __init__(self):super().__init__();self.out=[]
 def handle_starttag(self,t,a):
  if t in ['p','div','section','h1','h2','h3','li']:self.out.append('\n')
 def handle_data(self,d):self.out.append(d)
out=[]
for e in json.loads((O/'retrieval3-bindings.json').read_text()):
 if 'path' not in e:continue
 b=Path(e['path']).read_bytes();assert len(b)==e['size'] and hashlib.sha256(b).hexdigest()==e['sha256']
 p=P();p.feed(b.decode());s=''.join(p.out);dst=Path(e['path']).with_suffix('.txt');dst.write_text(s)
 b=dst.read_bytes();out.append({'path':str(dst),'size':len(b),'sha256':hashlib.sha256(b).hexdigest(),'parent_sha256':e['sha256']})
(O/'derivative3-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
