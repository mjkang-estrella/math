from pathlib import Path
import json,hashlib
from html.parser import HTMLParser
class Extract(HTMLParser):
 def __init__(self):super().__init__();self.parts=[]
 def handle_data(self,data):self.parts.append(data)
P=Path(__file__).resolve().parent;out=[]
for r in json.loads((P/'retrieval-bindings.json').read_text()):
 if 'path' not in r:continue
 b=(P/r['path']).read_bytes();assert len(b)==r['size'] and hashlib.sha256(b).hexdigest()==r['sha256']
 s=Extract();s.feed(b.decode());t=' '.join(s.parts);p=P/(r['key']+'.txt');p.write_text(t);b=p.read_bytes();out.append({'path':p.name,'sha256':hashlib.sha256(b).hexdigest(),'size':len(b),'parent_sha256':r['sha256']})
(P/'derivative-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
