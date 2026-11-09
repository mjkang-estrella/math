from pathlib import Path
from html.parser import HTMLParser
import hashlib,json
D=Path(__file__).resolve().parent
class Text(HTMLParser):
 def __init__(self):super().__init__();self.parts=[]
 def handle_data(self,d):self.parts.append(d)
rows=json.loads((D/'source-provenance.json').read_text());out=[]
for r in rows:
 if 'path' not in r:continue
 p=D/r['path'];b=p.read_bytes();assert len(b)==r['size'] and hashlib.sha256(b).hexdigest()==r['sha256']
 t=Text();t.feed(b.decode('utf-8',errors='replace'));p=p.with_suffix('.txt');p.write_text('\n'.join(t.parts));b=p.read_bytes();out.append({'path':p.name,'sha256':hashlib.sha256(b).hexdigest(),'size':len(b),'from':r['path']})
(D/'derivative-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
