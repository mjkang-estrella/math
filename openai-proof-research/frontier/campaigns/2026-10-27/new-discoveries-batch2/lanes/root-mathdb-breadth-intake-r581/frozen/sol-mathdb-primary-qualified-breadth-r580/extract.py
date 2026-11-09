from pathlib import Path
from html.parser import HTMLParser
import json,hashlib
D=Path(__file__).parent
class P(HTMLParser):
 def __init__(self):super().__init__();self.t=[]
 def handle_data(self,t):self.t.append(t)
p=P();r=json.loads((D/'source-provenance.json').read_text())[0];b=(D/r['path']).read_bytes();assert hashlib.sha256(b).hexdigest()==r['sha256'];p.feed(b.decode());q=D/'2512.16062v2.txt';q.write_text(' '.join(p.t));b=q.read_bytes();(D/'derivative-bindings.json').write_text(json.dumps([dict(path=q.name,size=len(b),sha256=hashlib.sha256(b).hexdigest(),parent=r['sha256'])],indent=2)+'\n')
