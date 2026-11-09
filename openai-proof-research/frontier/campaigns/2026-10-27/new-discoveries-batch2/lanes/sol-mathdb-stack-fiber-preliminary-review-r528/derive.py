from pathlib import Path
from html.parser import HTMLParser
import json,hashlib
D=Path(__file__).resolve().parent;P=D.parent/'sol-mathdb-primary-qualified-breadth-r522'
class X(HTMLParser):
 def __init__(self):super().__init__();self.a=[]
 def handle_data(self,s):self.a.append(s)
x=X();x.feed((P/'2410.17057v1.html').read_text());p=D/'primary-independent.txt';p.write_text('\n'.join(x.a));b=p.read_bytes();(D/'derivative-bindings.json').write_text(json.dumps([dict(path=str(p),size=len(b),sha256=hashlib.sha256(b).hexdigest())],indent=2)+'\n')
rows=json.loads((D/'derivative-bindings.json').read_text())
for name in ['defant-zheng','yi']:
 x=X();x.feed((D/(name+'.html')).read_text());p=D/(name+'.txt');p.write_text('\n'.join(x.a));b=p.read_bytes();rows.append(dict(path=str(p),size=len(b),sha256=hashlib.sha256(b).hexdigest()))
(D/'derivative-bindings.json').write_text(json.dumps(rows,indent=2)+'\n')
