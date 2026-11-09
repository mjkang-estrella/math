import pathlib,json,hashlib
from html.parser import HTMLParser
D=pathlib.Path(__file__).parent
class P(HTMLParser):
 def __init__(self):super().__init__();self.o=[]
 def handle_data(self,d):self.o.append(d)
out=[]
for name in ['downloads.json','downloads2.json']:
 for e in json.loads((D/name).read_text()):
  if 'path' not in e:continue
  b=pathlib.Path(e['path']).read_bytes();assert hashlib.sha256(b).hexdigest()==e['sha256']
  a=P();a.feed(b.decode());p=D/(e['name']+'.txt');p.write_text(' '.join(' '.join(a.o).split()));out.append({'path':str(p.resolve()),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'size':p.stat().st_size})
(D/'derivative-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
