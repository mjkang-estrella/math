import pathlib,json,hashlib
from html.parser import HTMLParser
class Parser(HTMLParser):
 def __init__(self):super().__init__();self.parts=[]
 def handle_data(self,t):self.parts.append(t)
P=pathlib.Path(__file__).resolve().parent;out=[]
for e in json.loads((P/'download-bindings.json').read_text()):
 if 'path' not in e:continue
 b=(P/e['path']).read_bytes();assert len(b)==e['size'] and hashlib.sha256(b).hexdigest()==e['sha256']
 s=Parser();s.feed(b.decode());text=' '.join(s.parts);n=e['path'].replace('.html','.txt');b=text.encode();(P/n).write_bytes(b);out.append({'path':n,'size':len(b),'sha256':hashlib.sha256(b).hexdigest(),'source':e['path']})
(P/'derivative-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
