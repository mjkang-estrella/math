import pathlib,json,hashlib,subprocess
from html.parser import HTMLParser
class Text(HTMLParser):
 def __init__(self):super().__init__();self.parts=[]
 def handle_data(self,d):self.parts.append(d)
 def text(self,b):self.feed(b.decode());return ' '.join(self.parts)
P=pathlib.Path(__file__).parent;out=[]
for e in json.loads((P/'retrieval-bindings.json').read_text()):
 if 'path' not in e:continue
 p=P/e['path'];b=p.read_bytes();assert len(b)==e['size'] and hashlib.sha256(b).hexdigest()==e['sha256']
 t=P/(e['name']+'.txt')
 if p.suffix=='.pdf':subprocess.run(['pdftotext','-layout',str(p),str(t)],check=True)
 else:t.write_text(Text().text(b))
 b=t.read_bytes();out.append({'path':t.name,'size':len(b),'sha256':hashlib.sha256(b).hexdigest(),'parent_sha256':e['sha256']})
(P/'derivative-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
