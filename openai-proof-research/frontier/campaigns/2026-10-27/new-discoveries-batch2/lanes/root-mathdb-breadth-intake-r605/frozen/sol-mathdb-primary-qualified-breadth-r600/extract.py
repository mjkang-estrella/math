import json,pathlib,hashlib
from html.parser import HTMLParser
D=pathlib.Path(__file__).resolve().parent
class Extract(HTMLParser):
 def __init__(self):super().__init__();self.out=[];self.skip=0
 def handle_starttag(self,t,a):
  if t in ['script','style']:self.skip+=1
  if t in ['p','div','section','h1','h2','h3']:self.out.append('\n')
 def handle_endtag(self,t):
  if t in ['script','style']:self.skip-=1
 def handle_data(self,s):
  if not self.skip:self.out.append(s)
out=[]
for e in json.loads((D/'source-provenance.json').read_text()):
 if 'failure' in e:continue
 b=pathlib.Path(e['path']).read_bytes();assert len(b)==e['size'] and hashlib.sha256(b).hexdigest()==e['sha256']
 p=Extract();p.feed(b.decode());s='\n'.join(x.strip() for x in ''.join(p.out).splitlines() if x.strip());f=D/(e['name']+'.txt');f.write_text(s);b=f.read_bytes();out.append({'path':str(f),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
(D/'derivative-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
