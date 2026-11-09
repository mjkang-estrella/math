import json,pathlib,hashlib
from html.parser import HTMLParser
P=pathlib.Path(__file__).parent
class Parser(HTMLParser):
 def __init__(self):super().__init__();self.s=[];self.skip=0
 def handle_starttag(self,t,a):
  if t in ['annotation','script','style']:self.skip+=1
  if t in ['p','section','h1','h2','h3','h4','div']:self.s.append('\n')
 def handle_endtag(self,t):
  if t in ['annotation','script','style']:self.skip-=1
 def handle_data(self,d):
  if not self.skip:self.s.append(d)
out=[]
for e in json.loads((P/'source-provenance.json').read_text()):
 f=pathlib.Path(e['path']);b=f.read_bytes();assert len(b)==e['size'] and hashlib.sha256(b).hexdigest()==e['sha256'];h=Parser();h.feed(b.decode());t='\n'.join(' '.join(s.split()) for s in ''.join(h.s).splitlines() if s.strip());d=f.with_suffix('.txt');d.write_text(t);out.append({'path':str(d),'size':d.stat().st_size,'sha256':hashlib.sha256(d.read_bytes()).hexdigest(),'source_sha256':e['sha256']})
(P/'derivative-bindings.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
