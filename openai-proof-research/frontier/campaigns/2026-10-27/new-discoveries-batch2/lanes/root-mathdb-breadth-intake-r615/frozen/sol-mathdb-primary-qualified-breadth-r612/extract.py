import json,pathlib,hashlib
from html.parser import HTMLParser
P=pathlib.Path(__file__).parent
class Parser(HTMLParser):
 def __init__(self):super().__init__();self.out=[];self.skip=0
 def handle_starttag(self,t,a):
  if t in ['script','style']:self.skip+=1
  if t in ['p','div','section','h1','h2','h3','h4','li','tr']:self.out.append('\n')
 def handle_endtag(self,t):
  if t in ['script','style']:self.skip-=1
 def handle_data(self,d):
  if not self.skip:self.out.append(d)
log=[]
for e in json.loads((P/'source-provenance.json').read_text()):
 if 'path' not in e:continue
 p=pathlib.Path(e['path']);b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==e['sha256'] and len(b)==e['size']
 s=Parser();s.feed(b.decode());out='\n'.join(' '.join(x.split()) for x in ''.join(s.out).splitlines() if x.strip());dest=p.with_suffix('.txt');dest.write_text(out)
 b=dest.read_bytes();log.append({'path':str(dest),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b),'source_sha256':e['sha256'],'method':'stdlib HTMLParser data nodes; math Unicode retained; formula layout may degrade'})
(P/'derivative-bindings.json').write_text(json.dumps(log,indent=2)+'\n')
