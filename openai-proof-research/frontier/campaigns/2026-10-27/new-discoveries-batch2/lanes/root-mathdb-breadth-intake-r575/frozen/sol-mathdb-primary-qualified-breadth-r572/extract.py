from html.parser import HTMLParser
import pathlib,json,hashlib
P=pathlib.Path(__file__).resolve().parent
class Parser(HTMLParser):
 def __init__(self):super().__init__();self.out=[];self.math=0;self.skip=0
 def handle_starttag(self,t,a):
  d=dict(a)
  if t=='math':self.math+=1;self.out.append(' $'+d.get('alttext','')+'$ ')
  if t in ['script','style']:self.skip+=1
  if t in ['p','div','section','h1','h2','h3','h4']:self.out.append('\n')
 def handle_endtag(self,t):
  if t=='math':self.math-=1
  if t in ['script','style']:self.skip-=1
 def handle_data(self,s):
  if not self.math and not self.skip:self.out.append(s)
log=[]
for e in json.loads((P/'source-provenance.json').read_text()):
 if 'path' not in e:continue
 b=(P/e['path']).read_bytes();assert hashlib.sha256(b).hexdigest()==e['sha256'];p=Parser();p.feed(b.decode());s='\n'.join(x.strip() for x in ''.join(p.out).splitlines() if x.strip());name=e['path']+'.txt';b=s.encode();(P/name).write_bytes(b);log.append({'path':name,'size':len(b),'sha256':hashlib.sha256(b).hexdigest(),'parent_sha256':e['sha256']})
(P/'derivative-bindings.json').write_text(json.dumps(log,indent=2)+'\n')
