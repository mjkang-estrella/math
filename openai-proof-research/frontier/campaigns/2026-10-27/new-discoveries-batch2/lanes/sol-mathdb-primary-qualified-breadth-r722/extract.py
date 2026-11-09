import pathlib,json,hashlib
from html.parser import HTMLParser
D=pathlib.Path(__file__).parent
class P(HTMLParser):
 def __init__(self):super().__init__();self.s=[];self.math=0
 def handle_starttag(self,t,a):
  if t in ['p','div','section','h1','h2','h3','h4','li']:self.s.append('\n')
  if t=='math':self.math+=1;self.s.append(dict(a).get('alttext',''))
 def handle_endtag(self,t):
  if t=='math':self.math-=1
 def handle_data(self,d):
  if not self.math:self.s.append(d)
out=[]
for x in json.loads((D/'source-provenance.json').read_text()):
 if 'error' in x:continue
 b=(D/x['path']).read_bytes();assert hashlib.sha256(b).hexdigest()==x['sha256'];p=P();p.feed(b.decode());b=''.join(p.s).encode();f=D/(x['version']+'.txt');f.write_bytes(b);out.append(dict(path=f.name,sha256=hashlib.sha256(b).hexdigest(),size=len(b),parent=x['path']))
(D/'derivative-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
