import pathlib,json,hashlib
from html.parser import HTMLParser
class Extract(HTMLParser):
 def __init__(self):super().__init__();self.out=[];self.skip=0;self.math=0
 def handle_starttag(self,t,a):
  a=dict(a)
  if t in ('script','style'):self.skip+=1
  if t=='math':self.math+=1;self.out.append(' $'+a.get('alttext','')+'$ ')
  if t in ('p','section','h1','h2','h3','h4','div','li','tr'):self.out.append('\n')
 def handle_endtag(self,t):
  if t in ('script','style'):self.skip-=1
  if t=='math':self.math-=1
 def handle_data(self,d):
  if not self.skip and not self.math:self.out.append(d)
P=pathlib.Path(__file__).parent;out=[]
for e in json.loads((P/'source-provenance.json').read_text()):
 if 'path' not in e:continue
 b=pathlib.Path(e['path']).read_bytes();assert len(b)==e['size'] and hashlib.sha256(b).hexdigest()==e['sha256']
 x=Extract();x.feed(b.decode());p=P/(e['name']+'.txt');p.write_text(''.join(x.out))
 d=p.read_bytes();out.append({'path':str(p),'size':len(d),'sha256':hashlib.sha256(d).hexdigest(),'input_sha256':e['sha256']})
(P/'derivative-bindings.json').write_text(json.dumps(out,indent=2)+'\n');print('Bound',len(out),'text derivatives before reading')
