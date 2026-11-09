import pathlib,json,hashlib
from html.parser import HTMLParser
P=pathlib.Path(__file__).resolve().parent
class Extract(HTMLParser):
 def __init__(self):super().__init__();self.out=[];self.skip=0
 def handle_starttag(self,t,a):
  if self.skip:self.skip+=1;return
  if t in ['script','style','math']:
   if t=='math':self.out.append(dict(a).get('alttext','[math]'))
   self.skip=1
  if t in ['p','div','section','h1','h2','h3','h4','li']:self.out.append('\n')
 def handle_endtag(self,t):
  if self.skip:self.skip-=1
 def handle_data(self,d):
  if not self.skip:self.out.append(d)
out=[]
for r in json.loads((P/'source-provenance.json').read_text()):
 b=pathlib.Path(r['path']).read_bytes();assert hashlib.sha256(b).hexdigest()==r['sha256'];e=Extract();e.feed(b.decode());p=P/(pathlib.Path(r['path']).stem+'.txt');b=''.join(e.out).encode();p.write_bytes(b);out.append({'path':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest(),'parent_sha256':r['sha256']})
(P/'derivative-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
