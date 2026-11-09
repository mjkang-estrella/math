import pathlib,json,hashlib
from html.parser import HTMLParser
class Parser(HTMLParser):
 def __init__(self):super().__init__();self.out=[];self.skip=None
 def handle_starttag(self,t,a):
  if self.skip:return
  if t in ['math','script','style']:
   self.skip=t
   if t=='math':self.out.append(dict(a).get('alttext','[math]'))
  elif t in ['p','div','section','h1','h2','h3','li']:self.out.append('\n')
 def handle_endtag(self,t):
  if t==self.skip:self.skip=None
 def handle_data(self,d):
  if not self.skip:self.out.append(d)
P=pathlib.Path(__file__).resolve().parent;out=[]
for e in json.loads((P/'retrieval2-bindings.json').read_text()):
 if 'failure' in e:continue
 b=(P/(e['name']+'.html')).read_bytes();assert len(b)==e['size'] and hashlib.sha256(b).hexdigest()==e['sha256']
 s=Parser();s.feed(b.decode());b='\n'.join(x.strip() for x in ''.join(s.out).splitlines() if x.strip()).encode();p=P/(e['name']+'.txt');p.write_bytes(b);out.append({'path':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
(P/'derivative2-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
