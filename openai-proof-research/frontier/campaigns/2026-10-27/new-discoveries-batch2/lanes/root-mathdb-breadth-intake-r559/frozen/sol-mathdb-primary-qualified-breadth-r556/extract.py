import json,pathlib,hashlib
from html.parser import HTMLParser
class Parser(HTMLParser):
 def __init__(self):super().__init__();self.parts=[];self.skip=0
 def handle_starttag(self,t,a):
  if self.skip:self.skip+=1;return
  if t=='math':self.parts.append(dict(a).get('alttext',''));self.skip=1
  elif t in ['p','div','section','h1','h2','h3','h4','li']:self.parts.append('\n')
 def handle_endtag(self,t):
  if self.skip:self.skip-=1
 def handle_data(self,d):
  if not self.skip:self.parts.append(d)
O=pathlib.Path(__file__).resolve().parent;out=[]
for e in json.loads((O/'downloads.json').read_text()):
 if 'path' not in e:continue
 p=pathlib.Path(e['path']);b=p.read_bytes();assert len(b)==e['size'] and hashlib.sha256(b).hexdigest()==e['sha256']
 s=Parser();s.feed(b.decode());p=O/(e['name']+'.txt');p.write_text(''.join(s.parts));b=p.read_bytes();out.append({'path':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
(O/'derivative-bindings.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
