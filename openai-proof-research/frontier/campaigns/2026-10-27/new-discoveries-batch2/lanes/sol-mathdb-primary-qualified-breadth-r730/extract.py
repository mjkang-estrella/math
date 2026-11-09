from html.parser import HTMLParser
import json,pathlib,hashlib
P=pathlib.Path(__file__).resolve().parent
class T(HTMLParser):
 def __init__(self):super().__init__();self.a=[];self.skip=0
 def handle_starttag(self,t,a):
  if t in ['script','style']:self.skip+=1
  if t in ['p','div','section','h1','h2','h3','li','tr']:self.a.append('\n')
 def handle_endtag(self,t):
  if t in ['script','style']:self.skip-=1
 def handle_data(self,s):
  if not self.skip:self.a.append(s)
out=[]
for e in json.loads((P/'source-provenance.json').read_text()):
 if 'path' not in e:continue
 b=(P/e['path']).read_bytes();assert len(b)==e['size'] and hashlib.sha256(b).hexdigest()==e['sha256']
 t=T();t.feed(b.decode());text='\n'.join(' '.join(s.split()) for s in ''.join(t.a).split('\n') if s.strip());p=P/(e['version']+'.txt');p.write_text(text)
 b=p.read_bytes();out.append(dict(path=p.name,sha256=hashlib.sha256(b).hexdigest(),size=len(b),parent=e['path']))
(P/'derivative-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
print('derivatives bound')
