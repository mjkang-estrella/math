import pathlib,json,hashlib
from html.parser import HTMLParser
P=pathlib.Path(__file__).parent
class Extract(HTMLParser):
 def __init__(self):super().__init__();self.out=[];self.skip=0
 def handle_starttag(self,t,a):
  if t in ['script','style']:self.skip+=1
  if t in ['p','div','section','h1','h2','h3','li']:self.out.append('\n')
 def handle_endtag(self,t):
  if t in ['script','style']:self.skip-=1
 def handle_data(self,s):
  if not self.skip:self.out.append(s)
out=[]
for a in json.loads((P/'source-provenance.json').read_text()):
 p=P/a['file'];b=p.read_bytes();assert len(b)==a['size'] and hashlib.sha256(b).hexdigest()==a['sha256']
 e=Extract();e.feed(b.decode());s='\n'.join(' '.join(l.split()) for l in ''.join(e.out).splitlines() if l.strip());p=p.with_suffix('.txt');p.write_text(s);b=p.read_bytes();out.append({'file':p.name,'sha256':hashlib.sha256(b).hexdigest(),'size':len(b),'parent_sha256':a['sha256']})
(P/'derivative-bindings.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
