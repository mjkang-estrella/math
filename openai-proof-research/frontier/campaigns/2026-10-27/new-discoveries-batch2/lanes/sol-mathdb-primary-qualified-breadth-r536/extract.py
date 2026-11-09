import pathlib,json,hashlib
from html.parser import HTMLParser
P=pathlib.Path(__file__).resolve().parent
class Parser(HTMLParser):
 def __init__(self):super().__init__();self.out=[];self.skip=0
 def handle_starttag(self,t,a):
  if self.skip:self.skip+=1;return
  if t in ['script','style']:self.skip=1;return
  if t=='math':self.out.append(' $'+dict(a).get('alttext','')+'$ ');self.skip=1;return
  if t in ['p','div','section','h1','h2','h3','h4','li','tr']:self.out.append('\n')
 def handle_endtag(self,t):
  if self.skip:self.skip-=1
 def handle_data(self,s):
  if not self.skip:self.out.append(s)
out=[]
for e in json.loads((P/'download-bindings.json').read_text()):
 if 'path' not in e:continue
 b=(P/e['path']).read_bytes();assert len(b)==e['size'] and hashlib.sha256(b).hexdigest()==e['sha256']
 p=Parser();p.feed(b.decode());s='\n'.join(' '.join(l.split()) for l in ''.join(p.out).splitlines() if l.strip())+'\n';name=e['path'].replace('.html','.txt');b=s.encode();(P/name).write_bytes(b);out.append(dict(path=name,size=len(b),sha256=hashlib.sha256(b).hexdigest(),source=e['path']))
(P/'derivative-bindings.json').write_text(json.dumps(out,indent=2)+'\n');print(out)
