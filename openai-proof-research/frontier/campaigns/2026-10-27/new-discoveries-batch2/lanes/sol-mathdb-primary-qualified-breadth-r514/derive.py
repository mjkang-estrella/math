import json,pathlib,hashlib
from html.parser import HTMLParser
class Parser(HTMLParser):
 def __init__(self):super().__init__();self.out=[];self.math=0;self.skip=0
 def handle_starttag(self,t,a):
  d=dict(a)
  if t=='math':self.out.append(d.get('alttext',''));self.math+=1
  elif t in ['script','style']:self.skip+=1
  elif not self.math and t in ['p','div','section','h1','h2','h3','h4','li','tr']:self.out.append('\n')
 def handle_endtag(self,t):
  if t=='math':self.math-=1
  elif t in ['script','style']:self.skip-=1
  elif not self.math and t in ['p','div','section','h1','h2','h3','h4','li','tr']:self.out.append('\n')
 def handle_data(self,d):
  if not self.math and not self.skip:self.out.append(d)
P=pathlib.Path(__file__).resolve().parent;out=[]
for e in json.loads((P/'source-bindings.json').read_text()):
 if 'path' not in e:continue
 p=pathlib.Path(e['path']);b=p.read_bytes();assert len(b)==e['size'] and hashlib.sha256(b).hexdigest()==e['sha256']
 s=Parser();s.feed(b.decode());q=p.with_suffix('.txt');q.write_text('\n'.join(l.strip() for l in ''.join(s.out).splitlines() if l.strip()));bb=q.read_bytes();out.append(dict(path=str(q),size=len(bb),sha256=hashlib.sha256(bb).hexdigest(),derived_from=e['sha256']))
(P/'derivative-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
