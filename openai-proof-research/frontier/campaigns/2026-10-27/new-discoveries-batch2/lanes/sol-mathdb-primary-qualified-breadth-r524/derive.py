from pathlib import Path
import json,hashlib
from html.parser import HTMLParser
class Parser(HTMLParser):
 def __init__(self):super().__init__();self.parts=[];self.math=0
 def handle_starttag(self,t,a):
  if t=='math':self.parts.append(dict(a).get('alttext',''));self.math+=1
  elif t in ['p','div','section','h1','h2','h3','h4','li']:self.parts.append('\n')
 def handle_endtag(self,t):
  if t=='math':self.math-=1
 def handle_data(self,d):
  if not self.math:self.parts.append(d)
O=Path(__file__).resolve().parent;out=[]
for e in json.loads((O/'source-bindings.json').read_text()):
 if 'path' not in e:continue
 p=Path(e['path']);b=p.read_bytes();assert len(b)==e['size'] and hashlib.sha256(b).hexdigest()==e['sha256']
 s=Parser();s.feed(b.decode());p=p.with_suffix('.txt');p.write_text('\n'.join(x.strip() for x in ''.join(s.parts).splitlines() if x.strip()));b=p.read_bytes();out.append(dict(path=str(p),size=len(b),sha256=hashlib.sha256(b).hexdigest(),source=e['url']))
(O/'derivative-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
