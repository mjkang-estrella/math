from pathlib import Path
import json,hashlib
from html.parser import HTMLParser
class Parse(HTMLParser):
 def __init__(self):super().__init__();self.out=[];self.depth=0;self.skip=0
 def handle_starttag(self,t,a):
  if t=='math':self.depth+=1;self.out.append(' $'+dict(a).get('alttext','[MISSING MATH]')+'$ ')
  if t in ['script','style']:self.skip+=1
 def handle_endtag(self,t):
  if t=='math':self.depth-=1
  if t in ['script','style']:self.skip-=1
  if t in ['p','div','section','h1','h2','h3','h4','li']:self.out.append('\n')
 def handle_data(self,d):
  if not self.depth and not self.skip:self.out.append(d)
D=Path(__file__).resolve().parent;a=[]
for e in json.loads((D/'source-download-bindings.json').read_text()):
 if 'path' not in e:continue
 p=Path(e['path']);b=p.read_bytes();assert len(b)==e['size'] and hashlib.sha256(b).hexdigest()==e['sha256'];s=Parse();s.feed(b.decode());p=p.with_suffix('.txt');b=''.join(s.out).encode();p.write_bytes(b);a.append({'path':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
(D/'derivative-bindings.json').write_text(json.dumps(a,indent=2)+'\n')
