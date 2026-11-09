from pathlib import Path
import json,hashlib,re
from html.parser import HTMLParser
P=Path(__file__).resolve().parent
class Parser(HTMLParser):
 def __init__(self):super().__init__();self.out=[];self.skip=0
 def handle_starttag(self,t,a):
  a=dict(a)
  if t=='math':self.out.append(' $'+a.get('alttext','')+'$ ');self.skip+=1
  if t in ['p','div','section','h1','h2','h3','li','tr']:self.out.append('\n')
 def handle_endtag(self,t):
  if t=='math':self.skip-=1
 def handle_data(self,d):
  if not self.skip:self.out.append(d)
rows=[]
for e in json.loads((P/'source-bindings.json').read_text()):
 p=Path(e['path']);b=p.read_bytes();assert len(b)==e['size'] and hashlib.sha256(b).hexdigest()==e['sha256']
 z=Parser();z.feed(b.decode());text='\n'.join(' '.join(s.split()) for s in ''.join(z.out).splitlines() if s.strip())+'\n'
 dest=p.with_suffix('.txt');dest.write_text(text);rows.append(dict(path=str(dest),size=dest.stat().st_size,sha256=hashlib.sha256(dest.read_bytes()).hexdigest(),parent_sha256=e['sha256']))
(P/'derivative-bindings.json').write_text(json.dumps(rows,indent=2)+'\n')
