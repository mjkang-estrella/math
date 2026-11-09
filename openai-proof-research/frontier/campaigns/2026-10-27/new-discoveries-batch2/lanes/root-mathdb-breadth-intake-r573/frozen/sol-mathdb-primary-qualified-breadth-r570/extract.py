from pathlib import Path
import json,hashlib
from html.parser import HTMLParser
class Parser(HTMLParser):
 def __init__(self):super().__init__();self.out=[];self.math=0;self.skip=0
 def handle_starttag(self,t,a):
  d=dict(a)
  if t in ('script','style'):self.skip+=1
  if t=='math':
   self.math+=1;self.out.append(' $'+d.get('alttext','MISSING_MATH')+'$ ')
 def handle_endtag(self,t):
  if t=='math':self.math-=1
  if t in ('script','style'):self.skip-=1
 def handle_data(self,d):
  if not self.math and not self.skip:self.out.append(d)
D=Path(__file__).resolve().parent
rows=json.loads((D/'source-provenance.json').read_text())
for r in rows:
 if 'path' not in r:continue
 b=Path(r['path']).read_bytes();assert hashlib.sha256(b).hexdigest()==r['sha256'] and len(b)==r['size']
 parser=Parser();parser.feed(b.decode());p=D/(r['label']+'.txt');p.write_text(''.join(parser.out));t=p.read_bytes();r['derivative']=dict(path=str(p),size=len(t),sha256=hashlib.sha256(t).hexdigest())
(D/'source-provenance.json').write_text(json.dumps(rows,indent=2)+'\n')
