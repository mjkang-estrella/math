from html.parser import HTMLParser
from pathlib import Path
import json,hashlib
D=Path(__file__).parent
class P(HTMLParser):
 def __init__(self):super().__init__();self.out=[];self.skip=0
 def handle_starttag(self,t,a):
  if self.skip:self.skip+=1;return
  if t in ['math','script','style']:
   self.skip=1
   if t=='math':self.out.append(dict(a).get('alttext',''))
  elif t in ['p','div','section','h1','h2','h3','h4','li']:self.out.append('\n')
 def handle_endtag(self,t):
  if self.skip:self.skip-=1
 def handle_data(self,d):
  if not self.skip:self.out.append(d)
a=[]
for r in json.loads((D/'source-provenance.json').read_text()):
 if 'path' not in r:continue
 b=(D/r['path']).read_bytes();assert hashlib.sha256(b).hexdigest()==r['sha256'];p=P();p.feed(b.decode());o=D/r['path'].replace('.html','.txt');o.write_text(''.join(p.out));b=o.read_bytes();a.append({'path':o.name,'sha256':hashlib.sha256(b).hexdigest(),'size':len(b),'parent':r['sha256']})
(D/'derivative-bindings.json').write_text(json.dumps(a,indent=2)+'\n')
