from pathlib import Path
from html.parser import HTMLParser
import json,hashlib
D=Path(__file__).resolve().parent
class P(HTMLParser):
 def __init__(self):super().__init__();self.t=[];self.skip=0
 def handle_starttag(self,tag,attrs):
  if tag in ['script','style']:self.skip+=1
  if tag in ['p','div','section','h1','h2','h3','h4']:self.t.append('\n')
 def handle_endtag(self,tag):
  if tag in ['script','style']:self.skip-=1
 def handle_data(self,d):
  if not self.skip:self.t.append(d)
refs=[]
for e in json.loads((D/'fetch-provenance.json').read_text()):
 if 'failure' in e:continue
 f=D/e['path'];b=f.read_bytes();assert hashlib.sha256(b).hexdigest()==e['sha256'] and len(b)==e['size']
 p=P();p.feed(b.decode());t=''.join(p.t);out=f.with_suffix('.txt');out.write_text(t)
 refs.append({'path':out.name,'sha256':hashlib.sha256(out.read_bytes()).hexdigest(),'size':out.stat().st_size,'source':e['path']})
# Re-parse the verified cached HTML rather than losing math from its single-line derivative.
f=D.parent/'sol-mathdb-primary-qualified-breadth-r576/1503.05295.html'
p=P();p.feed(f.read_text());out=D/'1503.05295-selected-source.txt';out.write_text(''.join(p.t))
refs.append({'path':out.name,'sha256':hashlib.sha256(out.read_bytes()).hexdigest(),'size':out.stat().st_size,'source':str(f)})
(D/'derivative-bindings.json').write_text(json.dumps(refs,indent=2)+'\n')
print('DERIVATIVES BOUND',refs)
