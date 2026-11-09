from pathlib import Path
import json,hashlib
from html.parser import HTMLParser
class Parser(HTMLParser):
 def __init__(self):super().__init__();self.parts=[];self.math=0
 def handle_starttag(self,tag,attrs):
  if tag=='math':self.math+=1;self.parts.append(dict(attrs).get('alttext',''))
 def handle_endtag(self,tag):
  if tag=='math':self.math-=1
 def handle_data(self,data):
  if not self.math:self.parts.append(data)
D=Path(__file__).resolve().parent;out=[]
for r in json.loads((D/'source-provenance.json').read_text()):
 if 'path' not in r:continue
 p=Path(r['path']);b=p.read_bytes();assert len(b)==r['size'] and hashlib.sha256(b).hexdigest()==r['sha256']
 s=Parser();s.feed(b.decode())

 t=' '.join(' '.join(s.parts).split());q=p.with_suffix('.txt');q.write_text(t)
 out.append(dict(path=str(q),sha256=hashlib.sha256(q.read_bytes()).hexdigest(),size=q.stat().st_size,source_sha256=r['sha256']))
(D/'derivative-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
print('bound derivatives',len(out))
