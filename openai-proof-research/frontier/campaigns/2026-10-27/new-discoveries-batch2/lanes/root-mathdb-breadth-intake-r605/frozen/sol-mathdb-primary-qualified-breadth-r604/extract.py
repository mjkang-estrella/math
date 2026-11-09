import json,pathlib,hashlib
from html.parser import HTMLParser
D=pathlib.Path(__file__).parent
class Parser(HTMLParser):
 def __init__(self):super().__init__();self.parts=[];self.skip=0
 def handle_starttag(self,t,a):
  if t in ['script','style']:self.skip+=1
  if t in ['p','section','div','h1','h2','h3','h4','tr']:self.parts.append('\n')
 def handle_endtag(self,t):
  if t in ['script','style']:self.skip-=1
 def handle_data(self,s):
  if not self.skip:self.parts.append(s)
rows=[]
for e in json.loads((D/'source-provenance.json').read_text()):
 b=(D/e['path']).read_bytes();assert len(b)==e['size'] and hashlib.sha256(b).hexdigest()==e['sha256'];p=Parser();p.feed(b.decode());q=D/e['path'].replace('.html','.txt');q.write_text(''.join(p.parts));b=q.read_bytes();rows.append({'path':q.name,'size':len(b),'sha256':hashlib.sha256(b).hexdigest(),'parent':e['path']})
(D/'derivative-bindings.json').write_text(json.dumps(rows,indent=2)+'\n')
