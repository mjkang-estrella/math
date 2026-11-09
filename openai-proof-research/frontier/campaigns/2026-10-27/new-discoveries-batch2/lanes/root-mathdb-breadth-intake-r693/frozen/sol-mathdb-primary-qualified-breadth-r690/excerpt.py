import pathlib,json,hashlib,re
from html.parser import HTMLParser
P=pathlib.Path(__file__).resolve().parent
class Parser(HTMLParser):
 def __init__(self):super().__init__();self.parts=[];self.math=0
 def handle_starttag(self,t,a):
  d=dict(a)
  if t=='math':self.math+=1;self.parts.append(' $'+d.get('alttext','')+'$ ')
  if t in ['p','div','h1','h2','h3','section']:self.parts.append('\n')
 def handle_endtag(self,t):
  if t=='math':self.math-=1
 def handle_data(self,d):
  if not self.math:self.parts.append(d)
for e in json.loads((P/'source-provenance.json').read_text()):
 if 'path' not in e:continue
 b=(P/e['path']).read_bytes();assert len(b)==e['size'] and hashlib.sha256(b).hexdigest()==e['sha256'];p=Parser();p.feed(b.decode());txt=re.sub('[ \t]+',' ',''.join(p.parts));path=P/(str(e['mathdb_id'])+'.txt');path.write_text(txt);entry={'path':path.name,'size':path.stat().st_size,'sha256':hashlib.sha256(path.read_bytes()).hexdigest()}
 with (P/'derivative-bindings.jsonl').open('a') as f:f.write(json.dumps(entry)+'\n')
 print(e['mathdb_id'],'candidate passage offsets',[(m.start(),txt[max(0,m.start()-65):m.start()+140]) for m in list(re.finditer('Conjecture|Payne|Bézout|Bezout',txt))[:25]])
