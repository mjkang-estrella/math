import pathlib,json,hashlib,re
from html.parser import HTMLParser
class Parser(HTMLParser):
 def __init__(self):super().__init__();self.parts=[];self.skip=0
 def handle_starttag(self,t,a):
  if t=='math':self.parts.append(dict(a).get('alttext',''));self.skip+=1
  elif t in ['script','style']:self.skip+=1
 def handle_endtag(self,t):
  if t in ['math','script','style']:self.skip-=1
  if t in ['p','div','section','h2','h3']:self.parts.append('\n')
 def handle_data(self,d):
  if not self.skip:self.parts.append(d)
D=pathlib.Path(__file__).resolve().parent;out=[]
for e in json.loads((D/'retrieval-bindings.json').read_text()):
 if 'path' not in e:continue
 b=(D/e['path']).read_bytes();assert len(b)==e['size'] and hashlib.sha256(b).hexdigest()==e['sha256']
 parser=Parser();parser.feed(b.decode());s=''.join(parser.parts);p=D/e['path'].replace('.html','.txt');p.write_text(s)
 out.append({'path':p.name,'size':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'parent_sha256':e['sha256']})
(D/'derivative-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
for e in out:
 s=(D/e['path']).read_text();print('\nSOURCE',e['path'])
 for m in re.finditer(r'(?i)conjecture',s):print(s[max(0,m.start()-150):m.start()+1300])
