import pathlib,json,hashlib
from html.parser import HTMLParser
class Parser(HTMLParser):
 def __init__(self):super().__init__();self.out=[];self.math=0;self.skip=0
 def handle_starttag(self,t,a):
  if t in ['script','style']:self.skip+=1
  if t=='math':self.math+=1;self.out.append(dict(a).get('alttext','[math]'))
  if t in ['p','div','section','h1','h2','h3','h4','li']:self.out.append('\n')
 def handle_endtag(self,t):
  if t=='math':self.math-=1
  if t in ['script','style']:self.skip-=1
 def handle_data(self,d):
  if not self.math and not self.skip:self.out.append(d)
P=pathlib.Path(__file__).resolve().parent;out=[]
for e in json.loads((P/'source-provenance.json').read_text())+json.loads((P/'closest-provenance.json').read_text()):
 if 'path' not in e:continue
 p=pathlib.Path(e['path']);b=p.read_bytes();assert len(b)==e['size'] and hashlib.sha256(b).hexdigest()==e['sha256']
 s=Parser();s.feed(b.decode());t='\n'.join(' '.join(x.split()) for x in ''.join(s.out).splitlines() if x.strip());p=p.with_suffix('.txt');p.write_text(t+'\n');b=p.read_bytes();out.append({'path':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest(),'derived_from':e['sha256']})
(P/'derivative-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
