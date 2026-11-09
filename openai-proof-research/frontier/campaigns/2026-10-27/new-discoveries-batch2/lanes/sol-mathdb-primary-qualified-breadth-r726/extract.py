from html.parser import HTMLParser
import pathlib,json,hashlib
P=pathlib.Path(__file__).parent
class Parse(HTMLParser):
 def __init__(self):super().__init__();self.out=[];self.skip=0
 def handle_starttag(self,t,a):
  if t in ['script','style']:self.skip+=1
  if t in ['p','div','section','h1','h2','h3','h4','table','tr']:self.out.append('\n')
 def handle_endtag(self,t):
  if t in ['script','style']:self.skip-=1
 def handle_data(self,d):
  if not self.skip:self.out.append(d)
bs=[]
for e in json.loads((P/'source-provenance.json').read_text()):
 if 'path' not in e:continue
 b=(P/e['path']).read_bytes();assert len(b)==e['size'] and hashlib.sha256(b).hexdigest()==e['sha256']
 h=Parse();h.feed(b.decode());text='\n'.join(s.strip() for s in ''.join(h.out).splitlines() if s.strip());p=P/e['path'].replace('.html','.txt');p.write_text(text);b=p.read_bytes();bs.append({'path':p.name,'size':len(b),'sha256':hashlib.sha256(b).hexdigest(),'parent':e['sha256']})
(P/'derivative-bindings.json').write_text(json.dumps(bs,indent=2)+'\n')
