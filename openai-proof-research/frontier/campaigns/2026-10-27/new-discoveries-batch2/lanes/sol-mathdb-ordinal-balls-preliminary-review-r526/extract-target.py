import pathlib,json,hashlib,subprocess
from html.parser import HTMLParser
D=pathlib.Path(__file__).resolve().parent
class Text(HTMLParser):
 def __init__(self):super().__init__();self.out=[];self.skip=0
 def handle_starttag(self,t,a):
  if t in ('script','style'):self.skip+=1
 def handle_endtag(self,t):
  if t in ('script','style'):self.skip-=1
 def handle_data(self,s):
  if not self.skip and s.strip():self.out.append(s.strip())
r=[]
for e in json.loads((D/'published-target-bindings.json').read_text()):
 if 'sha256' not in e:continue
 p=D/e['path'];assert hashlib.sha256(p.read_bytes()).hexdigest()==e['sha256']
 dest=D/'ordinal-published-body.txt'
 if p.suffix=='.pdf':subprocess.run(['pdftotext','-layout',str(p),str(dest)],check=True)
 else:
  h=Text();h.feed(p.read_text());dest.write_text('\n'.join(h.out)+'\n')
 b=dest.read_bytes();r.append(dict(path=dest.name,size=len(b),sha256=hashlib.sha256(b).hexdigest(),derived_from=e['sha256']))
(D/'published-target-extraction-bindings.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
