import pathlib,json,hashlib
from html.parser import HTMLParser
class Parser(HTMLParser):
 def __init__(self):super().__init__();self.out=[];self.math=0
 def handle_starttag(self,tag,attrs):
  if tag=='math':self.out.append(' $'+dict(attrs).get('alttext','')+'$ ');self.math+=1
  elif tag in ['p','section','div','h1','h2','h3','h4','li']:self.out.append('\n')
 def handle_endtag(self,tag):
  if tag=='math':self.math-=1
 def handle_data(self,d):
  if not self.math:self.out.append(d)
P=pathlib.Path(__file__).resolve().parent;out=[]
for e in json.loads((P/'source-bindings.json').read_text()):
 if 'path' not in e:continue
 p=pathlib.Path(e['path']);b=p.read_bytes();assert len(b)==e['size'] and hashlib.sha256(b).hexdigest()==e['sha256']
 s=Parser();s.feed(b.decode());p=p.with_suffix('.txt');b=''.join(s.out).encode();p.write_bytes(b);out.append({'path':str(p),'size':len(b),'sha256':hashlib.sha256(b).hexdigest(),'source':e['url'],'derivation':'stdlib HTMLParser; math alttext, omit math children, block newlines'})
(P/'derivative-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
