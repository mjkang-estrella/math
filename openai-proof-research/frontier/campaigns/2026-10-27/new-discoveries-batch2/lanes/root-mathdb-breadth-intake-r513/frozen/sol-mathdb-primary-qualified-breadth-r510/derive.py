from html.parser import HTMLParser
import pathlib,json,hashlib
P=pathlib.Path(__file__).resolve().parent
class Text(HTMLParser):
 def __init__(self):super().__init__();self.a=[];self.math=0
 def handle_starttag(self,t,a):
  d=dict(a)
  if t=='math':self.math+=1;self.a.append(' $'+d.get('alttext','')+'$ ')
  if t in ['p','div','section','h1','h2','h3','h4','li','tr']:self.a.append('\n')
 def handle_endtag(self,t):
  if t=='math':self.math-=1
 def handle_data(self,s):
  if not self.math:self.a.append(s)
out=[]
for e in json.loads((P/'source-bindings.json').read_text()):
 if 'path' not in e:continue
 p=pathlib.Path(e['path']);b=p.read_bytes();assert len(b)==e['size'] and hashlib.sha256(b).hexdigest()==e['sha256']
 t=Text();t.feed(b.decode());s='\n'.join(' '.join(l.split()) for l in ''.join(t.a).splitlines() if l.strip());q=p.with_suffix('.txt');q.write_text(s);b=q.read_bytes();out.append({'path':str(q),'size':len(b),'sha256':hashlib.sha256(b).hexdigest(),'derived_from':e['sha256']})
(P/'derivative-bindings.json').write_text(json.dumps(out,indent=2)+'\n')
