from html.parser import HTMLParser
import pathlib,json,hashlib
D=pathlib.Path(__file__).parent
class P(HTMLParser):
 def __init__(self):super().__init__();self.out=[];self.math=0
 def handle_starttag(self,t,a):
  a=dict(a)
  if t=='math':self.math+=1;self.out.append(' '+a.get('alttext','')+' ')
  if t in ['p','section','h1','h2','h3','h4','div','li']:self.out.append('\n')
 def handle_endtag(self,t):
  if t=='math':self.math-=1
 def handle_data(self,s):
  if not self.math:self.out.append(s)
logs=json.loads((D/'source-provenance.json').read_text());der=[]
for e in logs:
 if 'path' not in e:continue
 b=(D/e['path']).read_bytes();assert len(b)==e['size'] and hashlib.sha256(b).hexdigest()==e['sha256']
 p=P();p.feed(b.decode());out='\n'.join(' '.join(l.split()) for l in ''.join(p.out).splitlines() if l.strip());q=D/e['path'].replace('.html','.txt');q.write_text(out);b=q.read_bytes();der.append({'path':q.name,'sha256':hashlib.sha256(b).hexdigest(),'size':len(b),'parent_sha256':e['sha256']})
(D/'derivative-bindings.json').write_text(json.dumps(der,indent=2)+'\n')
print('HTML verified; text derivatives bound before reading')
