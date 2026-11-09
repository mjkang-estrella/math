import pathlib,json,hashlib
from html.parser import HTMLParser
P=pathlib.Path(__file__).resolve().parent
class H(HTMLParser):
 def __init__(self):super().__init__();self.out=[];self.skip=0
 def handle_starttag(self,t,a):
  d=dict(a)
  if t in ['script','style','math']:
   if t=='math':self.out.append(' $'+d.get('alttext','')+'$ ')
   self.skip+=1
  if t in ['p','section','h1','h2','h3','h4','li']:self.out.append('\n')
 def handle_endtag(self,t):
  if t in ['script','style','math']:self.skip=max(0,self.skip-1)
 def handle_data(self,s):
  if not self.skip:self.out.append(s)
binds=[]
for e in json.loads((P/'source-provenance.json').read_text()):
 if 'file' not in e:continue
 b=(P/e['file']).read_bytes();assert hashlib.sha256(b).hexdigest()==e['sha256'];h=H();h.feed(b.decode());p=P/e['file'].replace('.html','.txt');p.write_text(''.join(h.out));b=p.read_bytes();binds.append({'path':p.name,'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)})
(P/'derivative-bindings.json').write_text(json.dumps(binds,indent=2)+'\n')
