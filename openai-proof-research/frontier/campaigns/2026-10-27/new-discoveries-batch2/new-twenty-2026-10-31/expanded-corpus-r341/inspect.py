import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(30,30));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,json,re,hashlib,time
from html.parser import HTMLParser
L=pathlib.Path(__file__).resolve().parent;t=time.monotonic()
class P(HTMLParser):
 def __init__(self):super().__init__();self.out=[];self.math=0;self.skip=0
 def handle_starttag(self,tag,attrs):
  d=dict(attrs)
  if tag=='math':self.math+=1;self.out.append(' $'+d.get('alttext','')+'$ ')
  if tag in ['script','style']:self.skip+=1
  if tag in ['p','div','section','h1','h2','h3','h4','li','tr']:self.out.append('\n')
  if tag=='img' and d.get('alt'):self.out.append('[IMAGE ALT '+d['alt']+']')
 def handle_endtag(self,tag):
  if tag=='math':self.math-=1
  if tag in ['script','style']:self.skip-=1
 def handle_data(self,s):
  if not self.math and not self.skip:self.out.append(s)
inv=[]
for f in sorted((L/'sources').glob('*.html')):
 p=P();b=f.read_bytes();p.feed(b.decode());text=re.sub(r'[ \t\r\f\v]+',' ',''.join(p.out));text=re.sub('\n+','\n',text);o=L/'text'/ (f.stem+'.txt');o.parent.mkdir(exist_ok=True);o.write_text(text)
 inv.append({'file':str(f.relative_to(L)),'sha256':hashlib.sha256(b).hexdigest(),'text':str(o.relative_to(L)),'depth':'parsed; acquisition is not body review'})
 if '-html' in f.stem:
  print('\nID',f.stem)
  hits=list(re.finditer('conjectur',text,re.I))
  for m in hits[:5]:print(text[max(0,m.start()-160):m.start()+1250])
(L/'parsed-source-inventory.json').write_text(json.dumps(inv,indent=2)+'\n')
(L/'resource-inspect.json').write_text(json.dumps({'exit':0,'wall':time.monotonic()-t,'self':list(resource.getrusage(resource.RUSAGE_SELF))})+'\n')
