from pathlib import Path
from html.parser import HTMLParser
import json,hashlib,urllib.request,datetime,subprocess
D=Path(__file__).resolve().parent
class H(HTMLParser):
 def __init__(self):super().__init__();self.t=[];self.skip=0
 def handle_starttag(self,t,a):
  if t in ['script','style']:self.skip+=1
 def handle_endtag(self,t):
  if t in ['script','style']:self.skip-=1
  if t in ['p','div','section','h1','h2','h3','li']:self.t.append('\n')
 def handle_data(self,x):
  if not self.skip:self.t.append(x)
pv=json.loads((D/'source-provenance.json').read_text());der=[]
for r in pv:
 if 'path' not in r:continue
 p=Path(r['path']);b=p.read_bytes();assert hashlib.sha256(b).hexdigest()==r['sha256']
 h=H();h.feed(b.decode());p=p.with_suffix('.txt');p.write_text(''.join(h.t));der.append({'path':str(p),'size':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'from':r['path']})
for name,url in {'gyarfas':'https://math.torontomu.ca/~pralat/papers/2024_Erdos_Gyarfas.pdf','christensen':'https://people.math.rochester.edu/faculty/doug/otherpapers/Christensen-Hovey.pdf'}.items():
 r={'name':name,'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=25) as f:b=f.read();r.update(final_url=f.url,status=f.status)
  p=D/(name+'.pdf');p.write_bytes(b);r.update(path=str(p),size=len(b),sha256=hashlib.sha256(b).hexdigest())
  # Bind PDF bytes on disk before invoking extractor.
  pv.append(r);(D/'source-provenance.json').write_text(json.dumps(pv,indent=2)+'\n')
  subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
  p=p.with_suffix('.txt');der.append({'path':str(p),'size':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'from':r['path']})
 except Exception as e:r['failure']=str(e);pv.append(r)
(D/'source-provenance.json').write_text(json.dumps(pv,indent=2)+'\n');(D/'derivative-bindings.json').write_text(json.dumps(der,indent=2)+'\n')
print(json.dumps(pv[-2:],indent=2))
