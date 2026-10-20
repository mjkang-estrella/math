from pathlib import Path
import urllib.request,hashlib,json,subprocess,datetime,concurrent.futures
r=Path(__file__).resolve().parents[1]; out=r/'private/primary';out.mkdir(exist_ok=True)
a=[('cadoret-pirutka','https://webusers.imj-prg.fr/~anna.cadoret/K2.pdf'),('jacobson-1937','https://www.math.uci.edu/~brusso/jacobson1937.pdf'),('izhboldin-2000','https://msp.org/gtm/2000/03/gtm-2000-03p.pdf')]
def f(t):
 name,url=t;o={'name':name,'requested_url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=45) as s:b=s.read();o['final_url']=s.url
  assert b.startswith(b'%PDF');p=out/(name+'.pdf');p.write_bytes(b);subprocess.run(['pdftotext','-layout',str(p),str(p.with_suffix('.txt'))],check=True)
  o.update(sha256=hashlib.sha256(b).hexdigest(),text_sha256=hashlib.sha256(p.with_suffix('.txt').read_bytes()).hexdigest(),bytes=len(b),status='acquired')
 except Exception as e:o.update(status='failure',error=str(e))
 return o
with concurrent.futures.ThreadPoolExecutor(max_workers=3) as e:res=list(e.map(f,a))
(out/'register.json').write_text(json.dumps(res,indent=2)+'\n');print(json.dumps(res,indent=2))
