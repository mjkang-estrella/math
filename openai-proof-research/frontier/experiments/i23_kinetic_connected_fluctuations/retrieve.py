from pathlib import Path
import json,hashlib,datetime,urllib.request,subprocess,concurrent.futures
ROOT=Path(__file__).resolve().parents[3];S=ROOT/'frontier/sources/i23_kinetic_connected_fluctuations/literature';S.mkdir(exist_ok=True)
items=[('lebihan','2408.03597','v2'),('pss','1301.2514','v2'),('bgss','2008.10403','v2'),('cluster','2205.04110','v1'),('lebihan_hard','2212.04392',''),('bgss_equilibrium','220 equilibrium','')]
items=items[:-1]
def get(item):
 name,ar,ver=item;out=[]
 for kind,url in [('abs','https://arxiv.org/abs/'+ar),('pdf','https://arxiv.org/pdf/'+ar+ver)]:
  dst=S/(name+('.html' if kind=='abs' else '.pdf'))
  try:
   with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Mozilla/5.0'}),timeout=60) as r:b=r.read();status=r.status;resolved=r.url
   dst.write_bytes(b);out.append(dict(name=name,kind=kind,url=url,resolved=resolved,status=status,bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),file=str(dst.relative_to(ROOT)),retrieved=datetime.datetime.now(datetime.timezone.utc).isoformat()))
   if kind=='pdf' and b[:4]==b'%PDF':subprocess.run(['pdftotext','-layout',str(dst),str(dst.with_suffix('.txt'))],check=True)
  except Exception as e:out.append(dict(name=name,kind=kind,url=url,error=str(e)))
 return out
with concurrent.futures.ThreadPoolExecutor(max_workers=5) as ex:res=[x for r in ex.map(get,items) for x in r]
(S/'manifest.json').write_text(json.dumps(res,indent=2)+'\n');print(json.dumps(res,indent=2))
