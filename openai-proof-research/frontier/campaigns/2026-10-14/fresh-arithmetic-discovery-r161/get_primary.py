from pathlib import Path
import urllib.request,hashlib,json,subprocess,concurrent.futures
r=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r161/packet/private/primary');r.mkdir(parents=True,exist_ok=True)
items=[('fujita-published','https://link.springer.com/content/pdf/10.1007/s40879-015-0045-5.pdf'),('bcdd','https://arxiv.org/pdf/math/0204314v1'),('bcdd-erratum','https://druel.perso.math.cnrs.fr/textes/mukai_erratum.pdf'),('occhetta','https://www.cambridge.org/core/services/aop-cambridge-core/content/view/780A467520AE4046D054AA8BFB5838A7/S0008439500004707a.pdf/div-class-title-a-characterization-of-products-of-projective-spaces-div.pdf')]
def get(item):
 name,url=item
 try:
  with urllib.request.urlopen(url,timeout=50) as f:b=f.read()
  assert b.startswith(b'%PDF'),b[:50]
  p=r/(name+'.pdf');p.write_bytes(b)
  subprocess.run(['pdftotext','-layout',str(p),str(r/(name+'.txt'))],check=True)
  return {'name':name,'url':url,'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest(),'ok':True}
 except Exception as e:return {'name':name,'url':url,'error':str(e),'ok':False}
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex: data=list(ex.map(get,items))
(r/'access.json').write_text(json.dumps(data,indent=2)+'\n');print(json.dumps(data,indent=2))
for name,_ in items:
 p=r/(name+'.txt')
 if p.exists():print(name,'text bytes',p.stat().st_size)
