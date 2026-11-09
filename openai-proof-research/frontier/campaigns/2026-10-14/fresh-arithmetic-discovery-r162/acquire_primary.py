from pathlib import Path
import urllib.request,hashlib,json,subprocess,concurrent.futures
r=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r162/packet/private/primary');r.mkdir(exist_ok=True)
items=[('okuma2004','https://ems.press/content/serial-article-files/43021'),('parusinski-v1','https://arxiv.org/pdf/alg-geom/9711014v1'),('king1980','https://link.springer.com/content/pdf/10.1007/BF01391660.pdf'),('timourian1977','https://www.jstor.org/stable/pdf/2373829.pdf')]
def get(it):
 n,u=it; rec=dict(name=n,url=u)
 try:
  with urllib.request.urlopen(u,timeout=40) as s: b=s.read();rec['final_url']=s.url
  assert b.startswith(b'%PDF'), 'response is not PDF'
  p=r/(n+'.pdf');p.write_bytes(b)
  rec.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
  subprocess.run(['pdftotext','-layout',str(p),str(r/(n+'.txt'))],check=True)
  rec['text_bytes']=(r/(n+'.txt')).stat().st_size
 except Exception as e: rec['error']=str(e)
 return rec
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex: a=list(ex.map(get,items))
(r/'access.json').write_text(json.dumps(a,indent=2)+'\n')
for x in a: print(x)
