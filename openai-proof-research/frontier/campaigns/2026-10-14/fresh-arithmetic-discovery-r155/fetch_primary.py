from pathlib import Path
import urllib.request,hashlib,json,subprocess,concurrent.futures
p=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r155/packet/private/primary'); p.mkdir(exist_ok=True)
items=[('fujino2004','https://ems.press/content/serial-article-files/40849'),('fujino-addendum','https://arxiv.org/pdf/math/0408095v1'),('ahk','https://arxiv.org/pdf/math/0605137v2')]
def run(it):
 n,url=it
 try:
  b=urllib.request.urlopen(url,timeout=45).read(); assert b.startswith(b'%PDF'); (p/(n+'.pdf')).write_bytes(b)
  q=subprocess.run(['pdftotext','-layout',str(p/(n+'.pdf')),str(p/(n+'.txt'))],capture_output=True,text=True,check=True)
  return {'name':n,'url':url,'size':len(b),'sha256':hashlib.sha256(b).hexdigest(),'text_size':(p/(n+'.txt')).stat().st_size,'stderr':q.stderr}
 except Exception as e:return {'name':n,'url':url,'error':str(e)}
with concurrent.futures.ThreadPoolExecutor(max_workers=3) as pool: r=list(pool.map(run,items))
(p/'access.json').write_text(json.dumps(r,indent=2)+'\n'); print(json.dumps(r,indent=2))
