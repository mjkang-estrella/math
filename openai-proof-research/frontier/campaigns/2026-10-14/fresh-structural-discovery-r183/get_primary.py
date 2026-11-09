from pathlib import Path
import urllib.request,hashlib,json,subprocess,concurrent.futures
r=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r183/private/primary');r.mkdir(exist_ok=True)
items=[('adk','https://users.uoa.gr/~pdodos/Publications/13-Unconditional.pdf'),('alat','https://arxiv.org/pdf/math/0312522v2'),('fgs','https://shelah.logic.at/files/181794/763.pdf'),('brech','https://www.ime.usp.br/~brech/publ/BrechSurveyB.pdf'),('ssr','https://londmathsoc.onlinelibrary.wiley.com/doi/pdf/10.1112/jlms/53.1.158')]
def get(it):
 n,u=it
 try:
  b=urllib.request.urlopen(u,timeout=35).read();assert b.startswith(b'%PDF'), 'not PDF'
  p=r/(n+'.pdf');p.write_bytes(b);subprocess.run(['pdftotext','-layout',str(p),str(r/(n+'.txt'))],check=True)
  return dict(name=n,url=u,bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),text_bytes=(r/(n+'.txt')).stat().st_size)
 except Exception as e:return dict(name=n,url=u,error=str(e))
with concurrent.futures.ThreadPoolExecutor(max_workers=5) as ex:out=list(ex.map(get,items))
(r/'access.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
