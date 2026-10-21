from pathlib import Path
import urllib.request,hashlib,json,subprocess,concurrent.futures
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r168/private/primary');R.mkdir(parents=True,exist_ok=True)
items=[('ls2017','https://ir.cwi.nl/pub/27485/27485.pdf'),('hls1999','https://ir.cwi.nl/pub/1257/1257D.pdf'),('cm2025v2','https://arxiv.org/pdf/2408.05338v2')]
def get(item):
 name,url=item
 try:
  b=urllib.request.urlopen(url,timeout=40).read();p=R/(name+'.pdf');p.write_bytes(b);assert b.startswith(b'%PDF')
  out=R/(name+'.txt');subprocess.run(['pdftotext','-layout',str(p),str(out)],check=True,capture_output=True)
  return {'name':name,'url':url,'pdf_sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b),'text_sha256':hashlib.sha256(out.read_bytes()).hexdigest(),'lines':len(out.read_text().split('\n'))}
 except Exception as e:return {'name':name,'url':url,'error':str(e)}
with concurrent.futures.ThreadPoolExecutor(max_workers=3) as pool:out=list(pool.map(get,items))
(R/'acquisition.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
