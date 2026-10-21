from pathlib import Path
import urllib.request,hashlib,json,subprocess,concurrent.futures
R=Path('frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r132/private/primary')
items=[('xz-boundedness-v2','https://arxiv.org/pdf/2404.17134v2'),('liu-lci-v2','https://arxiv.org/pdf/2007.14320v2'),('xz-uniqueness-v1','https://arxiv.org/pdf/2005.08303v1'),('howald-v1','https://arxiv.org/pdf/math/0003232v1')]
def get(item):
 name,url=item
 try:
  response=urllib.request.urlopen(url,timeout=45);b=response.read();assert b.startswith(b'%PDF')
  p=R/(name+'.pdf');p.write_bytes(b)
  out=R/(name+'.txt');ret=subprocess.run(['pdftotext','-layout',str(p),str(out)],capture_output=True,text=True,timeout=30)
  rec=dict(name=name,url=url,final_url=response.url,size=len(b),sha256=hashlib.sha256(b).hexdigest(),extraction_returncode=ret.returncode,stderr=ret.stderr)
  if out.exists():rec.update(text_sha256=hashlib.sha256(out.read_bytes()).hexdigest(),pages=out.read_text().count('\f'))
  return rec
 except Exception as e:return dict(name=name,url=url,error=str(e))
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as ex: records=list(ex.map(get,items))
(R/'acquisition.json').write_text(json.dumps(records,indent=2)+'\n')
for x in records:print(json.dumps(x))
