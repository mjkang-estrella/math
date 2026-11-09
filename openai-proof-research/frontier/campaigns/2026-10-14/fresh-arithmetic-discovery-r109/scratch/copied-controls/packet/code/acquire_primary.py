from pathlib import Path
import urllib.request,hashlib,json,subprocess,concurrent.futures
R=Path('/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r109')
items=[('zero-generic-v2','https://arxiv.org/pdf/1303.5373v2'),('mermin-murai-v3','https://arxiv.org/pdf/0801.0391v3'),('caviglia-kummini-v2','https://arxiv.org/pdf/1210.5562v2'),('antieau-williams-v1','https://arxiv.org/pdf/1205.1279v1')]
def get(pair):
 name,url=pair
 try:
  with urllib.request.urlopen(url,timeout=45) as f:b=f.read(); final=f.url
  if not b.startswith(b'%PDF'):raise ValueError('not PDF')
  p=R/'private/primary'/f'{name}.pdf';p.write_bytes(b)
  t=p.with_suffix('.txt');subprocess.run(['pdftotext','-layout',str(p),str(t)],check=True)
  return {'name':name,'url':url,'final_url':final,'pdf':str(p.relative_to(R)),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest(),'text':str(t.relative_to(R)),'text_sha256':hashlib.sha256(t.read_bytes()).hexdigest()}
 except Exception as e:return {'name':name,'url':url,'failure':str(e)}
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:rs=list(pool.map(get,items))
(R/'private/primary/metadata.json').write_text(json.dumps(rs,indent=2)+'\n')
for r in rs:print(r['name'],r.get('bytes'),r.get('failure','success'))
