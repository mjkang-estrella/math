from pathlib import Path
import urllib.request,hashlib,json,concurrent.futures,subprocess
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r164')
items=[('liu-luo-2609.06867v2','https://arxiv.org/pdf/2609.06867v2'),('gu-xu-2610.01946v1','https://arxiv.org/pdf/2610.01946v1'),('delcourt-postle-2108.01633v5','https://arxiv.org/pdf/2108.01633v5'),('girao-narayanan-author-2020-05-02','https://sites.math.rutgers.edu/~narayanan/pdf/kappa_chi.pdf'),('xu-zhu-2110.00906v1','https://arxiv.org/pdf/2110.00906v1')]
def run(it):
 name,url=it
 try:
  req=urllib.request.Request(url,headers={'User-Agent':'mathematical-research/1.0'})
  with urllib.request.urlopen(req,timeout=40) as f:b=f.read();final=f.url
  assert b.startswith(b'%PDF'),b[:80]
  p=R/'private/primary'/(name+'.pdf');p.write_bytes(b)
  o=p.with_suffix('.txt');subprocess.run(['pdftotext','-layout',str(p),str(o)],check=True,timeout=25)
  return {'name':name,'requested_url':url,'resolved_url':final,'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest(),'text_sha256':hashlib.sha256(o.read_bytes()).hexdigest(),'text_lines':len(o.read_text().splitlines()),'read_status':'acquired; semantic read extents separate'}
 except Exception as ex:return {'name':name,'requested_url':url,'failure':str(ex)}
with concurrent.futures.ThreadPoolExecutor(max_workers=3) as ex:rows=list(ex.map(run,items))
(R/'private/primary/acquisition.json').write_text(json.dumps(rows,indent=2)+'\n');print(json.dumps(rows,indent=2))
