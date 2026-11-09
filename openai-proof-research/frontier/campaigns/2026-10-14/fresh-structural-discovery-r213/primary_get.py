from pathlib import Path
import urllib.request,json,hashlib,concurrent.futures,subprocess,datetime
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r213/private/primary');R.mkdir(exist_ok=True)
urls={
'AK2000':'https://projecteuclid.org/journals/acta-mathematica/volume-185/issue-1/Currents-in-metric-spaces/10.1007/BF02392711.pdf',
'Wenger2007v1':'https://arxiv.org/pdf/math/0508072v1',
'Wenger2005v1':'https://arxiv.org/pdf/math/0306089v1',
'Stadler2022v1':'https://arxiv.org/pdf/2212.07100v1',
'Schulze2020':'https://wrap.warwick.ac.uk/id/eprint/136928/1/WRAP-Optimal-isoperimetric-inequalities-Schulze-2020.pdf',
'GhomiSpruckv7':'https://arxiv.org/pdf/1908.09814v7',
'Sturm2003':'https://publish.illinois.edu/ymb/files/2020/04/Sturm-2003-Probability-measures-on-metric-spaces-of-nonpositi.pdf',
'BVfinal':'https://cvgmt.sns.it/media/doc/paper/2044/BVfunctionsfinal.pdf',
'NobiliViolov2':'https://arxiv.org/pdf/2409.14182v2',
'MaggiSynopsis':'https://web.ma.utexas.edu/users/maggi/Maggi_extract.pdf'}
def get(item):
 k,u=item;x={'id':k,'url':u,'access_utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  response=urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'Research read-only'}),timeout=35);b=response.read();x['resolved_url']=response.url
  assert b[:4]==b'%PDF',b[:80]
  p=R/(k+'.pdf');p.write_bytes(b)
  x.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest())
  subprocess.run(['pdftotext','-layout',str(p),str(R/(k+'.txt'))],check=True,timeout=25,stdout=subprocess.PIPE,stderr=subprocess.PIPE)
  t=(R/(k+'.txt')).read_text();x.update(extracted_pages=len(t.split('\f'))-1,extraction_bytes=len(t.encode()),semantic_read=False)
 except Exception as e:x['failure']=repr(e)
 return x
with concurrent.futures.ThreadPoolExecutor(max_workers=4) as pool:out=list(pool.map(get,urls.items()))
(R/'access.json').write_text(json.dumps(out,indent=2)+'\n')
for x in out:print(json.dumps(x))
