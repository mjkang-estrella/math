import urllib.request,pathlib,json,datetime,hashlib,resource,os
resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3));resource.setrlimit(resource.RLIMIT_CPU,(80,80));os.sched_setaffinity(0,{0,1})
D=pathlib.Path(__file__).resolve().parent;(D/'sources').mkdir(exist_ok=True)
urls={
'openai-head':'https://api.github.com/repos/openai/math/commits/HEAD',
'workshop':'https://aimath.org/pastworkshops/shapesurfacerep.pdf',
'HH2018':'https://arxiv.org/pdf/1808.07794v2',
'BMV2004':'https://www.dmg.tuwien.ac.at/drmota/bmv.pdf',
'HHauthor':'https://faculty.washington.edu/steinerb/openproblems.pdf',
'Stahl':'https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/6780-11511_2013_Article_104.pdf'}
for name,url in urls.items():
 receipt={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source review'}),timeout=25) as f:
   b=f.read(12000000);receipt.update(status=f.status,final_url=f.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest());(D/'sources'/name).write_bytes(b)
 except Exception as e:receipt['error']=str(e)
 (D/'sources'/f'{name}.receipt.json').write_text(json.dumps(receipt,indent=2));print(name,receipt,flush=True)
