import urllib.request,pathlib,json,datetime,hashlib,resource,os
resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3));resource.setrlimit(resource.RLIMIT_CPU,(80,80));os.sched_setaffinity(0,{0,1})
D=pathlib.Path(__file__).resolve().parent;(D/'sources').mkdir(exist_ok=True)
urls={
'HH2026':'https://eulersolve.org/papers/aim-analysis-0032/paper.pdf?v=378700605e70',
'Larson':'https://arxiv.org/pdf/2005.01853v2',
'Cross2026':'https://arxiv.org/pdf/2609.29449v1',
'Cross2025':'https://drops.dagstuhl.de/storage/00lipics/lipics-vol357-gd2025/LIPIcs.GD.2025.19/LIPIcs.GD.2025.19.pdf'}
for name,url in urls.items():
 receipt={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research source review'}),timeout=25) as f:
   b=f.read(12000000);receipt.update(status=f.status,final_url=f.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest());(D/'sources'/name).write_bytes(b)
 except Exception as e:receipt['error']=str(e)
 (D/'sources'/f'{name}.receipt.json').write_text(json.dumps(receipt,indent=2));print(name,receipt,flush=True)
