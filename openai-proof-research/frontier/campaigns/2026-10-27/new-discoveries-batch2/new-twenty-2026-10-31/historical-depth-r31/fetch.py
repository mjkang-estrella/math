import pathlib,json,hashlib,datetime,urllib.request,urllib.error,resource,os,subprocess
resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3));resource.setrlimit(resource.RLIMIT_CPU,(100,100));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
L=pathlib.Path(__file__).resolve().parent;(L/'sources').mkdir(exist_ok=True)
jobs=[('registry-head.json','https://api.github.com/repos/openai/math/commits/main'),('fs.pdf','https://arxiv.org/pdf/math/0601012v3'),('roots.pdf','https://arxiv.org/pdf/2301.00660'),('fs-compute.pdf','https://schauenburg.perso.math.cnrs.fr/papers/CHFSIFCCIFG.pdf')]
receipts=[]
for name,url in jobs:
 rec={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'requested_url':url,'file':'sources/'+name}
 try:
  req=urllib.request.Request(url,headers={'User-Agent':'research-source-verification/1.0'})
  with urllib.request.urlopen(req,timeout=25) as f:
   rec.update(status=f.status,final_url=f.url,headers=dict(f.headers));data=f.read(20*1024**2+1);assert len(data)<=20*1024**2
  (L/rec['file']).write_bytes(data);rec.update(sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
  if name.endswith('.pdf'):
   cp=subprocess.run(['pdftotext','-layout',str(L/rec['file']),str(L/'sources'/name.replace('.pdf','.txt'))],capture_output=True,text=True,timeout=30);rec['extraction']={'returncode':cp.returncode,'stdout':cp.stdout,'stderr':cp.stderr};rec['text_sha256']=hashlib.sha256((L/'sources'/name.replace('.pdf','.txt')).read_bytes()).hexdigest()
 except Exception as e:rec['error']=str(e)
 receipts.append(rec);(L/'source-receipts.json').write_text(json.dumps(receipts,indent=2)+'\n');print(name,rec.get('status'),rec.get('error',rec.get('sha256')))
