import os,resource,pathlib,json,urllib.request,hashlib,datetime,subprocess
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(40,40));resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3))
p=pathlib.Path(__file__).resolve().parent;(p/'sources').mkdir(exist_ok=True);receipts=[]
urls={'registry-head.json':'https://api.github.com/repos/openai/math/commits/HEAD','arcs.pdf':'https://arxiv.org/pdf/1807.00588','queens.pdf':'https://arxiv.org/pdf/1807.04741','edgecolor.pdf':'https://arxiv.org/pdf/1807.06556','tidy.pdf':'https://arxiv.org/pdf/1806.10120'}
for name,url in urls.items():
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(url,timeout=20) as q:data=q.read();r.update(status=q.status,final_url=q.url)
  (p/'sources'/name).write_bytes(data);r.update(path=name,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
  if name.endswith('.pdf'):subprocess.run(['pdftotext','-layout',str(p/'sources'/name),str(p/'sources'/name.replace('.pdf','.txt'))],timeout=15,check=True)
 except Exception as e:r['error']=str(e)
 receipts.append(r);(p/'source-receipts.json').write_text(json.dumps(receipts,indent=2)+'\n');print(r,flush=True)
