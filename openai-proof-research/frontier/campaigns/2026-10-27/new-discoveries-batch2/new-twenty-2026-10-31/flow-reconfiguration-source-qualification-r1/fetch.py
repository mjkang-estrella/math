import pathlib,urllib.request,datetime,hashlib,json,resource,os,subprocess,time
P=pathlib.Path(__file__).resolve().parent
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
jobs=[('cranston-live.html','https://arxiv.org/abs/2606.24685'),('esperet-live.html','https://arxiv.org/abs/2512.17342'),('esperet-author.html','https://oc.g-scop.grenoble-inp.fr/esperet/publications/'),('li-author.html','https://lijiaao-dm-nk.com/'),('goel-abs.html','https://arxiv.org/abs/2610.40863'),('goel.pdf','https://arxiv.org/pdf/2610.40863v1')]
for name,url in jobs:
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'destination':str(P/name)}
 try:
  with urllib.request.urlopen(url,timeout=12) as f:
   b=f.read(8*1024**2); r.update(status=f.status,final_url=f.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()); (P/name).write_bytes(b)
 except Exception as e:r['error']=repr(e)
 with (P/'fetch-receipts.jsonl').open('a') as f:f.write(json.dumps(r)+'\n')
 print(name,r.get('status',r.get('error')),flush=True)
 if name.endswith('.pdf') and (P/name).exists():
  subprocess.run(['pdftotext','-layout',str(P/name),str(P/name.replace('.pdf','.txt'))],timeout=15,check=True)
