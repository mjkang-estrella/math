import urllib.request,hashlib,json,datetime,pathlib,resource,subprocess
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(90,90))
p=pathlib.Path(__file__).resolve().parent;(p/'sources').mkdir(exist_ok=True)
urls={'omega-current':'https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD','iskander':'https://arxiv.org/pdf/2310.18798'}
for name,u in urls.items():
 rec={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':u,'name':name}
 try:
  with urllib.request.urlopen(urllib.request.Request(u,headers={'User-Agent':'research-source-check'}),timeout=35) as r:
   data=r.read();rec.update(status=r.status,final_url=r.url,sha256=hashlib.sha256(data).hexdigest());f=p/'sources'/(name+('.pdf' if data.startswith(b'%PDF') else '.json'));f.write_bytes(data)
   if data.startswith(b'%PDF'):subprocess.run(['pdftotext','-layout',str(f),str(f.with_suffix('.txt'))],timeout=20)
 except Exception as e:rec['error']=str(e)
 with (p/'receipts.jsonl').open('a') as f:f.write(json.dumps(rec)+'\n')
 print(rec,flush=True)
