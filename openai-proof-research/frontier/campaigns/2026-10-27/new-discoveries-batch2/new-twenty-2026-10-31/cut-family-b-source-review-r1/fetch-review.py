import urllib.request,json,datetime,hashlib,pathlib,resource,os,concurrent.futures
resource.setrlimit(resource.RLIMIT_AS,(768*1024**2,768*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(60,60));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
r=pathlib.Path(__file__).resolve().parent
urls={'openai-head':'https://api.github.com/repos/openai/math/commits/HEAD','omega-head':'https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD','ellis-abs':'https://arxiv.org/abs/2203.02457','published':'https://thotsaporn.com/PartitionGame.pdf','scinet-tree':'https://api.github.com/repos/scinet-ai/math-combinatorial-games/git/trees/HEAD?recursive=1'}
def fetch(item):
 name,url=item; rec={'name':name,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':url}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'public-source-review'}),timeout=18) as f:
   data=f.read(16*1024**2);rec.update(status=f.status,final_url=f.url,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data));(r/(name+'.body')).write_bytes(data)
 except Exception as e: rec['error']=str(e)
 return rec
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool: rows=list(pool.map(fetch,urls.items()))
(r/'http-receipts.json').write_text(json.dumps(rows,indent=2)+'\n');print(json.dumps(rows,indent=2))
