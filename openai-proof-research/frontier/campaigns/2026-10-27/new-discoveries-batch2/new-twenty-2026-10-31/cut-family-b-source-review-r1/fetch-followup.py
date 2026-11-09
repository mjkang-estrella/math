import urllib.request,json,datetime,hashlib,pathlib,resource,os,concurrent.futures
resource.setrlimit(resource.RLIMIT_AS,(768*1024**2,768*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(60,60));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
r=pathlib.Path(__file__).resolve().parent
urls={'omega-update':'https://api.github.com/repos/the-omega-institute/trureturing/compare/e9b39e568e8e0b68788ec0f007bc0107069db513...9e440b1c5cc46060c48d9f6896736db2b2c7175e','family-a-history':'https://api.github.com/repos/the-omega-institute/trureturing/commits?path=D5/S0/Certificates/Games/EllisThanatipanondaCutFamilyA.lean&sha=9e440b1c5cc46060c48d9f6896736db2b2c7175e&per_page=20','family-a-problem':'https://raw.githubusercontent.com/the-omega-institute/trureturing/9e440b1c5cc46060c48d9f6896736db2b2c7175e/Problems/ellis-thanatipanonda-2022-cut-family-a-conjecture-1.md','scinet-readme':'https://raw.githubusercontent.com/scinet-ai/math-combinatorial-games/578c758dd37f51cd2957ac7853330a995c4d5be7/README.md'}
def fetch(item):
 name,url=item; rec={'name':name,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':url}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'public-source-review'}),timeout=18) as f:
   data=f.read(16*1024**2);rec.update(status=f.status,final_url=f.url,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data));(r/(name+'.body')).write_bytes(data)
 except Exception as e: rec['error']=str(e)
 return rec
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as pool: rows=list(pool.map(fetch,urls.items()))
(r/'http-receipts-followup.json').write_text(json.dumps(rows,indent=2)+'\n');print(json.dumps(rows,indent=2))
