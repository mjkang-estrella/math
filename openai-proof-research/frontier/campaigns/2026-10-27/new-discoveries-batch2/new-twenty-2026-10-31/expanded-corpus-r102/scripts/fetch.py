import pathlib,json,urllib.request,urllib.error,hashlib,datetime,concurrent.futures,resource,os
D=pathlib.Path(__file__).resolve().parents[1]
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,set(sorted(os.sched_getaffinity(0))[:2]))
def get(q):
 name,url=q; r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'math-research/1.0'}),timeout=22) as f:b=f.read();r.update(status=f.status,final_url=f.url,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b));(D/'sources'/name).write_bytes(b)
 except Exception as e:r.update(error=str(e),status=getattr(e,'code',None))
 (D/'receipts'/ (name+'.json')).write_text(json.dumps(r,indent=2));return name,r
if __name__=='__main__':
 rows=json.loads((D/'extracted.json').read_text())
 jobs=[(i+'.html',o['source_url'].replace('/abs/','/html/')) for i,o in rows.items()]
 jobs += [('openai-head.json','https://api.github.com/repos/openai/math/commits/HEAD'),('omega-head.json','https://api.github.com/repos/the-omega-institute/trureturing/commits/HEAD')]
 with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
  for name,r in ex.map(get,jobs): print(name,r,flush=True)
