import pathlib,urllib.request,urllib.error,json,hashlib,datetime,resource,os,sys
BASE=pathlib.Path(__file__).resolve().parents[1]
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
def fetch(url,name):
 p=BASE/'sources'/name;p.parent.mkdir(parents=True,exist_ok=True)
 if (BASE/'receipts'/ (name.replace('/','_')+'.json')).exists(): raise RuntimeError('Already attempted '+url)
 status='error'; data=b'';final=url
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'bounded-mathematical-literature-review'}),timeout=25) as f:status=f.status;data=f.read();final=f.url
 except Exception as e: status=str(e)
 if data:p.write_bytes(data)
 rec={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':url,'final_url':final,'status':status,'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest(),'path':str(p.relative_to(BASE))}
 (BASE/'receipts'/(name.replace('/','_')+'.json')).write_text(json.dumps(rec,indent=2)); print(name,status,len(data),flush=True)
 return json.loads(data) if data and name.endswith('.json') else data
if __name__=='__main__':
 for repo,n in [('openai/math','openai'),('the-omega-institute/trureturing','omega')]:
  h=fetch('https://api.github.com/repos/'+repo+'/commits/HEAD',n+'-head.json');sha=h['sha'];fetch('https://api.github.com/repos/'+repo+'/git/trees/'+sha,n+'-root.json')
