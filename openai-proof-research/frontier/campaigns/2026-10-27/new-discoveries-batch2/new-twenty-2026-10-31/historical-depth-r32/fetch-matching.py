import pathlib,requests,hashlib,json,datetime,resource,os
resource.setrlimit(resource.RLIMIT_AS,(1536*1024**2,1536*1024**2));resource.setrlimit(resource.RLIMIT_CPU,(90,90));os.sched_setaffinity(0,set(sorted(os.sched_getaffinity(0))[:2]))
p=pathlib.Path(__file__).parent/'sources';p.mkdir(exist_ok=True)
urls={'matching.pdf':'https://arxiv.org/pdf/2209.09661v1'}
for name,url in urls.items():
 r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  q=requests.get(url,timeout=25); data=q.content;(p/name).write_bytes(data);r.update(status=q.status_code,final_url=q.url,headers=dict(q.headers),sha256=hashlib.sha256(data).hexdigest(),bytes=len(data))
 except Exception as e:r['error']=str(e)
 (p/(name+'.receipt.json')).write_text(json.dumps(r,indent=2)+'\n');print(name,r.get('status'),r.get('sha256'),flush=True)
