from pathlib import Path
import requests,json,hashlib,datetime,sys,resource,os
R=Path(__file__).resolve().parents[1]
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6<<30,6<<30));os.environ['MALLOC_ARENA_MAX']='2'
for label,url in json.loads(sys.argv[1]):
 row={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat()}
 try:
  q=requests.get(url,timeout=15,headers={'User-Agent':'Public mathematical literature review (no authentication)'})
  data=q.content; (R/'downloads'/label).write_bytes(data)
  row.update(status=q.status_code,final_url=q.url,sha256=hashlib.sha256(data).hexdigest(),bytes=len(data),content_type=q.headers.get('Content-Type'))
 except requests.RequestException as e:row['error']=str(e)
 (R/'receipts'/(label+'.json')).write_text(json.dumps(row,indent=2)); print(label,row,flush=True)
