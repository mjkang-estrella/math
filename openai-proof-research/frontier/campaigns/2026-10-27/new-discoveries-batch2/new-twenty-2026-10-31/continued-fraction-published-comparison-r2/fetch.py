import urllib.request,urllib.error,hashlib,json,datetime,sys,resource,os
from pathlib import Path
os.sched_setaffinity(0, sorted(os.sched_getaffinity(0))[:2]); resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3)); resource.setrlimit(resource.RLIMIT_CPU,(45,45))
o=Path(__file__).resolve().parent
for name,url in zip(sys.argv[1::2],sys.argv[2::2]):
 r={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':url,'file':name+'.body'}
 try:
  try: h=urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research-source-comparison/1.0'}),timeout=18)
  except urllib.error.HTTPError as e: h=e
  data=h.read(20*1024*1024+1); r.update(status=h.code,final_url=h.url,headers=dict(h.headers),sha256=hashlib.sha256(data).hexdigest(),bytes=len(data)); (o/r['file']).write_bytes(data)
 except Exception as e: r.update(status=None,error=str(e))
 with (o/'http-receipts.jsonl').open('a') as f: f.write(json.dumps(r)+'\n')
 print(json.dumps({k:v for k,v in r.items() if k!='headers'}))
