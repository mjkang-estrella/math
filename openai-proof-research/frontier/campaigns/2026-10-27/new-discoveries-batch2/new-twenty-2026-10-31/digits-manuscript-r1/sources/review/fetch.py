import urllib.request,urllib.error,pathlib,datetime,hashlib,json,sys,os,resource
w=pathlib.Path(__file__).resolve().parent; d=w/'http';d.mkdir(exist_ok=True)
os.environ['MALLOC_ARENA_MAX']='2';os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120))
receipts=[]
for name,url in zip(sys.argv[1::2],sys.argv[2::2]):
 r={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':url,'file':name}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'IndependentMathReview/1.0'}),timeout=20) as f:
   b=f.read();r.update(status=f.status,sha256=hashlib.sha256(b).hexdigest(),final_url=f.url);(d/name).write_bytes(b)
 except Exception as e:r['error']=str(e)
 receipts.append(r);print(r,flush=True)
with (w/'http-receipts.jsonl').open('a') as f:
 for r in receipts:f.write(json.dumps(r)+'\n')
