import pathlib,json,urllib.request,datetime,hashlib,resource,os,sys
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
o=pathlib.Path(__file__).resolve().parent;s=o/'sources';s.mkdir(exist_ok=True);r=[]
for name,url in [x.split('=',1) for x in sys.argv[1:]]:
 t=datetime.datetime.now(datetime.timezone.utc).isoformat()
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'MathResearch/1.0'}),timeout=22) as f: data=f.read();status=f.status;final=f.url
  (s/name).write_bytes(data);d={'name':name,'url':url,'utc':t,'status':status,'final_url':final,'bytes':len(data),'sha256':hashlib.sha256(data).hexdigest()}
 except Exception as e:d={'name':name,'url':url,'utc':t,'error':str(e)}
 r.append(d);print(d,flush=True)
p=s/'receipts.jsonl'
with p.open('a') as f:
 for d in r:f.write(json.dumps(d)+'\n')
