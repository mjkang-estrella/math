import pathlib,urllib.request,json,hashlib,datetime,sys,resource,os,subprocess
D=pathlib.Path(__file__).resolve().parents[1];resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
name,url=sys.argv[1:];r={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'url':url}
try:
 with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'research/1.0'}),timeout=25) as f:data=f.read();r.update(status=f.status,final_url=f.url,headers=dict(f.headers))
 (D/'sources'/name).write_bytes(data);r['sha256']=hashlib.sha256(data).hexdigest()
 if name.endswith('.pdf'):subprocess.run(['pdftotext','-layout',str(D/'sources'/name),str(D/'sources'/name.replace('.pdf','.txt'))],timeout=20)
except Exception as e:r['error']=str(e)
(D/'sources'/(name+'.receipt.json')).write_text(json.dumps(r,indent=2));print(r.get('status'),r.get('error','OK'))
