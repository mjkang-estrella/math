import pathlib,json,hashlib,resource,time,datetime,urllib.request,concurrent.futures,sys
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
L=pathlib.Path(__file__).resolve().parent;(L/'http').mkdir(exist_ok=True)
jobs=json.loads((L/sys.argv[1]).read_text());start=time.monotonic()
def fetch(j):
    name,url=j; now=datetime.datetime.now(datetime.timezone.utc).isoformat();r={'utc':now,'url':url,'name':name}
    try:
        with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'MathematicalResearch/1.0 public-source review'}),timeout=16) as f:
            b=f.read(16*1024**2);r.update(status=f.status,final_url=f.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest());(L/'http'/name).write_bytes(b)
    except Exception as e:r.update(error=str(e),status=getattr(e,'code',None))
    (L/'http'/(name+'.receipt.json')).write_text(json.dumps(r,indent=2)+'\n');return r
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
    for r in ex.map(fetch,jobs):print(json.dumps(r),flush=True)
print(json.dumps({'elapsed':time.monotonic()-start,'cpu':resource.getrusage(resource.RUSAGE_SELF).ru_utime,'maxrss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'script':str(pathlib.Path(__file__).resolve())}))
