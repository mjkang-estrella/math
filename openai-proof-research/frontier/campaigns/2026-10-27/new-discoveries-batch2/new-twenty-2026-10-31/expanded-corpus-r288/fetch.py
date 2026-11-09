import os,resource,pathlib,json,urllib.request,time,hashlib,concurrent.futures,sys
resource.setrlimit(resource.RLIMIT_CPU,(120,120))
resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,)*2)
os.sched_setaffinity(0,set(sorted(os.sched_getaffinity(0))[:2]))
l=pathlib.Path(__file__).resolve().parent
def fetch(arg):
    k,u=arg.split('=',1); start=time.monotonic()
    r=dict(key=k,url=u,utc=time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()))
    try:
        with urllib.request.urlopen(u,timeout=22) as z:
            data=z.read(15000000);r.update(status=z.status,final_url=z.url)
        (l/'sources'/(k+'.body')).write_bytes(data)
        r.update(bytes=len(data),sha256=hashlib.sha256(data).hexdigest())
    except Exception as e:r.update(error=str(e),status=getattr(e,'code',None),bytes=0,sha256=None)
    r.update(wall_seconds=time.monotonic()-start,depth='fetched, not automatically read')
    return r
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:rs=list(ex.map(fetch,sys.argv[1:]))
p=l/'http-receipts.json';p.write_text(json.dumps(json.loads(p.read_text())+rs,indent=2))
print(json.dumps(rs,indent=2))
with (l/'jobs.jsonl').open('a') as f:f.write(json.dumps(dict(script='fetch.py',reaped=True,rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,cpu_seconds=resource.getrusage(resource.RUSAGE_SELF).ru_utime,affinity=sorted(os.sched_getaffinity(0)),cpu_cap=120,wall_cap=140,as_cap=6*1024**3))+'\n')
