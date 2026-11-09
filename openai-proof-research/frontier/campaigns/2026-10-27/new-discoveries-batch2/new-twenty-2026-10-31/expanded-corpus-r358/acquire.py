import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,json,urllib.request,hashlib,datetime,time,concurrent.futures,sys
L=pathlib.Path(__file__).resolve().parent;t=time.monotonic()
def put(n,b):
 p=(L/n).resolve();assert p.is_relative_to(L);p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(b if isinstance(b,bytes) else b.encode())
def fetch(pair):
 name,url=pair;r={'url':url,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'method':'GET'}
 try:
  with urllib.request.urlopen(urllib.request.Request(url,headers={'User-Agent':'Research-source-reading/1.0'}),timeout=18) as f:
   b=f.read(16*1024**2);r.update(status=f.status,final_url=f.url,bytes=len(b),sha256=hashlib.sha256(b).hexdigest(),read_depth='acquired only');put('sources/'+name,b)
 except Exception as e:r.update(error=str(e),read_depth='access failure, no clearance')
 put('receipts/'+name+'.json',json.dumps(r,indent=2)+'\n');return r
r=json.loads((L/'reservation.json').read_bytes())
if sys.argv[1]=='primary': pairs=[(str(a['mathdb_id'])+'.pdf','https://arxiv.org/pdf/'+a['source_url'].rsplit('/',1)[1]) for a in r['rows']]
else:pairs=json.loads((L/sys.argv[1]).read_bytes())
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:
 for x in ex.map(fetch,pairs):print(json.dumps(x))
put('process-fetch-'+str(os.getpid())+'.json',json.dumps({'exit':0,'pid':os.getpid(),'elapsed':time.monotonic()-t,'threads_joined':True,'affinity':sorted(os.sched_getaffinity(0)),'self_maxrss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'scope':'self only, no concurrent group peak','cpu_limit':120,'as_limit':6*1024**3})+'\n')
