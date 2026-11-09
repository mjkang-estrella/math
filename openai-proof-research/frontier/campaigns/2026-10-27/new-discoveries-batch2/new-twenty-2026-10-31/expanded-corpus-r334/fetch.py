import os,resource,time,json,pathlib,hashlib,urllib.request,urllib.error,sys,concurrent.futures,html,re
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
p=pathlib.Path(__file__).parent;start=time.monotonic()
class NoRedirect(urllib.request.HTTPRedirectHandler):
 def redirect_request(self,*a,**k):return None
op=urllib.request.build_opener(NoRedirect)
def get(item):
 name,url=item;rec={'url':url,'method':'GET','utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),'read_depth':'retrieved only'}
 try:
  with op.open(urllib.request.Request(url,headers={'User-Agent':'ResearchSourceReader/1.0'}),timeout=12) as r:b=r.read(20000000);rec.update(status=r.status,headers=dict(r.headers))
 except urllib.error.HTTPError as e:b=e.read(1000000);rec.update(status=e.code,error=str(e),headers=dict(e.headers))
 except Exception as e:b=b'';rec.update(status=None,error=str(e))
 rec.update(bytes=len(b),sha256=hashlib.sha256(b).hexdigest());(p/(name+'.bytes')).write_bytes(b);(p/(name+'.receipt.json')).write_text(json.dumps(rec,indent=2))
 if rec['status']==200 and b'<html' in b[:2000].lower():
  s=b.decode(errors='replace');s=re.sub(r'<(script|style)\b[^>]*>.*?</\1>','',s,flags=re.S);s=html.unescape(re.sub('<[^>]+>',' ',s));s=re.sub(r'[ \t]+',' ',s);(p/(name+'.txt')).write_text(s)
 print(name,rec['status'],len(b),flush=True)
with concurrent.futures.ThreadPoolExecutor(max_workers=2) as ex:list(ex.map(get,json.loads(sys.argv[1])))
(p/('resource-'+str(time.time_ns())+'.json')).write_text(json.dumps({'wall_seconds':time.monotonic()-start,'self_rusage':list(resource.getrusage(resource.RUSAGE_SELF)),'affinity':sorted(os.sched_getaffinity(0)),'CPU_limit':120,'AS_limit':6*1024**3,'group_RSS':'unavailable','exit':0}))
