import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(25,25));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import sys,pathlib,hashlib,json,time,subprocess,uuid
lane=pathlib.Path(__file__).resolve().parent
path=pathlib.Path(sys.argv[1]).resolve();data=path.read_bytes();lines=data.decode().splitlines();ranges=sys.argv[2:];selected=[]
for r in ranges:
 a,b=map(int,r.split(':'));selected+=list(range(a-1,min(b,len(lines))))
print('FILE',path,'TOTAL LINES',len(lines))
for i in sorted(set(selected)):print(str(i+1)+': '+lines[i])
r={'id':str(uuid.uuid4()),'path':str(path),'sha256':hashlib.sha256(data).hexdigest(),'bytes':len(data),'ranges':ranges,'depth':'selected lines emitted; not full source unless explicitly all lines','utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),'caps_before_reads':True,'self_highwater_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'rss_sampling':'none; self highwater only','exit_at_receipt':0}
p=subprocess.run([sys.executable,'-I','-B',str(lane/'write_lane.py'),'reads/'+r['id']+'.json'],input=json.dumps(r,indent=2),text=True,capture_output=True,timeout=15);assert p.returncode==0
