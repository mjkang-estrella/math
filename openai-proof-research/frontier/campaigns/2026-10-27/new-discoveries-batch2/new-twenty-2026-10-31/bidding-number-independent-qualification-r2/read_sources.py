import os,resource
os.sched_setaffinity(0, sorted(os.sched_getaffinity(0))[:2])
resource.setrlimit(resource.RLIMIT_CPU,(120,120)); resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import sys,json,hashlib,time,pathlib,subprocess
lane=pathlib.Path(__file__).resolve().parent
log=lane/'reads.jsonl'
for arg in sys.argv[1:]:
 p=pathlib.Path(arg).resolve(); assert 'crown' not in str(p) and 'tournament' not in str(p)
 b=p.read_bytes(); s=b.decode(); print('\nFILE '+str(p)+'\n'+s)
 rec={'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b),'utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),'depth':'full text emitted; cognitive depth specified in final inventory','exit':0,'self_maxrss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'caps_before_reads':True}
 old=log.read_text() if log.exists() else ''
 subprocess.run([sys.executable,'-I','-B',str(lane/'write_lane.py'),'reads.jsonl'],input=old+json.dumps(rec)+'\n',text=True,check=True,stdout=subprocess.DEVNULL)
