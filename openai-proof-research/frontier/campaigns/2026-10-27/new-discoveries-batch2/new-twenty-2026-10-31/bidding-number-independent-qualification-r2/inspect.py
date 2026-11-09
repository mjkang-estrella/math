import os,resource
os.sched_setaffinity(0, sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import sys,pathlib,json,hashlib,time,subprocess,re
lane=pathlib.Path(__file__).resolve().parent
p=pathlib.Path(sys.argv[1]).resolve();assert 'crown' not in str(p) and 'tournament' not in str(p)
b=p.read_bytes();s=b.decode();lines=s.splitlines()
if sys.argv[2]=='find':
 for i,l in enumerate(lines):
  if re.search(sys.argv[3],l,re.I):print(str(i+1)+': '+l[:900])
else:
 for r in sys.argv[2:]:
  a,z=map(int,r.split(':'));print('\n'.join(str(i+1)+': '+lines[i] for i in range(a-1,min(z,len(lines)))))
rec={'path':str(p),'sha256':hashlib.sha256(b).hexdigest(),'bytes':len(b),'selection':sys.argv[2:],'utc':time.strftime('%Y-%m-%dT%H:%M:%SZ',time.gmtime()),'exit':0,'self_maxrss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss,'caps_before_reads':True}
log=lane/'reads.jsonl';old=log.read_text() if log.exists() else '';subprocess.run([sys.executable,'-I','-B',str(lane/'write_lane.py'),'reads.jsonl'],input=old+json.dumps(rec)+'\n',text=True,check=True,stdout=subprocess.DEVNULL)
