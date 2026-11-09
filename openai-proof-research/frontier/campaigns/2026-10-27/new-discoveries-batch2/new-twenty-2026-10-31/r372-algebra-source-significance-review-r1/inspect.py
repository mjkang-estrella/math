import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import sys,pathlib
sys.path.insert(0,str(pathlib.Path(__file__).resolve().parent))
import review_ops as r
import json,re,time
p=r.BASE/sys.argv[1]; s=r.read(p).decode(); lines=s.splitlines()
if len(sys.argv)==2: print(s)
elif sys.argv[2]=='find':
 for i,l in enumerate(lines):
  if re.search(sys.argv[3],l,re.I): print(i+1,l)
else:
 a,b=map(int,sys.argv[2:4]); print('\n'.join(f'{i+1}: {lines[i]}' for i in range(a-1,min(b,len(lines)))))
r.finish('inspect-'+str(time.time_ns()))
