import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import sys,re,json
from pathlib import Path
P=Path(__file__).resolve().parent
name,term,size=sys.argv[1:4];t=(P/'sources'/name).read_text();size=int(size)
hits=list(re.finditer(re.escape(term),t))
print('HITS',len(hits))
for m in hits[:int(sys.argv[4]) if len(sys.argv)>4 else 3]:print(t[max(0,m.start()-300):m.start()+size])
