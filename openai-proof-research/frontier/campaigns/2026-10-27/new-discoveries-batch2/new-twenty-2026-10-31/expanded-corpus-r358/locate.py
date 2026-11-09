import os,resource
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(20,20));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import pathlib,re,json
L=pathlib.Path(__file__).resolve().parent
for p in sorted((L/'sources').glob('*.txt')):
 lines=p.read_text().splitlines();matches=[f'{i+1}: {s.strip()}' for i,s in enumerate(lines) if re.search(r'Conjecture|codegree decomposition|Proof of Theorem 1.3',s)]
 print(p.name,'; '.join(matches)[:2100])
