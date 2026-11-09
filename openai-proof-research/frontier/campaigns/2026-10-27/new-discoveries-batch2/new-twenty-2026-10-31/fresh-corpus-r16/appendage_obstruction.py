import os,resource
resource.setrlimit(resource.RLIMIT_AS,(3*1024**3,3*1024**3))
os.sched_setaffinity(0,{0,1})
import random,json
from pathlib import Path
r=random.Random(100336130);p=Path(__file__).resolve().parent
for it in range(100000):
 n=10;prob=.28;a=[[int(i!=j and r.random()<prob) if i<j else 0 for j in range(n)]for i in range(n)]
 for i in range(n):
  for j in range(i):a[i][j]=a[j][i]
 d=[[0 if i==j else 1 if a[i][j] else n+1 for j in range(n)]for i in range(n)]
 for k in range(n):
  for i in range(n):
   for j in range(n):d[i][j]=min(d[i][j],d[i][k]+d[k][j])
 if any(max(row)!=3 for row in d):continue
 for x in range(n):
  for y in range(x):
   if d[x][y]!=3:continue
   A=[v for v in range(n)if d[x][v]<=1];B=[v for v in range(n)if d[y][v]<=1]
   bad=[v for v in A if all(d[v][w]<3 for w in B)]
   if bad:
    out={'adjacency':a,'distances':d,'x':x,'y':y,'fixed_A':A,'fixed_B':B,'initial_vertices_without_cross_distance3':bad,'scope':'obstructs direct reuse of source Proposition5.2 initialization; not a counterexample to the conjecture'}
    (p/'appendage-greedy-obstruction.json').write_text(json.dumps(out,indent=2));print(json.dumps(out));raise SystemExit
print('none')
