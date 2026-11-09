import random,itertools,json,sys
from pathlib import Path
rng=random.Random(106372231)
def iso(A,B):
 n=len(A);da=[sum(x) for x in A];db=[sum(x) for x in B]
 if sorted(da)!=sorted(db):return False
 choices=[[j for j in range(n) if db[j]==da[i]] for i in range(n)]
 order=sorted(range(n),key=lambda i:len(choices[i]));f={};used=set()
 def rec(k):
  if k==n:return True
  i=order[k]
  for j in choices[i]:
   if j not in used and all(A[i][u]==B[j][v] for u,v in f.items()):
    f[i]=j;used.add(j)
    if rec(k+1):return True
    del f[i];used.remove(j)
  return False
 return rec(0)
def delete(A,v):return [[a for j,a in enumerate(r) if j!=v] for i,r in enumerate(A) if i!=v]
def strong(A):
 n=len(A)
 for rev in [False,True]:
  seen={0};todo=[0]
  while todo:
   i=todo.pop()
   for j in range(n):
    if j not in seen and (A[j][i] if rev else A[i][j]):seen.add(j);todo.append(j)
  if len(seen)<n:return False
 return True
def check(A,robust=True):
 if robust and not strong(A):return False
 ds=[delete(A,i) for i in range(len(A))]
 if robust and not all(strong(B) for B in ds):return False
 return not any(iso(a,b) for i,a in enumerate(ds) for b in ds[:i])
def rand(n):
 A=[[0]*n for _ in range(n)]
 for i in range(n):
  for j in range(i):A[i][j]=rng.randrange(2);A[j][i]=1-A[i][j]
 return A
out={}
for n in range(6,18):
 for trial in range(100000):
  A=rand(n)
  if check(A):
   out[str(n)]={'trial':trial+1,'adjacency':A,'robust':True};break
 else:out[str(n)]={'failed_trials':100000}
 Path('outputs/tournaments.json').write_text(json.dumps(out,indent=2)+'\n');print(n,out[str(n)].get('trial','FAIL'),flush=True)
