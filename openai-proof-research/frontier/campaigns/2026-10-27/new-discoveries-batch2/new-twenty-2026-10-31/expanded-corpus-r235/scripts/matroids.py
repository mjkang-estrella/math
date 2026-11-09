from pathlib import Path
import json,itertools,sys
D=Path(__file__).resolve().parents[1]
def antichains(n):
 masks=list(range(1<<n));comp=[sum(1<<y for y in masks if (x&y)==x or (x&y)==y) for x in masks]
 def rec(av,chosen):
  yield chosen
  while av:
   bit=av&-av;av-=bit;x=bit.bit_length()-1
   yield from rec(av&~comp[x],chosen+[x])
 yield from rec((1<<(1<<n))-1,[])
def mats(n):
 allm=list(range(1<<n));res=[];ideal_count=0
 for bases in antichains(n):
  if not bases:continue
  fam=sum(1<<x for x in allm if any(x&b==x for b in bases));ideal_count+=1
  if len(set(x.bit_count() for x in bases))>1:continue
  if any(not any((b&~a)>>e&1 and (a^(1<<i)|(1<<e)) in bases for e in range(n)) for a in bases for b in bases for i in range(n) if a>>i&1 and not b>>i&1):continue
  circuits=[x for x in allm if not fam>>x&1 and all(fam>>(x^(1<<e))&1 for e in range(n) if x>>e&1)]
  cyclic=[x for x in allm if all(any(c>>e&1 and c&x==c for c in circuits) for e in range(n) if x>>e&1)]
  res.append((fam,circuits,cyclic))
 return res,ideal_count
def val(n,X):
 dp=[-100]*(1<<n);dp[0]=0
 for u in range(1<<n):
  if dp[u]<0:continue
  for x in X:
   if x&~u:dp[u|x]=max(dp[u|x],dp[u]+1)
 return [min((f|u).bit_count()-l for u,l in enumerate(dp) if l>=0) for f in range(1<<n)]
def submod(v):
 return next(((a,b) for a in range(len(v)) for b in range(a+1,len(v)) if v[a]+v[b]<v[a|b]+v[a&b]),None)
out=[]
for n in range(1,6):
 M,ideals=mats(n);F={f for f,c,y in M};groups={}
 for f,c,y in M:
  for choose in range(1<<len(c)):
   X=sum(1<<x for j,x in enumerate(c) if choose>>j&1);groups[X]=groups.get(X,0)|f
 checks=unique=0
 for X,f in groups.items():
  if f not in F:continue
  unique+=1;v=val(n,[x for x in range(1<<n) if X>>x&1]);bad=submod(v);checks+=1
  if bad:out.append({'COUNTEREXAMPLE':n,'X':X,'f':f,'bad':bad,'v':v});print(out[-1],flush=True)
 row={'n':n,'nonempty_ideals':ideals,'matroids':len(M),'circuit_families':len(groups),'unique_maximal_families':unique,'non_submodular':len([x for x in out if x.get('COUNTEREXAMPLE')==n])};out.append(row);print(row,flush=True)
(D/'matroid-search.json').write_text(json.dumps(out,indent=2)+'\n')
