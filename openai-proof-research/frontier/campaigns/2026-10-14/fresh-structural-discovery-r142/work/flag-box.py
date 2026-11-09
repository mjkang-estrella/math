from itertools import product,combinations
from pathlib import Path
import runpy,json
R=Path(__file__).resolve().parents[1];rank=runpy.run_path(str(R/'work/flag-betti.py'),run_name='flaglib')['rank']
def ideals(box):
 E=list(product(*(range(a) for a in box)));out=[];n=len(box)
 # enumerate downsets recursively with predecessor condition, by total degree
 E.sort(key=lambda a:(sum(a),a))
 def walk(i,A):
  if i==len(E):out.append(frozenset(A));return
  u=E[i];walk(i+1,A)
  if all(tuple(u[j]-(j==k) for j in range(n)) in A for k in range(n) if u[k]):
   A.add(u);walk(i+1,A);A.remove(u)
 walk(0,set());return E,out
def lex(A,E):
 L=set()
 for d in range(max(map(sum,E))+1):
  row=sorted(u for u in E if sum(u)==d);L.update(row[:sum(sum(u)==d for u in A)])
 return frozenset(L)
def beta(D,box):
 n=len(box);out={}
 for a in product(*(range(x+1) for x in box)):
  bases=[]
  for p in range(n+1):
   bases.append([s for s in combinations(range(n),p) if tuple(a[i]-(i in s) for i in range(n)) in D])
  ranks=[0]
  for p in range(1,n+1):
   idx={s:i for i,s in enumerate(bases[p-1])};mat=[[0]*len(bases[p]) for _ in bases[p-1]]
   for c,s in enumerate(bases[p]):
    for q,i in enumerate(s):
     t=s[:q]+s[q+1:]
     if t in idx:mat[idx[t]][c]=(-1)**q
   ranks.append(rank(mat))
  ranks.append(0)
  for p in range(n+1):
   v=len(bases[p])-ranks[p]-ranks[p+1]
   if v:out[p,sum(a)]=out.get((p,sum(a)),0)+v
 return out
if __name__=='__main__':
 for box in [(2,3),(3,3),(2,2,3),(2,3,3)]:
  E,sets=ideals(box);cache={};found=None;checked=0
  for A in sets:
   for B in sets:
    if not B<=A:continue
    D=A-B;L=lex(A,E)-lex(B,E)
    for W in (D,L):
     if W not in cache:cache[W]=beta(W,box)
    a,b=cache[D],cache[L];checked+=1
    if any(v>b.get(k,0) for k,v in a.items()):
     found=dict(A=sorted(A),B=sorted(B),D=sorted(D),L=sorted(L),beta={str(k):v for k,v in a.items()},lex_beta={str(k):v for k,v in b.items()});break
   if found:break
  out=dict(box=box,sets=len(sets),checked=checked,field=1000003,found=found)
  print(json.dumps(out),flush=True);(R/('packet/private/flag-box-'+''.join(map(str,box))+'.json')).write_text(json.dumps(out,indent=2))
