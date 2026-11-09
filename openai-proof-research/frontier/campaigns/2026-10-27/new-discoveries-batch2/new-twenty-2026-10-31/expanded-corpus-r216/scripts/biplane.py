from itertools import combinations
import sys
v=int(sys.argv[1]);D={7:{0,1,2,4},11:{1,3,4,5,9},37:{1,7,9,10,12,16,26,33,34}}[v];k=len(D);blocks=[{(x+t)%v for x in D} for t in range(v)]
assert all(len(A&B)==2 for A,B in combinations(blocks,2))
assert all(sum(x in B and y in B for B in blocks)==2 for x,y in combinations(range(v),2))
print('validated design',v,k,2,flush=True)
# Universal union bound: a chosen point set covers at most k+(a-1)(k-2) block vertices.
possible=[]
for a in range(k+1):
 b=k-a;cap_a=0 if not a else a*(k-2)+2;cap_b=0 if not b else b*(k-2)+2
 if v<=cap_a+b and v<=cap_b+a:possible.append((a,b))
print('possible splits of size k from exact union bound',possible,flush=True)
if not possible:print('known design plus elementary union bound refutes equality; zero-credit routine bridge');sys.exit(0)
# exact domination for the small cyclic designs
bm=[sum(1<<x for x in B) for B in blocks];full=(1<<v)-1
for total in range(1,k+2):
 tested=0;found=None
 for a in range(total+1):
  b=total-a
  for P in combinations(range(v),a):
   pm=sum(1<<x for x in P);forced=[i for i,B in enumerate(bm) if not pm&B]
   if len(forced)>b:continue
   optional=[i for i in range(v) if i not in forced]
   for extra in combinations(optional,b-len(forced)):
    tested+=1;chosen=forced+list(extra);cov=pm
    for i in chosen:cov|=bm[i]
    if cov==full:found=(P,chosen);break
   if found:break
  if found:break
 print('total',total,'candidate covers tested',tested,'witness',found,flush=True)
 if found:break
