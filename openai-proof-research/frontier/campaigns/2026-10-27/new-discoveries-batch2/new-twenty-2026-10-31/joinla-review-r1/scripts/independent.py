"""Independent complete necessary-condition screen, not a label-permutation solver.
Completeness justification is supplied in REVIEW.md. No discovery code imported."""
import json,pathlib
root=pathlib.Path(__file__).resolve().parents[1]
out=[]
for n,m in [(3,2),(3,3),(5,2)]:
 q=2*n*(1+2*m); T=q*(q+1)//2
 lo=lambda k:k*(k+1)//2
 hi=lambda k:k*(2*q-k+1)//2
 # same-null case: enumerate the entire possible null and endpoint weights.
 same=[]
 for X in range(lo(2*n),hi(2*n)+1):
  M=T-2*m*X
  if not(lo(2*n)<=M<=hi(2*n)) or M%2: continue
  for Y in range(lo(m+1),hi(m+1)+1):
   rem=T-m*X-n*Y
   if rem%n: continue
   Z=rem//n
   if Y<Z and X not in (Y,Z) and lo(m+1)<=Z<=hi(m+1):
    same.append([X,Y,Z,M])
 # mixed case: X,Y each occurs at both null and endpoint vertices.
 lower=max(lo(2*n),lo(m+1)); upper=min(hi(2*n),hi(m+1))
 mixed=[]
 for X in range(lower,upper+1):
  for Y in range(X+1,upper+1):
   rem=2*T-(2*n+m)*(X+Y)
   if rem%(2*n): continue
   Z=rem//(2*n)
   if Z in (X,Y) or not(lo(m+1)<=Z<=hi(m+1)): continue
   M=T-m*(X+Y); Q=2*n*Z-M
   if lo(2*n)<=M<=hi(2*n) and lo(2*n*m)<=Q<=hi(2*n*m):
    mixed.append([X,Y,Z,M,Q])
 out.append(dict(n=n,m=m,edges=q,total=T,same_survivors=len(same),mixed_survivors=len(mixed),
                 examples=[same[:3],mixed[:3]],decision='NO <=3 labelling' if not same and not mixed else 'UNDECIDED by necessary conditions'))
assert out[0]['same_survivors']==out[0]['mixed_survivors']==0
# Independently inspect emitted metadata rather than trusting the audit's success message.
rows=[x.split('\t') for x in (root/'outputs/audit.tsv').read_text().splitlines()]
local=[r for r in rows if r[1]=='Antimagic']
axioms=[r[0] for r in rows if r[2]=='axiom']
assert set(axioms)=={'propext','Classical.choice','Quot.sound'}
assert all(r[3:]==['false']*4 for r in local)
result=dict(cases=out,metadata=dict(total=len(rows),local=len(local),axioms=axioms))
(root/'outputs/independent.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
