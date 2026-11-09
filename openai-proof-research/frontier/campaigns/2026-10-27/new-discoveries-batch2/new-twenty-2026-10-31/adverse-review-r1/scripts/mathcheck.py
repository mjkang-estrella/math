from fractions import Fraction as F
from itertools import permutations,product
import json
from pathlib import Path
cells=list(product(range(6),repeat=2))
def adj(p,q):return p!=q and (p[0]==q[0] or p[1]==q[1] or sum(p)%6==sum(q)%6)
B=[[int((p[0],p[1],sum(p)%6)[t]==a) for p in cells] for t,a in product(range(3),range(6))]
assert all(sum(B[k][i]*B[k][j] for k in range(18))-3*(i==j)==adj(p,q) for i,p in enumerate(cells) for j,q in enumerate(cells))
def rref(M):
 M=[[F(x) for x in row] for row in M]; piv=[];r=0
 for j in range(len(M[0])):
  k=next((k for k in range(r,len(M)) if M[k][j]),None)
  if k is None:continue
  M[r],M[k]=M[k],M[r];v=M[r][j];M[r]=[x/v for x in M[r]]
  for k in range(len(M)):
   if k!=r:
    v=M[k][j];M[k]=[x-v*y for x,y in zip(M[k],M[r])]
  piv.append(j);r+=1
  if r==len(M):break
 return M,piv
# Average under permutations of (r,c,-r-c) and negation, stabilizing origin.
D=[i for i,p in enumerate(cells) if not adj((0,0),p)]
unseen=set(D);orbits=[]
while unseen:
 p=cells[min(unseen)];tr=(p[0],p[1],-sum(p)%6)
 orb={cells.index((sgn*q[0]%6,sgn*q[1]%6)) for q in permutations(tr) for sgn in [1,-1]}
 assert orb<=set(D);orbits.append(sorted(orb));unseen-=orb
M=[[sum(B[l][i] for i in orb) for orb in orbits]+[1] for l in range(18)]
rr,piv=rref(M);assert len(orbits) not in piv
w=[F(0)]*len(orbits)
for row,j in zip(rr,piv):w[j]=row[-1]
x=[F(0)]*36
for orb,v in zip(orbits,w):
 for i in orb:x[i]=v
assert min(x)>=0 and all(sum(a*b for a,b in zip(row,x))==1 for row in B)
rr,piv=rref([[row[i] for i in D] for row in B]);free=next(j for j in range(len(D)) if j not in piv)
z=[F(0)]*36;z[D[free]]=1
for row,j in zip(rr,piv):z[D[j]]=-row[free]
assert any(z) and all(sum(a*b for a,b in zip(row,z))==0 for row in B)
checks=[]
for a,b in cells:
 xx=[x[cells.index(((r-a)%6,(c-b)%6))] for r,c in cells]
 zz=[z[cells.index(((r-a)%6,(c-b)%6))] for r,c in cells]
 keep=[i for i,p in enumerate(cells) if not adj((a,b),p)]
 assert all(xx[i]==zz[i]==0 for i,p in enumerate(cells) if adj((a,b),p))
 assert min(xx)>=0 and sum(xx)==6 and any(zz)
 assert all(sum(row[i]*xx[i] for i in keep)==1 and sum(row[i]*zz[i] for i in keep)==0 for row in B)
 checks.append({'vertex':[a,b],'deletion_order':len(keep),'lambda_min':-3,'upsilon':6})
# Exact exhaustive test of every putative full transversal.
full=[q for q in permutations(range(6)) if len({(i+q[i])%6 for i in range(6)})==6]
assert not full
five=next([(i,q[i]) for i in range(5)] for q in permutations(range(6),5) if len({(i+q[i])%6 for i in range(5)})==5)
assert all(not adj(p,q) for p,q in permutations(five,2))
report={'own_code':True,'gram_identity':True,'degree':15,'nonadjacent_pair':[[0,0],[1,1]],'fractional_base':list(map(str,x)),'kernel_base':list(map(str,z)),'orbits':orbits,'orbit_weights':list(map(str,w)),'all_deletions':checks,'full_transversals':len(full),'permutations_tested':720,'independent_five':five,'alpha':5,'global_upsilon':6,'global_lambda_min':-3}
Path('receipts/math.json').write_text(json.dumps(report,indent=2));print(json.dumps(report,indent=2))
