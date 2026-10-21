"""Exact finite support diagnostics, not a full pattern/host computation."""
from fractions import Fraction as Q
from itertools import combinations,product
from collections import Counter
import json

def geometry(faces):
 pairs=sorted({tuple(e) for f in faces for e in combinations(sorted(f),2)});corners=[(v,j) for j,f in enumerate(faces) for v in sorted(f)];ci={c:i for i,c in enumerate(corners)}
 U={e:sum(1<<ci[v,j] for j,f in enumerate(faces) if set(e)<=set(f) for v in e) for e in pairs}
 assert all(sum(set(e)<=set(f) for f in faces)==2 for e in pairs)
 M={};G={};L=[]
 for c in corners:
  v,j=c;e,f=[tuple(e) for e in combinations(sorted(faces[j]),2) if v in e]
  M[c]=U[e]|U[f];G[c]=U[e]^U[f];L.append((pairs.index(e),pairs.index(f)))
  assert M[c].bit_count()==7 and G[c].bit_count()==6 and M[c]^G[c]==1<<ci[c]
 assert set(Counter(x for e in L for x in e).values())=={4}
 return pairs,corners,U,M,G,L

def subs(mask):
 a=mask
 while a:yield a;a=(a-1)&mask

def moment(a,b,M,G,sgn=1):
 if (a|b)&~M:return Q(0)
 if a==b:return Q(1) if not a&~G else Q(1,2)
 return Q(sgn,4) if (a^b)==G and ((a|b)&~G) else Q(0)

# Direct branch averaging, independent of closed-form matrix entries.
checks=0
for sigma in [-1,1]:
 for a in range(1,128):
  for b in range(1,128):
   total=0
   for S,scale in [(127,1),(126,2)]:
    if (a|b)&~S:continue
    for minus in [0]+list(subs(S)):
     parity=(-1)**((minus&126).bit_count())
     wt=scale*(2+(sigma if S==127 else -sigma)*parity)
     total+=wt*((-1)**((minus&(a^b)).bit_count()))
   assert Q(total,512)==moment(a,b,127,126,sigma)
   checks+=1

faces=[tuple(f) for f in combinations(range(4),3)]
pairs,corners,U,M,G,L=geometry(faces);k=corners[0];m=len(corners)
# Enumerate full supported labelings of the connected six-vertex L, via sparse transitions.
labels=list(subs(M[k]));adj={a:[b for b in labels if moment(a,b,M[k],G[k],1)] for a in labels}
prev=[[] for _ in pairs]
for a,b in L:
 if a>b:a,b=b,a
 prev[b].append(a)

def direct_collapsed(sigma):
 assignment=[];total=Q(0);count=0
 def rec(i,val):
  nonlocal total,count
  if i==len(pairs):total+=val;count+=1;return
  choices=labels if not prev[i] else set.intersection(*(set(adj[assignment[j]]) for j in prev[i]))
  for a in choices:
   fac=Q(1)
   for j in prev[i]:fac*=moment(a,assignment[j],M[k],G[k],sigma)
   assignment.append(a);rec(i+1,val*fac);assignment.pop()
 rec(0,Q(1));return total,count
spin=Counter(sum(s[a]!=s[b] for a,b in L) for s in product([0,1],repeat=len(pairs)))
assert all(x%2==0 for x in spin)
predicted=63+Q(32,2**m)*sum(n*Q(1,2)**cut for cut,n in spin.items())
vals=[direct_collapsed(s) for s in [-1,1]];assert all(t==predicted for t,c in vals)
# Full local-face triangle contractions for each image-degeneracy type.
faceinfo={}
cs=[(v,0) for v in sorted(faces[0])]
for name,types in [('distinct',cs),('two_equal',[cs[0],cs[0],cs[1]]),('all_equal',[cs[0]]*3)]:
 A=[]
 for c in types:
  labs=list(subs(M[c]));A.append({a:{b:moment(a,b,M[c],G[c]) for b in labs if moment(a,b,M[c],G[c])} for a in labs})
 counts=Counter()
 for x,row in A[0].items():
  for y in row:
   for z in A[1].get(y,{}):
    if x in A[2].get(z,{}):
     flags=(x!=y,y!=z,z!=x);counts[''.join('1' if z else '0' for z in flags)]+=1
 allowed={'distinct':{'000','111'},'two_equal':{'000','110'},'all_equal':{'000','110','101','011'}}[name]
 assert set(counts)<=allowed
 faceinfo[name]=dict(counts)

torus=[]
vid=lambda x,y:(x%4)+4*(y%4)
for x,y in product(range(4),repeat=2):
 torus.extend([tuple(sorted([vid(x,y),vid(x+1,y),vid(x+1,y+1)])),tuple(sorted([vid(x,y),vid(x,y+1),vid(x+1,y+1)]))])
tp,tc,tU,tM,tG,tL=geometry(torus);degs=Counter(v for f in torus for v in f);assert set(degs.values())=={6}
finite=[]
for q in [3,5,7]:
 counts=Counter()
 for a,b,c in product(range(q),repeat=3):
  if (a*c-b*b)%q or (a,b,c)==(0,0,0):continue
  z=a if a else c;sgn=1 if pow(z,(q-1)//2,q)==1 else -1;counts[sgn]+=1
 assert counts[1]==counts[-1]==(q*q-1)//2
 for sg in [-1,1]:
  prob=Q(counts[sg],q**3)
  direct=sum((Q(1,1)/prob)**3 for _ in range(counts[sg]))/q**3
  assert direct==prob**-2
  lb=Q(1,q**(15*3))*prob**-64
  finite.append({'q':q,'sign':sg,'layer_count':counts[sg],'mass':str(prob),'torus_exact_collapse_lower_bound':str(lb),'greater_than_one':lb>1})
# Exponent identities, covering dimensions without computing full kernels.
exponents=[]
for D in [2,4,12,1642]:
 b=lambda x:x*(x+1)//2
 for v,f in [(13,22),(16,32),(4,4),(12,20)]:
  chi=v-f//2;E=2*f*b(D//2)-(v-1)*b(D)
  assert E==((1-chi)*D*D+(v-2*chi+1)*D)//2
  exponents.append({'D':D,'v':v,'f':f,'chi':chi,'exponent':E})
print(json.dumps({'moment_entry_checks':checks,'tetrahedral_collapsed':{'direct':str(vals[0][0]),'supported_labelings':vals[0][1],'spin_cut_counts':dict(spin),'formula':str(predicted),'same_for_both_signs':True},'local_face_patterns':faceinfo,'torus':{'points':16,'faces':len(torus),'pairs':len(tp),'corners':len(tc),'point_degree':6,'medial_degree':4},'finite_rank_checks':finite,'exponents':exponents,'limits':'Finite exact diagnostics. No enumeration of all type maps, no full torus density, no sign optimization, no theorem or contribution grade.'},indent=2))
