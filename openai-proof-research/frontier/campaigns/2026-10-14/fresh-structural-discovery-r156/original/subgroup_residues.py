"""Finite GL(3,2) diagnostic; standard library, no network and no bytecode imports."""
from itertools import product,combinations
from fractions import Fraction
from collections import Counter
import json
from pathlib import Path
OUT=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r156/private/gl32-residues-diagnostic.json')
def apply(a,v):
 x=0
 for i in range(3):
  if v>>i&1:x^=a[i]
 return x
M=[a for a in product(range(1,8),repeat=3) if len({apply(a,v) for v in range(8)})==8]
idx={a:i for i,a in enumerate(M)};one=idx[(1,2,4)]
mul=[[idx[tuple(apply(a,v) for v in b)] for b in M] for a in M]
inv=[next(j for j in range(168) if mul[i][j]==one and mul[j][i]==one) for i in range(168)]
conj=[[mul[mul[g][h]][inv[g]] for h in range(168)] for g in range(168)]
def norm(H,g):return all(conj[g][h] in H for h in H)
# Enumerate by all index-two extensions, enough for EVERY finite 2-subgroup.
sub={frozenset([one])};todo=list(sub)
while todo:
 H=todo.pop()
 if len(H)==8:continue
 for g in range(168):
  if g not in H and mul[g][g] in H and norm(H,g):
   K=H|frozenset(mul[g][h] for h in H)
   assert len(K)==2*len(H)
   if K not in sub:sub.add(K);todo.append(K)
S=sorted((H for H in sub if len(H)>1),key=lambda h:(len(h),tuple(sorted(h))))
A=[H for H in S if all(mul[h][h]==one for h in H)]
B=[];normalizers={};cores={}
for H in S:
 N=frozenset(g for g in range(168) if norm(H,g));normalizers[H]=N
 Qs=[Q for Q in sub if Q<=N and all(norm(Q,g) for g in N)]
 core=max(Qs,key=len);assert all(Q<=core for Q in Qs)
 cores[H]=core
 if core==H:B.append(H)
I=[H for H in A if H in B]
def chains(V,less=lambda x,y:x<y):
 levels={-1:[()]};cur=[(x,) for x in V];d=0
 while cur:
  levels[d]=cur;cur=[c+(x,) for c in cur for x in V if less(c[-1],x)];d+=1
 return levels
def rank(columns):
 piv={}
 for col in columns:
  a={i:Fraction(x) for i,x in col.items() if x}
  while a:
   k=min(a)
   if k not in piv:
    v=a[k];piv[k]={i:x/v for i,x in a.items()};break
   v=a[k]
   for i,x in piv[k].items():
    a[i]=a.get(i,0)-v*x
    if not a[i]:a.pop(i,None)
 return len(piv)
def hom(V,less=lambda x,y:x<y):
 C=chains(V,less);R={-1:0};dims={d:len(c) for d,c in C.items()}
 for d in range(max(C)+1):
  loc={c:i for i,c in enumerate(C[d-1])}
  cols=[]
  for c in C[d]:
   a={}
   for j in range(d+1):a[loc[c[:j]+c[j+1:]]]=(-1)**j
   cols.append(a)
  R[d]=rank(cols)
 h={d:dims[d]-R.get(d,0)-R.get(d+1,0) for d in dims}
 return {'chain_dimensions':dims,'boundary_ranks':R,'reduced_betti':h}
result={'group_order':len(M),'subgroups_by_order':dict(Counter(map(len,S))), 'elementary_by_order':dict(Counter(map(len,A))), 'radical_by_order':dict(Counter(map(len,B))), 'intersection_by_order':dict(Counter(map(len,I))), 'Brown':hom(S),'Quillen':hom(A),'Bouc':hom(B),'intersection':hom(I)}
# Verify exact augmented link formula for every nonempty subgroup chain.
# Compute link as a join-poset of comparable vertices; its chains are the link.
allchains=[c for d,cs in chains(S).items() if d>=0 for c in cs]
checked=0
for c in allchains:
 V=[x for x in S if x not in c and all(x<y or y<x for y in c)]
 actual=hom(V)['reduced_betti']
 prev=frozenset([one]);ds=[];good=True
 for H in c:
  if not all(norm(prev,h) for h in H) or not all(mul[h][h] in prev for h in H):good=False
  ds.append((len(H)//len(prev)).bit_length()-1);prev=H
 U=[Q for Q in S if c[-1]<Q and Q<=normalizers[c[-1]]]
 upper=hom(U)['reduced_betti'];a=sum(ds);k=len(c)-1;mult=2**sum(d*(d-1)//2 for d in ds)
 expected={d+a-k-1:mult*v for d,v in upper.items() if v} if good else {}
 assert {d:v for d,v in actual.items() if v}==expected,(c,actual,expected)
 assert bool(expected)==(good and c[-1] in B)
 checked+=1
result['all_nonempty_chain_links_checked']=checked
# Standard incidence-poset replacement, already a classical fiber composition.
D=[(E,R) for E in A for R in B if E<=R]
le=lambda x,y:x!=y and x[0]<=y[0] and x[1]<=y[1]
result['incidence_pair_poset']={'vertices':len(D),**hom(D,le)}
# Independent Fano graph calculation.
lines=list(range(1,8));planes=sorted({frozenset([a,b,a^b]) for a,b in combinations(lines,2)})
fano_edges=[(l,p) for l in lines for p in planes if l in p]
result['fano_graph']={'vertices':len(lines)+len(planes),'edges':len(fano_edges),'cycle_rank':len(fano_edges)-len(lines)-len(planes)+1}
assert {d:v for d,v in result['Brown']['reduced_betti'].items() if v}=={1:8}
assert result['intersection']['reduced_betti'][0]==13
assert {d:v for d,v in result['incidence_pair_poset']['reduced_betti'].items() if v}=={1:8}
# Construct the rank-filtration Steinberg differential explicitly.
# Each rank2 E has three lines; reduced H0(E proper) basis [L]-[L0].
linegroups=[E for E in A if len(E)==2];loc={E:i for i,E in enumerate(linegroups)}
cols=[]
for E in A:
 if len(E)!=4:continue
 L=[x for x in linegroups if x<E]
 for x in L[1:]:cols.append({loc[x]:1,loc[L[0]]:-1})
result['Steinberg_chain_model']={'C1':len(cols),'C0':len(linegroups),'C_minus1':1,'rank_d1':rank(cols),'rank_d0':1,'H1':len(cols)-rank(cols),'H0':len(linegroups)-rank(cols)-1}
assert result['Steinberg_chain_model']=={'C1':28,'C0':21,'C_minus1':1,'rank_d1':20,'rank_d0':1,'H1':8,'H0':0}
# Full cycle space and all SAME-TOP residue evaluation ranks.
vertices=A; edges=[(x,y) for x in vertices for y in vertices if x<y];vloc={x:i for i,x in enumerate(vertices)}
piv={};basis=[]
for j,(x,y) in enumerate(edges):
 a={vloc[y]:Fraction(1),vloc[x]:Fraction(-1)};combo={j:Fraction(1)}
 while a:
  k=min(a)
  if k not in piv:
   v=a[k];piv[k]=({i:z/v for i,z in a.items()},{i:z/v for i,z in combo.items()});break
  row,rc=piv[k];v=a[k]
  for i,z in row.items():
   a[i]=a.get(i,0)-v*z
   if not a[i]:a.pop(i,None)
  for i,z in rc.items():
   combo[i]=combo.get(i,0)-v*z
   if not combo[i]:combo.pop(i,None)
 if not a:basis.append(combo)
assert len(basis)==8
ranks=[]
for E in I:
 edgeids=[j for j,(x,y) in enumerate(edges) if y==E]
 ranks.append(rank([{j:b.get(j,0) for j in edgeids} for b in basis]))
assert ranks==[2]*14
result['same_top_residue_ranks']={'cycle_dimension':8,'number_of_top_groups':14,'ranks':ranks,'sum_of_individual_ranks':sum(ranks),'joint_rank':rank(basis),'warning':'Individual surjections have shared domain and are not an independent direct sum.'}

OUT.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
