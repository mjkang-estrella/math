import itertools,json
from fractions import Fraction
# Two 2-minimal 6-vertex graphs obtained from K4 by proper 2-stretching.
def seed(A,B):
 E={(0,1),(0,2),(1,2),(3,4),(3,5)}
 E|={(i,4) for i in A};E|={(i,5) for i in B};return E
seeds=[seed([0],[1,2]),seed([0,1],[1,2])]
def rank(rows):
 # rank over F_1000003 gives a rigorous lower bound on rational rank; rank9 certifies facet.
 p=1000003;basis={}
 for rr in rows:
  a=list(rr)
  for j in range(9):
   if not a[j]:continue
   if j in basis:
    x=a[j];a=[(b-x*c)%p for b,c in zip(a,basis[j])]
   else:
    inv=pow(a[j],-1,p);basis[j]=[(b*inv)%p for b in a];break
 return len(basis)
out={'labeled_construction_instances':0,'distinct_labeled_graphs':0,'alpha3_allones_facet_candidates':0,'rank_not_computed':True};seen=set()
for E in seeds:
 for flags in itertools.product(range(4),repeat=6):
  # 0 absent; 1 A only; 2 B only; 3 both. Each stretched part nonempty and proper.
  S={i for i,f in enumerate(flags) if f};A={i for i,f in enumerate(flags) if f&1};B={i for i,f in enumerate(flags) if f&2}
  if not A or not B or A==S or B==S:continue
  F=E|{(6,7),(6,8)}|{(i,7) for i in A}|{(i,8) for i in B};out['labeled_construction_instances']+=1
  code=sum(1<<(v*(v-1)//2+u) for x,y in F for u,v in [sorted((x,y))])
  if code in seen:continue
  seen.add(code);out['distinct_labeled_graphs']+=1
  indeps=[];alpha=0
  for s in range(1<<9):
   if all(not(s>>u&1 and s>>v&1) for u,v in F):
    k=s.bit_count()
    if k>alpha:alpha=k;indeps=[]
    if k==alpha:indeps.append([(s>>i)&1 for i in range(9)])
  if alpha==3 and rank(indeps)==9:out['alpha3_allones_facet_candidates']+=1
open('outputs/three-minimal-screen.json','w').write(json.dumps(out,indent=2));print(out)
