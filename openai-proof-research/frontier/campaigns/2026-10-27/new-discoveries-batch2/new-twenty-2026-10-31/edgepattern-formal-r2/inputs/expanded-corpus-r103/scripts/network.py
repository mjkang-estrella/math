import numpy as np,itertools as it,json,random,time,warnings
from scipy.optimize import linprog
from pathlib import Path
warnings.filterwarnings('ignore',category=Warning)
D=Path(__file__).resolve().parents[1];rng=random.Random(103);counts={};bad=[]
def test(n,edges):
 E=len(edges);cuts={}
 for s in range(1,8):
  cuts[s]=[np.array([bool(mask>>a&1)!=bool(mask>>b&1) for a,b,c in edges],dtype=float) for z in range(1<<(n-4)) for mask in [(z<<4)|s]]
 S={s:min(sum(v[e]*edges[e][2] for e in range(E)) for v in cuts[s]) for s in cuts}
 S.update({s:S[15^s] for s in range(8,15)});S[0]=S[15]=0
 pairs=list(it.combinations(range(4),2));qs=[(S[1<<a]+S[1<<b]-S[(1<<a)|(1<<b)])/2 for a,b in pairs]
 q0=-(S[1]+S[2]+S[4]-S[3]-S[5]-S[6]+S[7])/2
 targets=[]
 for s in range(1,8):targets.append([q*(bool(s>>a&1)!=bool(s>>b&1)) for q,(a,b) in zip(qs,pairs)]+[q0*min(s.bit_count(),4-s.bit_count())])
 A=[];B=[]
 for s in range(1,8):
  assert abs(sum(targets[s-1])-S[s])<1e-8
  for k,t in enumerate(targets[s-1]):
   if t<=0:continue
   for cut in cuts[s]:
    v=np.zeros(7*E);v[k*E:(k+1)*E]=-cut;A.append(v);B.append(-t)
 eq=np.tile(np.eye(E),(1,7))
 r=linprog(np.zeros(E*7),A_ub=np.array(A) if A else None,b_ub=B if B else None,A_eq=eq,b_eq=[c for a,b,c in edges],bounds=(0,None),method='highs',options={'threads':1})
 if r.status!=0:return dict(n=n,edges=edges,S=S,qs=qs,q0=q0,status=r.status,message=r.message)
 return None
for n,trials in [(4,None),(5,None),(6,2000),(7,1000),(8,500)]:
 allpairs=list(it.combinations(range(n),2));ok=skip=0
 for k in range((1<<len(allpairs)) if trials is None else trials):
  if trials is None: edges=[(a,b,1) for j,(a,b) in enumerate(allpairs) if k>>j&1]
  else:edges=[(a,b,rng.randint(1,5)) for a,b in allpairs if rng.random()<.5]
  reach={0}
  for _ in range(n):reach|={b for a,b,c in edges if a in reach}|{a for a,b,c in edges if b in reach}
  if len(reach)!=n:skip+=1;continue
  r=test(n,edges);ok+=1
  if r:bad.append(r);print('FAIL',r,flush=True);break
 counts[n]=dict(tested=ok,disconnected_skipped=skip,trials=trials,exhaustive=trials is None)
 print('progress',n,counts[n],flush=True)
 (D/'outputs/network.json').write_text(json.dumps(dict(counts=counts,failures=bad,seed=103,limitation='Floating point LP feasibility; no exact certificate inferred; original cut constraints exact integers.'),indent=2)+'\n')
 if bad:break
