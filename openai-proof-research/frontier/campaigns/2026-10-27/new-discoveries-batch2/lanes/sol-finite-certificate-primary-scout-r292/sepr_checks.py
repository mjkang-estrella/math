"""Exact deductions for the one permitted pivot; no universal result asserted."""
import itertools,json,pathlib
L=pathlib.Path(__file__).resolve().parent
P=[[1,1,0],[-1,-1,1],[0,1,0]]
Q=[[-1,1,-1],[-1,1,1],[-1,-1,0]]
M=[[0]*6 for _ in range(6)]
for i in range(3):
 for j in range(3):M[i][j]=P[i][j];M[i+3][j+3]=Q[i][j]
def terms(A,inds):
 result=[]
 for perm in itertools.permutations(inds):
  inv=sum(perm[i]>perm[j] for i in range(len(inds)) for j in range(i+1,len(inds)))
  sign=(-1)**inv
  for i,j in zip(inds,perm):sign*=A[i][j]
  if sign:result.append((sign,list(zip(inds,perm))))
 return result
def signs(A,inds):return {s for s,t in terms(A,inds)} or {0}
profile=[]
for k in range(1,7):
 fixed={-1:[],0:[],1:[]};amb=[]
 for inds in itertools.combinations(range(6),k):
  ss=signs(M,inds)
  if len(ss)==1:fixed[next(iter(ss))].append(inds)
  else:amb.append(inds)
 satisfies=not amb or all(fixed[s] for s in [-1,0,1])
 assert satisfies
 profile.append(dict(k=k,ambiguous=amb,fixed=fixed,criterion_holds=bool(satisfies)))
# Shared monomials in 3-minors explicitly obstruct treating minors as independent knobs.
N=[[1]*4 for _ in range(4)]
t123=terms(N,(0,1,2));t124=terms(N,(0,1,3))
edge=(0,1)
assert any(edge in t for s,t in t123) and any(edge in t for s,t in t124)
result=dict(direct_sum_source='1807.04874v1 Example3.1; published masking is not a new counterexample',profile=profile,shared_entry={'edge':edge,'minor123_terms':[t for s,t in t123 if edge in t],'minor124_terms':[t for s,t in t124 if edge in t]},conclusion='Neither mechanism proves or refutes Conjecture3.8; see pivot-sepr.md')
(L/'sepr-result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
