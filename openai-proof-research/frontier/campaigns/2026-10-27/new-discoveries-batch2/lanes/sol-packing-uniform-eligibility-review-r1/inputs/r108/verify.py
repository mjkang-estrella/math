exec((__import__('pathlib').Path(__file__).parent/'check.py').read_text().split('# Exact source model')[0])
def closure(n,edges):
 a=[0]*n
 for x,y in edges:a[x]|=1<<y
 for k in range(n):
  for i in range(n):
   if a[i]>>k&1:a[i]|=a[k]
 assert all(not(a[i]>>i&1) for i in range(n))
 return a
cases=0
for m in range(3,8):
 for r in range(5):
  K=2*m+1+r;d=K-m;pi=tuple(range(1,m))+(K-1,)+tuple(range(m+1,K-m))+(K,m)+tuple(range(K-m,K-1))
  assert sorted(pi)==list(range(1,K+1))
  order=sorted(range(K),key=lambda i:pi[i])
  for j in range(1,9):
   n=K+(j-1)*d;edges=[(t*d+a,t*d+b) for t in range(j) for a,b in zip(order,order[1:])]
   low=[];H=[];Z=[]
   for t in range(j+1):
    low.append(t*d)
    if t>0:low.extend(range((t-1)*d+m,(t-1)*d+m+r))
    low.extend(t*d+i for i in range(1,m-1));H.append(t*d+m-1)
    if t<j:Z.append(t*d+m+r)
   assert sorted(low+H+Z)==list(range(n))
   spine=low+list(reversed(H));model=list(zip(spine,spine[1:]))+[(H[t],Z[t]) for t in range(j)]
   assert closure(n,edges)==closure(n,model)
   cases+=1
# A generic recurrence does not make five equal terms decisive.
# Two nonnegative integer weighted automata: delayed path length6 vs zero.
A=[[0]*7 for _ in range(7)]
for i in range(6):A[i][i+1]=1
v=[1]+[0]*6;s=[]
for n in range(8):
 s.append(v[6]);v=[sum(v[i]*A[i][k] for i in range(7)) for k in range(7)]
assert s==[0,0,0,0,0,0,1,0]
(L/'verification.json').write_text(json.dumps({'closure_identity_cases':cases,'m_range':[3,7],'r_range':[0,4],'j_range':[1,8],'generic_delayed_automaton':s,'automaton_is_source_counterexample':False,'full_proof':'PROOF.md','credit':0},indent=2));print(cases,s)
