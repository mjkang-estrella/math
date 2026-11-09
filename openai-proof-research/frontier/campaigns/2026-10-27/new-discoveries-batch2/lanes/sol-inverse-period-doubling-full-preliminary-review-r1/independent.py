from pathlib import Path
import json,re
L=Path(__file__).resolve().parent
# Literal journal table, independent of candidate scripts.
T={1:(8,2),2:(3,4),3:(5,6),4:(3,2),5:(3,5),6:(8,7),7:(8,6),8:(8,8),'S':('S',2)}
F=[0,1]
for i in range(105):F.append(sum(F[-2:]))
N=2**19
u=bytearray(N);u[1]=1
for n in range(2,N):
 if n%4==1:u[n]=u[(n-1)//2-1]
 elif n%4==3:u[n]=u[n//4]
def accept(n):
 q=1
 for c in bin(n)[2:]:q=T[q][int(c)]
 return int(q in (2,6))
assert all(u[n]==accept(n) for n in range(N))
states=['S']
for i in range(19):states=[r for q in states for r in T[q]]
assert bytes(q in (2,6) for q in states)==u
H={q:([2] if T[q][1] in (2,6) else [1,1]) for q in T if q!=1}
z=[i for i,v in enumerate(u) if not v];a=[i for i,v in enumerate(u) if v]
g=[y-x for x,y in zip(z,z[1:])]
hh=[v for q in states[:N//2] for v in H[q]]
assert hh[:len(g)]==g
c=[n for n,v in enumerate(g) if v==2]
assert c==[v-j-1 for j,v in enumerate(a) if v-j-1<len(g)]
# Bottom-up suffix statistics without enumerating suffix languages.
D={q:(0,0,1) if q in (2,6) else None for q in T}
diag=[]
for t in range(1,101):
 p=2**(t-1);E={}
 for q,(l,r) in T.items():
  items=[D[l], None if D[r] is None else (p+D[r][0],p+D[r][1],D[r][2])]
  items=[v for v in items if v is not None]
  E[q]=None if not items else (items[0][0],items[-1][1],sum(v[2] for v in items))
 D=E;p*=2
 if t<3:continue
 if t%2:
  expected={'S':(1,p-1,F[t+1]),2:(5,p-3,F[t]-1),3:(1,p-1,F[t-1]+1),4:(5,p-1,F[t]),5:(5,p-3,F[t]-1),6:None,7:(p-1,p-1,1),8:None}
 else:
  expected={'S':(1,p-3,F[t+1]-1),2:(1,p-1,F[t]+1),3:(5,p//2-3,F[t-1]-1),4:(1,p-3,F[t]),5:(1,p-3,F[t]),6:(p-1,p-1,1),7:None,8:None}
 assert all(D[q]==v for q,v in expected.items()),t
 if t<=16:
  j=next(j for j in range(len(c)-1) if c[j+1]-c[j]>p)
  assert c[j]==5*p-2*F[t+2]-2
  assert j==2*F[t+2]-2
  assert a[j]==5*p-3 and a[j+1]==6*p+(-1 if t%2==0 else 1)
  diag.append({'t':t,'first_start':c[j],'rank':j,'a_start':a[j],'a_next':a[j+1],'c_gap':c[j+1]-c[j]})
out={'independent_u_recurrence_and_MSB_table_N':N,'H':H,'suffix_statistics_levels':100,'threshold_diagnostics':diag,'candidate_checker_used':False,'scope':'Finite diagnostics only; all-level induction and pumping reviewed in review.md'}
(L/'independent-result.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
