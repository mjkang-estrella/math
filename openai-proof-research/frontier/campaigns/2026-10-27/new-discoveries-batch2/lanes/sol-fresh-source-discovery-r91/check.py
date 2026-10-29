import pathlib,json,math,itertools
L=pathlib.Path(__file__).resolve().parent

def add(*p):
 r=[0]*max(map(len,p))
 for v in p:
  for k,c in enumerate(v):r[k]+=c
 while len(r)>1 and not r[-1]:r.pop()
 return r
def shift(p,j=1):return [0]*j+p
def mul(p,q):
 r=[0]*(len(p)+len(q)-1)
 for i,a in enumerate(p):
  for j,b in enumerate(q):r[i+j]+=a*b
 return r
def update(T,Q,C):return add(shift(T),Q,shift(Q),C,shift(C)),add(Q,shift(Q),shift(C)),add(shift(T),shift(T,2),C,shift(C))
def lc(p):return all(p[k]*p[k]>=p[k-1]*p[k+1] for k in range(1,len(p)-1))
def ulcfail(p):
 d=len(p)-1
 return next((k for k in range(1,d) if p[k]*p[k]*k*(d-k)<p[k-1]*p[k+1]*(k+1)*(d-k+1)),None)
T=[0,0,0,2,1];Q=[0,0,0,0,1];C=[0,0,0,2,2];count=0;fails=[];firstreal=None;states={};sync=[]
for n in range(4,501):
 V=add(T,Q,C);states[n]=V if n<=35 else None
 for name,p in [('T',T),('Q',Q),('C',C),('V',V)]:
  count+=max(0,len(p)-2);f=ulcfail(p)
  if f is not None:fails.append([n,name,f])
 if n<=35:
  for a,b in itertools.combinations([T,Q,C],2):
   for k in range(1,min(len(a),len(b))-1):
    # Standard synchronized log-concavity requires BOTH these bounds.
    for u in [a[k]*b[k]-a[k-1]*b[k+1],a[k]*b[k]-a[k+1]*b[k-1]]:
     if u<0 and not sync:sync=[n,k,u,a,b]
 # scalar recurrence starting at n4, independently compare next via matrix
 T1,Q1,C1=update(T,Q,C)
 if n>=5:
  # V_{n+1}=(2+3z)V_n +(z^3-z^2-3z-1)V_{n-1}
  rhs=add(mul(V,[2,3]),mul(prev,[-1,-3,-1,1]));assert rhs==add(T1,Q1,C1)
 prev=V;T,Q,C=T1,Q1,C1
# exact positive finite-sum formula through r20, derived by shifted Fibonacci GF
H0=[4,4];H1=[8,8,1];Hs=[H0,H1]
for j in range(2,21):Hs.append(add(Hs[-1],mul([1,1],Hs[-2])))
identities=0
for r in range(21):
 formula=[0]
 for j in range(r+1):formula=add(formula,[math.comb(r,j)*c for c in shift(mul([math.comb(r-j,k) for k in range(r-j+1)],Hs[j]),j+3)])
 assert formula==states[r+4],r;identities+=1
# Generic componentwise LC preservation fails even for common-support positive inputs.
ob=None
polys=[[a,b,c] for a in range(1,5) for b in range(1,9) for c in range(1,5) if b*b>=a*c]
for p in polys:
 for q in polys:
  for c in ([1],[1,1],[1,2,1]):
   out=update(p,q,c)
   if not lc(add(*out)):
    ob={'input':[p,q,c],'output':out,'sum':add(*out)};break
  if ob:break
 if ob:break
result={'n_range':[4,500],'ulc_inequalities':count,'ulc_failures':fails,'scalar_recurrence_comparisons':496,'positive_sum_formula_checks':identities,'first_pair_synchronization_failure':sync,'generic_componentwise_LC_obstruction':ob}
(L/'checks.json').write_text(json.dumps(result,indent=2));print(json.dumps(result,indent=2))
