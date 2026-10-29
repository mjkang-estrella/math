import pathlib,json
P=pathlib.Path(__file__).resolve().parent
n=0;odd=0
for s in range(3,301):
 L=2*s+1
 for p in [2,3,5,7,11,13,17,19,23,29,31]:
  E=[0]*p;O=[0]*p
  for u in range(-s,s+1):(O if u%2 else E)[u%p]+=1
  if p==2:
   # Direct x,y parity counts rather than the noninvertible rotation.
   C=[0]*4
   for x in range(-s,s+1):
    t=s-abs(x)
    for j in range(2):C[2*(x%2)+j]+=sum(y%2==j for y in range(-t,t+1))
   cap=4*min(C);assert cap<=2*s*s
  else:
   q,r=divmod(L,p)
   value=q*q//2 if q%2==0 else ((q*q+1)//2 if r==p-1 else (q*q-1)//2)
   actual=min(E[i]*E[j]+O[i]*O[j] for i in range(p) for j in range(p))
   assert actual==value,(s,p,q,r,actual,value)
   cap=p*p*value
   if r:assert cap<=2*s*s,(s,p,cap)
   else:assert cap==(L*L-p*p)//2
   odd+=1
  n+=1
(P/'fiber-checks.json').write_text(json.dumps({'s_range':[3,300],'primes':[2,3,5,7,11,13,17,19,23,29,31],'cases':n,'odd_formula_checks':odd,'status':'PASS; bounded evidence only'},indent=2))
print(n,odd)
