import json,pathlib,math,fractions
P=pathlib.Path(__file__).parent
F=fractions.Fraction
def det(a):
 a=[[F(x) for x in r] for r in a];v=F(1)
 for i in range(len(a)):
  t=next((t for t in range(i,len(a)) if a[t][i]),None)
  if t is None:return 0
  if t!=i:a[i],a[t]=a[t],a[i];v=-v
  z=a[i][i];v*=z
  for t in range(i+1,len(a)):
   zt=a[t][i]/z
   for k in range(i,len(a)):a[t][k]-=zt*a[i][k]
 return v
def D(i,j,k):return det([[math.comb(i+j+r+s,i+r) for s in range(k)] for r in range(k)])
checks=0
for i in range(5):
 for j in range(6):
  for k in range(1,6):assert D(i,j,k)==D(i,k,j);checks+=1
tep=0
for n in range(7):
 for l in range(1,5):
  for x in range(-2,3):
   # One nonmonic polynomial per degree, lower terms nonzero.
   co=[t+2 for t in range(n+1)]
   val=sum((-1)**k*math.comb(n,k)*sum(c*(x-l*k)**t for t,c in enumerate(co)) for k in range(n+1))
   assert val==co[-1]*l**n*math.factorial(n);tep+=1
(P/'bounded-calculation.json').write_text(json.dumps({'executed':True,'pascal_exact_rational_determinant_comparisons':checks,'pascal_ranges':'0<=i<=4,0<=j<=5,1<=k<=5; empty determinant=1','tepper_integer_checks':tep,'tepper_ranges':'0<=n<=6,1<=l<=4,-2<=x<=2,P(t)=sum_(a=0)^n(a+2)t^a','conclusion':'Sanity checks only; no general proof or novelty clearance inferred. Both routes uncredited; Pascal proved in source, Tepper routine substitution.'},indent=2)+'\n')
print('PASS',checks,tep)
