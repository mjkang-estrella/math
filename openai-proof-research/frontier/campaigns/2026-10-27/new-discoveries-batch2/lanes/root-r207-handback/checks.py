from fractions import Fraction as F
import json
out={'status':'PASS','finite_controls_only':True}
n=0
for q in range(2,100):
 for p in range(1,q):
  t=F(p,q);h=t/(1+2*t);phi=t/(2+t)
  assert h-phi==t*(1-t)/((1+2*t)*(2+t))>0
  assert 1/(1+2*t)**2<=h*(1-h)/t
  assert 0<h<F(1,3);n+=1
out['profile_controls']=n
for k in range(30):
 # exact infinite geometric tail; no truncated-series claim
 mass=F(3,4)*F(1,4)**k/(1-F(1,4));s=mass/2**k
 assert s==F(1,8)**k
out['geometric_tail_controls']=30
alloc=0
for p in range(1,101):
 # Source Step 5: all levels assigned to bin p have m<=p-1.
 assert sum(2**(m-1) for m in range(1,p))<2**(p-1)
 alloc+=1
out['gap_bin_controls']=alloc
print(json.dumps(out,indent=2))
