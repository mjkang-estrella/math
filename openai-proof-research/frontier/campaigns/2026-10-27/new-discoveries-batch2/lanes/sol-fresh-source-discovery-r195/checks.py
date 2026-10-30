from fractions import Fraction as Q
from math import factorial
import json
X=[(Q(-1),Q(1,2)),(Q(1),Q(1,2))]
Y=[(Q(-2),Q(1,8)),(Q(0),Q(3,4)),(Q(2),Q(1,8))]
def moment(A,j):return sum(w*x**j for x,w in A)
def call(A,j,t):return sum(w*max(x-t,0)**j for x,w in A)
assert all(moment(X,j)==moment(Y,j) for j in range(4))
count=0
for k in range(-400,401):
 t=Q(k,100);a=abs(t)
 expected=Q(0) if a>=2 else (2-a)**3/8 if a>=1 else (4-6*a*a+3*a**3)/8
 assert call(Y,3,t)-call(X,3,t)==expected>=0
 # Symmetry and equal quadratic moments give the crossing of quadratic transforms.
 assert call(Y,2,t)-call(X,2,t)==-(call(Y,2,-t)-call(X,2,-t))
 count+=1
assert call(X,2,Q(0))==call(Y,2,Q(0))==Q(1,2)
left=-2*call(X,1,Q(0));right=-2*call(Y,1,Q(0))
assert left==-1 and right==Q(-1,2)
escapes=[]
for p in range(2,10):
 for r in [2,4,16,256]:
  A=[(Q(0),1-Q(1,r**p)),(Q(r),Q(1,r**p))]
  assert moment(A,p)==1
  assert all(moment(A,j)==Q(1,r**(p-j)) for j in range(1,p))
  escapes.append([p,r])
print(json.dumps(dict(status='PASS',rational_transform_controls=count,moments_match_through=3,
 max_gluing_left_derivative=str(left),max_gluing_right_derivative=str(right),
 escape_controls=len(escapes),limits='Diagnostics only. Universal interpolation lemma and source conjecture NOT proved.'),indent=2))
