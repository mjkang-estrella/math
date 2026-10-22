from fractions import Fraction as Q
import json
# Exact arithmetic controls for the displayed projective-model family and graph equations.
def sigma(v,w):
 return v[0]*w[2]+v[1]*w[3]-v[2]*w[0]-v[3]*w[1]
v0=(1,0,0,0);v1=(0,0,1,0);u=(0,1,1,0)
out=[]
for a in [Q(1,2),Q(2),Q(-3)]:
 d0=tuple(v1[i]-v0[i]-a*u[i] for i in range(4))
 d1=tuple(v1[i]-v0[i]+a*u[i] for i in range(4))
 assert sigma(v0,d0)==1-a and sigma(v1,d1)==1
 out.append({'a':str(a),'scalar_at_fixed_ends':str(sigma(v0,d0)*sigma(v1,d1))})
for length in [1,2,3,7]:
 deg=[1]+[0]*(length-1)+[1]; val=[1]+[2]*(length-1)+[1]; orders=[1]*(length+1)
 for i in range(length+1):
  ns=[j for j in [i-1,i+1] if 0<=j<=length]
  assert deg[i]-2+val[i]==sum(orders[j]-orders[i] for j in ns)
# Eliminate c using P(0)=1 in dimension five.
x0=Q(3,2);x1=Q(5,2)
assert x1**5-x1*x0**4==85
assert x1**3-x1*x0**2==10
assert x1/x0==Q(5,3)
print(json.dumps({'fixed_end_values':out,'chain_R3_c1':{'scalar_order':-1,'vector_order':-2},'hilbert_P1_coefficients':['85','10','5/3'],'scope':'finite arithmetic controls, not global contact realizability or mathematical gates'},indent=2))
