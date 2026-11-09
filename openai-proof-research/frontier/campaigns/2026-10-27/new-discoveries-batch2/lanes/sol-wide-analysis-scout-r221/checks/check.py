from fractions import Fraction as F
from math import comb
import json

def moment(k):
    return sum((F(comb(k,j)*(-3)**j*2,(j+1)*(j+2)) for j in range(k+1)),F())
m=[moment(k) for k in range(15)]
assert m[:5]==[F(1),F(0),F(1,2),F(-1,5),F(3,5)]
a=F(1,100); gamma=a*a*m[2]**2
R=a**4*m[4]**2/(12*(1-4*a))
upper=a*a*m[2]**2/2-a**3*m[3]**2/6+R
gap=gamma-2*upper
assert gamma==F(1,40000) and R==F(1,3200000000)
assert gap==F(61,4800000000)>0
# Independent longer exact convergent-series enclosure. |aW|<=4a.
N=12
partial=sum((F((-1)**k,k*(k-1))*a**k*m[k]**2 for k in range(2,N+1)),F())
tail=(4*a)**(N+1)/((N+1)*N*(1-4*a))
assert partial+tail<gamma/2
assert partial-tail>0
print(json.dumps({'moments':[str(v) for v in m[:7]],'gamma':str(gamma),'remainder_bound':str(R),'gamma_minus_2I_lower_bound':str(gap),'I_interval':[str(partial-tail),str(partial+tail)],'PASS':True},indent=2))
