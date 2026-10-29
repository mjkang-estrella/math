"""Exact arithmetic for a failed proof shortcut; not a conjecture refutation."""
from fractions import Fraction as Q
import json
from pathlib import Path

def mul(a,b):return (a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def sub(a,b):return (a[0]-b[0],a[1]-b[1])
def normsq(a):return a[0]*a[0]+a[1]*a[1]

# f(z)=(z-a)(z-b), a=1+i/10, b=-3-i/10. f'(z)=2z+2.
a=(Q(1),Q(1,10));b=(Q(-3),Q(-1,10));one=(Q(1),Q(0))
assert normsq(a)==Q(101,100)>1
assert normsq(b)==Q(901,100)>1
assert (a[0]+b[0],a[1]+b[1])==(Q(-2),Q(0))
f1=mul(sub(one,a),sub(one,b)); assert f1==(Q(1,100),Q(-2,5))
# |f'|<=4 on |z|=1 by triangle inequality, attained at z=1.
qnormsq=Q(16)/normsq(f1)
assert qnormsq==Q(160000,1601)>1 # S/2=1
fminus1=mul(sub((-one[0],one[1]),a),sub((-one[0],one[1]),b))
assert fminus1==(Q(-399,100),Q(-2,5))
assert normsq(fminus1)==Q(160801,10000)>16
out={'root_norms_squared':[str(normsq(a)),str(normsq(b))],
     'f_at_1':[str(x) for x in f1],
     'global_derivative_maximum':'4, uniquely at z=1 by |z+1|<=2',
     'logderivative_squared_at_max':str(qnormsq),
     'proposed_local_bound_squared':'1',
     'f_at_minus1_squared':str(normsq(fminus1)),
     'conjecture_status':'not refuted: ||f|| >= |f(-1)| > 4 = ||fprime||',
     'checks':'PASS'}
Path(__file__).with_suffix('.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
