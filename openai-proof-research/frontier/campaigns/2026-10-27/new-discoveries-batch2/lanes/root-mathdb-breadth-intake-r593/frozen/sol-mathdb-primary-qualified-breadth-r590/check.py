from fractions import Fraction as Q
import json,pathlib
P=pathlib.Path(__file__).parent
f=[Q(1,2)**k+Q(1,3)**k for k in range(3)]
eps=Q(1,1000);det=f[0]*f[2]-f[1]**2
bound=eps*(abs(f[0])+abs(f[2])+2*abs(f[1]))+2*eps**2
assert det==Q(1,36) and bound<det
(P/'bounded-checks.json').write_text(json.dumps(dict(ids=[400382,400383],executed=True,calculation='f_k=(1/2)^k+(1/3)^k; rank-one Hankel determinant of any one-exponential approximant is zero; l2 error <=epsilon implies each first-three coordinate error <=epsilon',epsilon=str(eps),f_first_three=list(map(str,f)),determinant=str(det),determinant_perturbation_bound=str(bound),conclusion='literal arbitrary-epsilon strict shortening fails already for N=2; domain/wording obstruction only, zero discovery credit'),indent=2)+'\n')
print(det,bound)
