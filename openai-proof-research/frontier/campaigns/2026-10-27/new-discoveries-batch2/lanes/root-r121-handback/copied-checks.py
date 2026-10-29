"""Exact diagnostics only; run through the prescribed helper_guard.py."""
from pathlib import Path
from fractions import Fraction
import hashlib,json,time
L=Path(__file__).resolve().parent
start=time.monotonic()
M=[1,1]
for n in range(1,81):
    a=(2*n+3)*M[n]+3*n*M[n-1]
    assert a%(n+3)==0
    M.append(a//(n+3))
T=[1]
for n in range(1,len(M)):T.append(M[n]-T[-1])
assert T[:13]==[1,0,2,2,7,14,37,90,233,602,1586,4212,11299]
# Independent quadratic GF recurrence M=1+zM+z^2 M^2.
C=[1]
for n in range(1,len(M)):
    C.append(C[-1]+sum(C[k]*C[n-2-k] for k in range(n-1)))
assert C==M
root=[];ratio_fail=[]
for n in range(9,81):
    # Centered root inequality; no logarithms or floating point.
    left=pow(T[n],2*(n*n-1))
    right=pow(T[n-1],n*(n+1))*pow(T[n+1],n*(n-1))
    root.append({'center':n,'strict':left>right})
    assert left>right
for n in range(3,80):
    # Ratio log-concavity at y_n=T_(n+1)/T_n.
    if T[n+1]**3*T[n-1]<T[n]**3*T[n+2]:ratio_fail.append(n)
# Log-balanced plus bounded ratios does NOT imply root log-concavity:
# a_n=2*3^n, a_n/n! log-concave, a_n log-convex, ratio exactly 3.
n=10;a=lambda k:2*3**k
assert a(n)**2==a(n-1)*a(n+1)
assert (n+1)*a(n)**2>=n*a(n-1)*a(n+1)
assert a(n)**(2*(n*n-1))<a(n-1)**(n*(n+1))*a(n+1)**(n*(n-1))
# Test the actual published coarse envelopes in Hou--Li3.1.
# y_n>=b_n and y_(n+1)<=b_(n+3), b_n=6(n+1)/(2n+5).
# h_n=3^n is a crude upper bound, not a sharp asymptotic one.
n=80;b=lambda k:Fraction(6*(k+1),2*k+5)
coarse=Fraction(3**(2*n))*b(n+3)**(n*(n+1))/b(n)**(n*(n+3))
assert coarse>1
receipt={'scope':'diagnostics, no source proof or source refutation',
 'motzkin_independent_recurrence_agreements':len(M),'root_inequalities':root,
 'ratio_logconcavity_failed_centers':ratio_fail,
 'generic_logbalanced_route_counterexample':'a_n=2*3^n at center10; not the source T_n',
 'published_coarse_envelope_failure':{'index':80,'HouLi_multiplicative_bound_greater_than_one':coarse>1},
 'arithmetic':'integer recurrence and integer-power comparisons only'}
(L/'check-results.json').write_text(json.dumps(receipt,indent=2)+'\n')
print({k:v for k,v in receipt.items() if k!='root_inequalities'})
