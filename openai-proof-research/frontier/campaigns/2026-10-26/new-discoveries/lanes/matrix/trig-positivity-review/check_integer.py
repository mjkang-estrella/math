"""Independent exact review: square-coefficient recursion, scaled Chebyshev recurrence.

This does not use the originating worker's generalized-binomial convolution.
"""
from pathlib import Path
import hashlib
import json
import sys
import time

sys.set_int_max_str_digits(100000)
root = Path(__file__).resolve().parent
d, n, p, q = 49, 949, 523, 527
start = time.time()

# B[k]=4**k*b[k].  The defining square is 1+z+...+z**d.
B = [1]
for k in range(1, n + 1):
    numerator = (4**k if k <= d else 0) - sum(B[i]*B[k-i] for i in range(1, k))
    assert numerator % 2 == 0
    B.append(numerator // 2)

# C[k]=q**k*ChebyshevT(k,p/q).
C = [1, p]
for k in range(2, n + 1):
    C.append(2*p*C[-1] - q*q*C[-2])

# Exact common-denominator accumulation, V/(4q)**n = sum b[k]*T[k](p/q).
V = B[0]*C[0]
for k in range(1, n + 1):
    V = (4*q)*V + B[k]*C[k]
den = (4*q)**n
assert -q < p < q
assert V < 0
out = dict(d=d, n=n, cosine=f'{p}/{q}', numerator=str(V), denominator=str(den),
           negative=V<0, value_approx=V/den,
           coefficient_method='B0=1; Bk=(4^k*indicator(k<=d)-sum_{i=1}^{k-1}Bi*B(k-i))/2',
           chebyshev_method='C0=1; C1=p; Ck=2p*C(k-1)-q^2*C(k-2)',
           coefficient_integer_sha256=hashlib.sha256(('\n'.join(map(str,B))+'\n').encode()).hexdigest(),
           elapsed_seconds=time.time()-start)
(root/'integer-certificate.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k not in {'numerator','denominator'}},indent=2))
