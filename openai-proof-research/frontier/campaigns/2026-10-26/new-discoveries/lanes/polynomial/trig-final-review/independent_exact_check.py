from pathlib import Path
import json,hashlib,decimal
N=949;D=50
# Independent coefficients: directly square the normalized root. No ODE recurrence.
B=[1]
for k in range(1,N+1):
    n=(4**k if k<D else 0)-sum(B[i]*B[k-i] for i in range(1,k))
    assert n%2==0
    B.append(n//2)
# Independent cosine: multiply in Z[sqrt(-4200)], rather than use Chebyshev recurrence.
x,y=1,0
H=0
for k in range(N+1):
    H=2108*H+B[k]*x
    x,y=523*x-4200*y,x+523*y
assert H<0
assert -476*(2108**N) < 1000000*H < -475*(2108**N)
decimal.getcontext().prec=60
value=decimal.Decimal(H)/decimal.Decimal(2108**N)
result={'D':D,'source_d':D-1,'n':N,'cos_t':'523/527','exact_scaled_sum_negative':True,'strict_rational_bracket':['-476/1000000','-475/1000000'],'integer_numerator_decimal_digits':len(str(-H)),'integer_numerator_sha256':hashlib.sha256(str(H).encode()).hexdigest(),'scaled_by':'2108^949','sum_approx':str(value),'coefficient_method':'square-root convolution with B_k=4^k b_k','cosine_method':'powers of523+sqrt(-4200), integer quadratic ring'}
p=Path(__file__).resolve().parent
(p/'independent-exact-check.json').write_text(json.dumps(result,indent=2)+'\n')
(p/'independent-numerator.txt').write_text(str(H)+'\n')
print(json.dumps(result,indent=2))
