from pathlib import Path
from fractions import Fraction as Q
from math import factorial
import json,hashlib,time
L=Path(__file__).resolve().parent
t=time.monotonic();p=L/'frozen/01-moment-witness.json';d=json.loads(p.read_text())
def q(z):return Q(int(z['numerator_hex'],16),int(z['denominator_hex'],16))
r=list(map(q,d['r']));eps=q(d['epsilon']);n=len(r)-1
# Certificate r entries are literal monomial coefficients, checked below.
sq=[sum((r[i]*r[k-i] for i in range(max(0,k-n),min(n,k)+1)),Q(0)) for k in range(2*n+1)]
lam=[Q(factorial(k),k*k+k+1) for k in range(2*n+1)]
quadratic=sum((lam[k]*sq[k] for k in range(2*n+1)),Q(0))
g=sq.copy();g[0]+=eps
f=[lam[k]*g[k] for k in range(2*n+1)]
facts={
 'n_is_36':n==36,'r_leading_is_inverse_factorial':r[-1]==Q(1,factorial(36)),
 'negative_form_direct':quadratic==q(d['negative_form']) and quadratic<0,
 'epsilon_positive_half':eps>0 and eps==-quadratic/2,
 'output_convolution_matches':g==list(map(q,d['output'])),
 'input_matches':f==list(map(q,d['input'])),
 'input_at_one_negative':sum(f)==q(d['input_at_one'])==quadratic/2 and sum(f)<0,
 'both_degree_72':len(f)==73 and f[-1]!=0 and g[-1]!=0,
 'positive_leading':f[-1]>0 and f[-1]==lam[-1]/factorial(36)**2,
 'all_73_diagonal_identities':all(Q(k*k+k+1,factorial(k))*f[k]==g[k] for k in range(73))}
result={'method':'independent Fraction convolution and direct moment functional; no LDL/checker import', 'checks':facts,'pass':all(facts.values()),'witness_sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'seconds':time.monotonic()-t}
(L/'exact-evidence.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2));assert result['pass']
