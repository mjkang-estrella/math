from pathlib import Path
from fractions import Fraction as F
from math import factorial
import json,hashlib
L=Path(__file__).resolve().parent
def dec(q):return F(int(q['numerator_hex'],16),int(q['denominator_hex'],16))
p=L/'moment-witness.json';raw=p.read_bytes();j=json.loads(raw);r=list(map(dec,j['r']));f=list(map(dec,j['input']));g=list(map(dec,j['output']));d=dec(j['negative_form']);e=dec(j['epsilon'])
assert len(r)==37 and len(f)==len(g)==73 and e>0 and d<0
q=[F(0)]*73
for i,a in enumerate(r):
 for k,b in enumerate(r):q[i+k]+=a*b
functional=sum(z*F(factorial(k),k*k+k+1) for k,z in enumerate(q))
assert functional==d
q[0]+=e
assert q==g and [z*F(k*k+k+1,factorial(k)) for k,z in enumerate(f)]==g
assert sum(f)==d/2==dec(j['input_at_one'])<0 and f[-1]>0
assert hashlib.sha256(p.read_bytes()).digest()==hashlib.sha256(raw).digest()
out=dict(status='PASS',degree=72,source_sequence='(k*k+k+1)/k!',input_real_coefficients=True,input_at_one_negative=True,input_leading_positive=True,output_exactly_square_plus_positive=True,input_nonreal_at_most=70,output_nonreal_exactly=72,source_hypotheses_checked='every real polynomial; no real-rootedness restriction in CZDS definition',witness_sha256=hashlib.sha256(raw).hexdigest(),verification='direct Fraction convolution, direct reciprocal moment sum, coefficientwise diagonal identity; no LDL regeneration, no floating roots')
(L/'witness-verification.json').write_text(json.dumps(out,indent=2));print(json.dumps(out))
