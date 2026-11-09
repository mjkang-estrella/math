from pathlib import Path
from fractions import Fraction as Q
from math import factorial
import json,hashlib
d=Path(__file__).parent
raw=(d/'moment-witness.json').read_bytes();a=json.loads(raw)
def dec(x): return Q(int(x['numerator_hex'],16),int(x['denominator_hex'],16))
r=list(map(dec,a['r']));f=list(map(dec,a['input']));g=list(map(dec,a['output']));eps=dec(a['epsilon'])
assert len(r)==37 and len(f)==len(g)==73
square=[sum((r[i]*r[k-i] for i in range(37) if 0<=k-i<37),Q(0)) for k in range(73)]
assert g==[v+(eps if k==0 else 0) for k,v in enumerate(square)]
assert eps>0 and r[-1]==Q(1,factorial(36))
lam=[Q(factorial(k),k*k+k+1) for k in range(73)]
assert all(f[k]==lam[k]*g[k] for k in range(73))
neg=sum((lam[k]*square[k] for k in range(73)),Q(0))
assert neg==dec(a['negative_form'])<0
assert sum(f)==neg/2==dec(a['input_at_one'])<0
assert eps==-neg/2 and f[-1]>0 and g[-1]>0
out={'status':'PASS','degree':72,'square_degree':36,'diagonal_identities':73,'positive_epsilon':True,'negative_input_at_one':True,'positive_leading_coefficient':True,'witness_sha256':hashlib.sha256(raw).hexdigest()}
(d/'root-check-result.json').write_text(json.dumps(out,indent=2)+'\n'); print(out)
