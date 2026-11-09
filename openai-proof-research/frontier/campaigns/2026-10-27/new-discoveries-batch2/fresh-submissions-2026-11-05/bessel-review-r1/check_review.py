from fractions import Fraction as Q
from pathlib import Path
import json,hashlib,datetime
p=Path(__file__).parent
rows=[]
for n,lo,hi in [(1,13,16),(2,48,51),(3,102,105)]:
 l=Q(49,5)*(n+Q(1,4))**2-Q(3,4)-Q(1,3*n)
 u=10*(n+Q(1,4))**2-Q(3,4)+Q(1,3*n)
 assert lo<l<u<hi
 rows.append([n,str(l),str(u)])
a=Q(3,4)
assert a/2==Q(3,8) and 4*a*a/3==Q(3,4)
assert Q(3,8)+Q(3,4)/3<1
assert Q(1)-Q(9,8)+Q(81,192)-Q(729,9216)==Q(2007,9216)
assert Q(32)**2-16*57==112
assert 4*3**4-32*4-Q(4,27)==Q(5288,27)>0
# Square (b-3/(8b)+3/(128b^3)); coefficients of errors b^-2,b^-4,b^-6.
c,d=Q(-3,8),Q(3,128)
assert c*c+2*d==Q(3,16)
assert 2*c*d==Q(-9,512) and d*d==Q(9,16384)
assert c*c==Q(9,64)
# Upper-error correction = 9/(16384*b^6)*(1-32*b^2) <0 for b>3.
assert Q(1)-32*9<0
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'checks_pass':True,'enclosures':rows,'first_determinant':112,'uniform_determinant':'5288/27','classical_sandwich_squared_error_coefficients':['3/16','-9/512','9/16384'],'scope':'Exact arithmetic only; analytic reasoning is independently audited in REVIEW.md.'}
(p/'review-diagnostics.json').write_text(json.dumps(out,indent=2))
# Hash reused inputs without copying source trees.
inputs=['../analysis-r2/326635-proof.md','../analysis-r2/REPORT.md','../analysis-r2/exact-diagnostic.json','../analysis-r2/check_exact.py','../analysis-r2/sources/326635.pdf','../analysis-r2/sources/326635.txt','../analysis-r2/sources/dlmf-10-21.html','../analysis-r2/registry-reuse-screen.json','../../ledger.json','../../prior-campaign-context.json','../status.json']
receipt=[]
for q in inputs:
 f=p/q;receipt.append({'path':q,'sha256':hashlib.sha256(f.read_bytes()).hexdigest(),'bytes':f.stat().st_size})
(p/'input-receipts.json').write_text(json.dumps(receipt,indent=2))
print('Independent rational and sandwich expansion checks pass')
