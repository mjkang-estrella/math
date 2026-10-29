from pathlib import Path
from fractions import Fraction
from math import factorial,prod
import hashlib,json
from datetime import datetime,timezone
root=Path(__file__).resolve().parent
lane=root.parent/'sol-fresh-source-discovery-r115'
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for c in iter(lambda:f.read(1024*1024),b''):h.update(c)
    return h.hexdigest()
rows=[json.loads(line) for line in (lane/'manifest.jsonl').read_text().splitlines()]
for row in rows:
    p=lane/row['path']
    assert p.stat().st_size==row['bytes'] and sha(p)==row['sha256'],row['path']
A=[3,5,6,7,8,14,16,20,36];B=[4,10,12,15,18,21,32]
assert len(set(A+B))==16 and min(A+B)>1
left=prod(Fraction(factorial(n),n**n) for n in A)
right=prod(Fraction(factorial(n),n**n) for n in B)
assert left==right
primes=[n for n in range(2,37) if all(n%d for d in range(2,n))]
def val(n,p):
    k=0
    while n%p==0:k+=1;n//=p
    return k
def legendre(n,p):
    z=0
    while n:n//=p;z+=n
    return z
va=[sum(legendre(n,p)-n*val(n,p) for n in A) for p in primes]
vb=[sum(legendre(n,p)-n*val(n,p) for n in B) for p in primes]
assert va==vb==[-123,-37,-4,-8,6,5,3,2,1,1,1]
cross1=prod(factorial(n) for n in A)*prod(n**n for n in B)
cross2=prod(factorial(n) for n in B)*prod(n**n for n in A)
assert cross1==cross2
record={'utc':datetime.now(timezone.utc).isoformat(),'manifest_verified':len(rows),
 'sets':[A,B],'primes':primes,'exponents':va,'cross_product_digits':len(str(cross1)),
 'rational_numerator':str(left.numerator),'rational_denominator':str(left.denominator),
 'source_text_scope':'PASS','ordinary_math':'PASS','substantive':'HOLD','novelty':'HOLD',
 'formal':'not started','credit':0,'counts':[8,38]}
(root/'ADOPTION.json').write_text(json.dumps(record,indent=2)+'\n')
rows.append({'path':'manifest.jsonl','bytes':(lane/'manifest.jsonl').stat().st_size,'sha256':sha(lane/'manifest.jsonl')})
(root/'review-freeze.json').write_text(json.dumps({'candidate':str(lane),'files':rows},indent=2)+'\n')
print(json.dumps(record))
