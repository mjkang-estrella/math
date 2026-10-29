from pathlib import Path
from hashlib import sha256
from fractions import Fraction as F
from datetime import datetime,timezone
import json
root=Path(__file__).resolve().parent
lane=root.parent/'sol-fresh-source-discovery-r110'
def mul(a,b):return(a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0])
def scale(c,a):return(c*a[0],c*a[1])
u=(F(6),F(1));z=(F(-6),F(1));w=(F(0),F(1));v=(F(-4,5),F(3,5))
terms=[mul(u,v),scale(2,mul(z,v)),scale(2,mul(u,w)),mul(z,w)]
assert tuple(sum(t[i] for t in terms) for i in range(2))==(0,0)
assert all(t[1]>0 for t in [u,z,w,v])
def det(a):
    a=[[F(x) for x in row] for row in a];out=F(1)
    for k in range(len(a)):
        hit=next((i for i in range(k,len(a)) if a[i][k]),None)
        if hit is None:return F(0)
        if hit!=k:a[k],a[hit]=a[hit],a[k];out=-out
        p=a[k][k];out*=p
        for i in range(k+1,len(a)):
            q=a[i][k]/p
            for j in range(k+1,len(a)):a[i][j]-=q*a[k][j]
    return out
H=[[int(0<=2*j-i+1<=6) for j in range(6)] for i in range(6)]
minors=[det([row[:k] for row in H[:k]]) for k in range(1,7)]
assert minors==[1,0,0,0,-1,-1]
count=0
for line in (lane/'MANIFEST.sha256').read_text().splitlines():
    h,name=line.split(maxsplit=1);p=lane/name.lstrip('*');sha=sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(65536),b''):sha.update(b)
    assert h==sha.hexdigest(),name
    count+=1
record={'utc':datetime.now(timezone.utc).isoformat(),'status':'UNRESOLVED','credit':0,'counts':[8,38],
 'target':'Kudra2605.07628v2 Conjectures1/2, full stable/quasi-stable idealizer characterizations',
 'root_read':'Completed thread and full SUMMARY/discovery. Independent exact upper-half-plane symbol witness and six Hurwitz minors verified.',
 'root_checks':{'symbol_zero':True,'identity_multiplier_minors':[str(v) for v in minors]},
 'gap':'Separate even/odd multiplier real-rootedness and shifted binomial tests do not yet establish relative interlacing for every admissible pair, with strictness and boundary cases. No source counterexample.',
 'other_claim':'Marashdeh numerical-semigroup Conjecture4.9 screened unresolved; older genus/type bound is not its requested type bound.',
 'manifest_entries_verified':count,'holds':['Full mathematics','Current semantic registry clearance'],
 'qualification':'No external classical proof-body audit claimed by root; worker inspected bodies retained. Serialization MemoryError and corrected JSONL streaming preserved. Root initial run used lowercase manifest filename and failed FileNotFoundError after arithmetic checks; corrected to actual uppercase MANIFEST, same caps. No Lean or paper.'}
(root/'ADOPTION.json').write_text(json.dumps(record,indent=2)+'\n')
B=root.parents[1];p=B/'NEXT.md';text=p.read_text()
old='Active Sol high/default: fresh structural/algebraic discovery r110; two freed slots reserved for independent packing-construction eligibility review and fresh discovery r111.'
new='Active Sol high/default: independent packing-construction eligibility review; two freed slots reserved for fresh analytic discovery r111 and finite/structural discovery r112. r110 Kudra idealizer conjectures remain unresolved; root verified the exact stronger-symbol obstruction and identity-multiplier Hurwitz minors. This is not a source refutation. See root-fresh-source-r110-handback/ADOPTION.json.'
assert old in text;p.write_text(text.replace(old,new,1))
print(json.dumps({'status':'PASS','manifest_entries':count}))
