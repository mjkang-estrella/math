from pathlib import Path
from hashlib import sha256
from datetime import datetime,timezone
from math import comb
import json
root=Path(__file__).resolve().parent;lanes=root.parent;B=lanes.parent
def digest(p):
    h=sha256()
    with p.open('rb') as f:
        for b in iter(lambda:f.read(65536),b''):h.update(b)
    return h.hexdigest()
verified={};bulk=[]
for num in [112,113]:
    lane=lanes/f'sol-fresh-source-discovery-r{num}';count=0
    with (lane/'manifest.jsonl').open() as f:
        for line in f:
            d=json.loads(line);p=lane/d['path']
            assert p.stat().st_size==d['bytes'],d['path']
            if d['bytes']>10*1024*1024:
                bulk.append({'lane':num,**d,'root_check':'size only; worker hash receipt retained, root does not claim rehash of bulk survey cache'})
            else:
                assert digest(p)==d['sha256'],d['path'];count+=1
    verified[str(num)]=count
(root/'bulk-evidence.json').write_text(json.dumps(bulk,indent=2)+'\n')
# Exact cyclic-action obstruction, with a distinguished fixed point.
g=[0,2,1,4,5,3]
def power(k,x):
    for _ in range(k):x=g[x]
    return x
f2={x for x in range(6) if power(2,x)==x};f3={x for x in range(6) if power(3,x)==x}
assert f2=={0,1,2} and f3=={0,3,4,5} and f2|f3==set(range(6))
assert all(power(6,x)==x for x in range(6))
assert all(any(power(k,x)==x for k in [1,2,3]) for x in range(6))
# Correct auxiliary bounded-unit proof uses divisibility, not Frobenius in char 2^t.
for s in range(1,9):
    assert all(comb(2**s,k)%2==0 for k in range(1,2**s))
# Alternating idempotent differences over F2; no bound on nilpotence index.
def mul(a,b):
    n=len(a);return [[sum(a[i][k]*b[k][j] for k in range(n))%2 for j in range(n)] for i in range(n)]
for n in [3,5,8]:
    e=[[int(i==j and i%2==0) ^ int(j==i+1 and i%2==0) for j in range(n)] for i in range(n)]
    f=[[int(i==j and i%2==0) ^ int(j==i+1 and i%2==1) for j in range(n)] for i in range(n)]
    assert mul(e,e)==e and mul(f,f)==f
    assert all((e[i][j]^f[i][j])==int(j==i+1) for i in range(n) for j in range(n))
record={
 'utc':datetime.now(timezone.utc).isoformat(),'credit':0,'counts':[8,38],'small_manifest_hashes_verified':verified,
 'bulk_caches':'Sizes checked, worker manifests/receipts retained; root did not rehash the approximately37GB generated survey corpora. They are not new mathematical evidence and remain on disk unstaged. Details bulk-evidence.json.',
 'r112':{
  'Fu':'EXCLUDE_CLASSICAL_COROLLARY: full2409.12404v5 Conjecture5.3 covered.',
  'root_primary_read':'Actual Fu Definition1.2, admissibility and Conj5.3; visually read Zaslavsky printedpp57-58 Theorem3.1(A)(j); read AHK Theorem9.9(1) with preceding Proposition9.8 proof.',
  'bridge':'Zero-gain cycles form a biased graph. Complete lift adds e0 with ranks rG(S)+epsilon(S), rG(S)+1 when e0 included. Pair characteristic-polynomial terms: unbalanced cancel, balanced contribute (k-1)(-1)^|S| k^(rG(E)-rG(S)). Hence reduced characteristic polynomial equals literal tau=P/k^c. No balanced loops by alpha(loop)=1, so loopless, including disconnected/parallel/torsion/empty-edge cases. AHK supplies unsigned log-concavity; nonzero coefficients yield unimodality.',
  'strongest_countercase':'The explicit connection may be missing from the question, but the all-parameter endpoint is exactly the classical complete-lift reduced polynomial; no new inequality or construction remains.',
  'Hayashi':'UNRESOLVED. Proper fixed sets Fix(L_a^(d/p)) must not cover Q; generic cyclic action with fixed point and cycles2,3 defeats that weaker inference, not quandle conjecture. Root exact permutation check passes.',
  'neural':'Worker read actual public Dao-Rodriguez counterexample; no independent external certificate replay by root.',
  'novelty':'Current semantic-prior HOLD independent of positive classical exclusion.'},
 'r113':{
  'status':'Danchev2020 Problem3 UNRESOLVED, both pi-regular and J=0 regular clauses',
  'root_math':'Re-derived characteristic2 identity en+ne=n+n² for n=e+f. Alternating diagonal/superdiagonal idempotents yield all Jordan blocks. Unital matrix direct limit has actual hypotheses and unbounded nilpotence but is itself regular, so not counterexample. Exact sizes3,5,8 checks pass.',
  'auxiliary_correction':'Frozen Problem1 paragraph improperly treats (1+a)^(2^s)-1 as a^(2^s) in characteristic2^t. Correct proof: write m=2^s*d with d odd. b=(1+a)^(2^s)-1 is nilpotent; 0=(1+b)^d-1=b*(d+nilpotent), second factor a unit, so b=0. Interior binomial coefficients even imply a^(2^s) in2R, hence a^(t*2^s)=0. This weaker uniform bound still supplies bounded-index corollary. The claimed sharper bound is not adopted. Frozen report untouched.',
  'remaining':'No uniform derivation of inner inverses for powers from arbitrary difference witnesses; symmetry upgrade and bounded-index route fail. Ster2018 body unread. Routine Problem2 clauses do not settle printed 2p-group branch.'},
 'scope':'No discovery nomination, Lean, paper or count change. Both completed threads/full reports read. Core sources hashed; bulk cache limitation explicit.'}
(root/'ADOPTION.json').write_text(json.dumps(record,indent=2)+'\n')
p=B/'NEXT.md';text=p.read_text()
old='finite/structural discovery r112 and arithmetic/structural discovery r113; completed r111 replaced by independent Renyi-threshold preliminary review.'
new='independent Renyi-threshold preliminary review; two freed slots reserved for fresh discovery r114 and r115. r112 Fu full conjecture is EXCLUDED by literal complete-lift reduced-characteristic-polynomial identification and AHK; Hayashi remains unresolved. r113 Danchev Problem3 remains unresolved; root corrected auxiliary char2^t bound to t*2^s, preserving routine disposition and frozen report. See root-fresh-source-r112-r113-handbacks/ADOPTION.json.'
assert old in text;p.write_text(text.replace(old,new,1))
print(json.dumps({'status':'PASS','core_hashes_verified':verified,'bulk_cache_files_not_rehashed':len(bulk)}))
