from pathlib import Path
from hashlib import sha256
from fractions import Fraction as Q
from math import comb, prod
from datetime import datetime, timezone
import json

root = Path(__file__).resolve().parent
lanes = root.parent
B = lanes.parent
def digest(p):
    h = sha256()
    with p.open('rb') as f:
        for b in iter(lambda: f.read(65536), b''):
            h.update(b)
    return h.hexdigest()
def manifest(lane):
    rows = []
    for line in (lane/'manifest.sha256').read_text().splitlines():
        h, name = line.split(maxsplit=1)
        name = name.lstrip('*')
        assert digest(lane/name) == h, name
        rows.append(name)
    return len(rows)
def closure(n, edges):
    rows = [0]*n
    for a,b in edges:
        rows[a] |= 1 << b
    for k in range(n):
        for a in range(n):
            if rows[a] >> k & 1:
                rows[a] |= rows[k]
    assert all(not (rows[a] >> a & 1) for a in range(n))
    return rows

packing = []
for m in range(3,7):
    for r in range(3):
        K = 2*m+1+r
        d = K-m
        pi = list(range(1,m))+[K-1]+list(range(m+1,K-m))+[K,m]+list(range(K-m,K-1))
        assert sorted(pi) == list(range(1,K+1))
        for j in range(1,6):
            n = m+j*d
            edges = []
            rank = sorted(range(K), key=lambda a: pi[a])
            for t in range(j):
                order = [t*d+a for a in rank]
                edges.extend(zip(order,order[1:]))
            chain = list(range(m-1))
            for t in range(j):
                chain += [(t+1)*d] + list(range(t*d+m,t*d+m+r)) + list(range((t+1)*d+1,(t+1)*d+m-1))
            hs = [t*d+m-1 for t in range(j+1)]
            zs = [t*d+m+r for t in range(j)]
            assert sorted(chain+hs+zs) == list(range(n))
            model = list(zip(chain,chain[1:])) + [(chain[-1],hs[-1])]
            model += list(zip(hs[:0:-1],hs[-2::-1]))
            model += list(zip(hs[:-1],zs))
            assert closure(n,edges) == closure(n,model)
            # Tree hook formula independently counts the residual comb:
            # root subtree sizes (2j+1), 2j, 2j-2,...,2; leaves size one.
            from math import factorial
            e = factorial(2*j+1)//((2*j+1)*prod(range(2,2*j+1,2)))
            assert e == prod(range(1,2*j,2))
            packing.append([m,K,j,e])

join = []
for n in range(2,10):
    for p in range(1,5):
        mixed = sum(comb(n*p,j)*comb(n,j) for j in range(n+1))
        assert mixed == comb((p+1)*n,n)
        central = comb(n,n//2)
        assert mixed > central and 2**n > central
        join.append([n,p,str(Q(mixed,central)),str(Q(2**n,central))])
for q in [Q(1,4),Q(1,2),Q(1),Q(3,2)]:
    assert 0 < 2-q < 2 # square intersection has unequal side lengths

utc = datetime.now(timezone.utc).isoformat()
l108 = lanes/'sol-fresh-source-discovery-r108'
l109 = lanes/'sol-fresh-source-discovery-r109'
counts = {str(i):manifest(lanes/f'sol-fresh-source-discovery-r{i}') for i in [108,109]}
freeze = {str(p.relative_to(l108)):digest(p) for p in sorted(l108.rglob('*')) if p.is_file() and '__pycache__' not in p.parts and p.suffix != '.pyc'}
(root/'r108-freeze.json').write_text(json.dumps(freeze,indent=2)+'\n')
(root/'checks.json').write_text(json.dumps({'utc':utc,'packing_closure_and_hook_checks':packing,'join_bound_loss_checks':join,'manifest_counts':counts},indent=2)+'\n')
record = {
 'utc':utc, 'credit':0, 'counts':[8,38], 'manifest_entries_verified':counts,
 'r108':{
  'status':'Full ordinary construction verified; routine-source-adaptation exclusion proposed, independent adjudication pending',
  'target':'Blitvic-Kammoun-Steingrimsson 2610.29846v1 Section7 item6, all m>2, K>2m, j>=1',
  'root_read':'Full proof and source Proposition5.24 with proof; Section7 items5-8. Earlier completed thread read retained.',
  'argument':'Literal window orders equal an initial globally comparable chain followed by a comb. Delete the chain; root subtree sizes give (2j-1)!!, equivalently source tree formula with unit branches.',
  'checks':'60 exact literal-vs-comb transitive closures and hook counts; independent corroboration, universal proof is in PROOF.md.',
  'strongest_contrary_case':'The uniform pattern construction answers an explicitly open all-parameter question; generic counting alone does not literally supply that construction. Independent review must distinguish routine adaptation from substantive new object construction.',
  'other_items':'Separator classification item5 and five-occurrence cutoff item8 remain unresolved.',
  'freeze':'r108-freeze.json', 'scope':'No Lean, paper, novelty PASS or acceptance.'},
 'r109':{
  'status':'UNRESOLVED',
  'target':'Frys-Kotrbaty 2609.08612v2 Conjecture1.11, every n>=2,p>=1, convex full-dimensional K,t in [0,1], some x in K',
  'root_read':'Completed thread, complete SUMMARY/discovery, actual source Conjecture1.11 and Theorem1.9; source explicitly states join implies mixed-volume bound.',
  'root_derivation':'At t=1/2, hull-to-Minkowski-sum loses binom((p+1)n,n)/binom(n,floor(n/2)); all-origin bound loses 2^n/binom(n,floor(n/2)). Translation-invariant coefficients cannot recover optimizer information. Square intersections are unequal-sided rectangles, so the simplex homothetic-fibre argument fails.',
  'checks':'32 exact Vandermonde/loss identities and four rational square fibres; no claim of universal join inequality or counterexample.',
  'gap':'Uniform sharp min-over-x hull-volume bound, or a concrete all-x violation; neither proved.',
  'holds':['Current semantic registry coverage','No formal endpoint'],
  'public_exclusions':'Worker body-read higher-order Godbersen proof and previous distance/Petty results retained as screened exclusions; root claims no independent external formal audit.'},
 'registry':'r108 records successful Omega89cda9c274d1122b7676173296af3047c3b64cd1 dated20:10:57Z and short 73a5033 delta (7 commits/3 paths), OpenAI7ef5 unchanged. This is later lawful evidence, not repair of prior 300-file truncation or full semantic absence. r109 respected supplied 403 limits; its frozen report remains unchanged.'
}
(root/'ADOPTION.json').write_text(json.dumps(record,indent=2)+'\n')
nextfile = B/'NEXT.md'
text = nextfile.read_text()
old = 'Active Sol high/default: fresh finite/discrete discovery r108, fresh structural/algebraic discovery r110, fresh analytic/geometric discovery r109.'
new = 'Active Sol high/default: fresh structural/algebraic discovery r110; two freed slots reserved for independent packing-construction eligibility review and fresh discovery r111. r108 full uniform double-factorial packing construction passes root ordinary checks, but routine-source-adaptation exclusion awaits independent adjudication. Items5/8 remain unresolved. r109 full unbalanced-join conjecture remains unresolved: source mixed-volume and all-origin bounds lose the sharp factor; square fibres obstruct direct simplex transfer. No counts changed. See root-fresh-source-r108-r109-handbacks/ADOPTION.json.'
assert old in text
nextfile.write_text(text.replace(old,new,1))
print(json.dumps({'status':'PASS','manifest_counts':counts,'r108_frozen_files':len(freeze),'packing_checks':len(packing),'join_checks':len(join)}))
