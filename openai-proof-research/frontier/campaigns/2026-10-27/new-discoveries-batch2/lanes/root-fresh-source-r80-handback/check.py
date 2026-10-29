import datetime, hashlib, itertools, json, math
from pathlib import Path
P=Path(__file__).resolve().parent
B=P.parent.parent
S=P.parent/'sol-fresh-source-discovery-r80'
def sha(p):
    h=hashlib.sha256()
    with p.open('rb') as f:
        for chunk in iter(lambda:f.read(1048576),b''):h.update(chunk)
    return h.hexdigest()
prov=json.loads((S/'provenance.json').read_text())
for name,d in prov['artifacts'].items():
    assert sha(S/name)==d['sha256'],name
# Independent literal simulator uses a vacancy bitset and least free bit.
N=80
C=[[1]*N]
A=[[]]
for n in range(1,N+1):
    row=[]
    for l in range(n):
        row.append(sum(math.comb(n-1,k)*min(l+1,k+1)*C[k][l]*C[n-1-k][l] for k in range(n)))
    row.extend([row[-1]]*(N-n))
    C.append(row)
    A.append([row[l]-(row[l-1] if l else 0) for l in range(n)])
    assert sum(A[n])==(n+1)**(n-1)
for n in range(1,7):
    counts=[0]*n
    for word in itertools.product(range(n),repeat=n):
        free=(1<<n)-1
        maximum=0
        for preference in word:
            options=free & ~((1<<preference)-1)
            if not options:break
            bit=options & -options
            position=bit.bit_length()-1
            maximum=max(maximum,position-preference)
            free^=bit
        else:counts[maximum]+=1
    assert counts==A[n]
assert A[80][39]*A[80][41]>A[80][40]**2
assert A[62][30]*A[61][31]>A[62][31]*A[61][30]
for l in range(9):
    for n in range(26):
        lhs=C[n+1][l]
        rhs=(l+1)*sum(math.comb(n,k)*C[k][l]*C[n-k][l] for k in range(n+1))
        rhs-=sum(math.comb(n,k)*(l-k)*(1 if k==0 else (k+1)**(k-1))*C[n-k][l] for k in range(min(l,n+1)))
        assert lhs==rhs
out={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'status':'UNRESOLVED','credit':0,'counts':[8,38],
 'source':'Celano et al arXiv2507.07243v2 Conjecture6.5, exact maximum individual displacement unimodality',
 'source_body_read':'Actual frozen target definition and statement around Conjecture6.5; full worker discovery and summary read.',
 'artifact_hashes_verified':len(prov['artifacts']),'literal_bitset_enumeration_n_max':6,'recurrence_rows':80,'riccati_coefficient_checks':234,
 'exact_method_obstructions':['logconcavity n80,l40','adjacent-size likelihood-ratio n62,l30'],
 'root_reasoning':'Last-car vacancy separates earlier left and right intervals and preserves arrival order. Recurrence and reciprocal linear ODE are sound helpers. Neither establishes uniform coefficient single crossing.',
 'limits':'No full source proof, no formal certificate, no root replay through n500, no independent adjudication of screen-only Foata/inversion claims. Finite checks are diagnostic only.',
 'freshness':'Worker18:04 Omega observation is superseded by coherent root18:13:38 snapshot in root-edge-irregulator-final-freeze-r1; no parking-specific full current delta/body clearance performed, so hold retained.',
 'reviewed_summary_sha256':sha(S/'SUMMARY.md'),'reviewed_discovery_sha256':sha(S/'discovery.md')}
(P/'ADOPTION.json').write_text(json.dumps(out,indent=2)+'\n')
n=(B/'NEXT.md').read_text()
n=n.replace('fresh finite/arithmetic discovery r80 and fresh analysis/probability discovery r81.', 'fresh finite/arithmetic discovery r82 and fresh analysis/probability discovery r81.')
marker='r79 lasso yields'
note='r80 maximum parking displacement Conjecture6.5 remains unresolved. Root verified the last-car recurrence, 234 Riccati coefficient identities, literal counts through n6 and the two exact stronger-invariant failures; no all-n single-crossing proof. See root-fresh-source-r80-handback/ADOPTION.json.\n'
assert marker in n
n=n.replace(marker,note+marker,1)
(B/'NEXT.md').write_text(n)
root=B.parents[4]
paths=[p for p in S.rglob('*') if p.is_file() and '__pycache__' not in p.parts]
paths.extend([P/'check.py',P/'ADOPTION.json',P/'pathspec.txt',B/'NEXT.md'])
(P/'pathspec.txt').write_text(''.join(str(p.relative_to(root))+'\n' for p in sorted(paths)))
print(json.dumps({'status':'PASS scoped diagnostics; unresolved','hashes':len(prov['artifacts']),'counts':[8,38]}))
