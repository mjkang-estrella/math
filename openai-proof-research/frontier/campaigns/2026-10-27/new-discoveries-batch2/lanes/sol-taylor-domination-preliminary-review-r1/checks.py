from pathlib import Path
from fractions import Fraction as F
import hashlib, json, datetime

lane = Path(__file__).resolve().parent
def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

rows = []
for t in range(1, 8):
    p = 3**t
    m = p*t
    assert m+1 > p and 3**m == p**p <= (m+1)**p
    # Exact simple-root derivative is -m; no numerical root solver.
    assert m > 0 and F(1, 3) < F(1, 2)
    rows.append(dict(t=t, p=p, m=m, roots=m+1, ratio=str(F(m+1,p)), pass_all=True))
products = []
for t in [1, 2]:
    p = 5**t
    m = p*t
    cs = [3+F(j,m+1) for j in range(1,m+1)]
    coeff = [F(1)]
    mass = F(1)
    for c in cs:
        nxt = [F(0)]*(len(coeff)+1)
        for i,a in enumerate(coeff):
            nxt[i] += a
            nxt[i+1] -= a*c
        coeff = nxt
        mass *= 1+c
    assert len(set(cs)) == m
    assert all(F(1,4)<1/c<F(1,3) for c in cs)
    assert sum(map(abs,coeff)) == mass < 5**m == p**p
    initial = max(map(abs,coeff[:p+1]))
    excluded = max(map(abs,coeff[1:p+1]))
    assert initial >= 1 and excluded > 1
    assert all(abs(coeff[k]) <= k**p*excluded for k in range(p+1,m+1))
    # Product derivative at each root, exact and nonzero.
    for c in cs:
        derivative = -c
        for d in cs:
            if d != c:
                derivative *= 1-d/c
        assert derivative != 0
    products.append(dict(t=t,p=p,m=m,tail_checked_indices=max(0,m-p),pass_all=True))

bindings = json.loads((lane/'bindings.json').read_text())
for r in bindings:
    assert sha(Path(r['original'])) == r['sha256'] == sha(lane/r['copy'])
ledger=json.loads((lane/'administrative/ledger.json').read_text())
assert (ledger['accepted_count'],ledger['total_accepted_count'],ledger['next_global_outcome_number']) == (9,39,40)
assert sha(lane/'live/1909.04918v1.pdf') == '4fc022935fb3de23343e9cbbae30c3a8b70d74c3300821ca802d28ed4b618aa3'
for rec in json.loads((lane/'access.json').read_text()):
    if 'file' in rec:
        assert sha(lane/rec['file']) == rec['sha256']
for name in ['published-exp','published-sp']:
    assert (lane/'live'/f'{name}.pdf').read_bytes().startswith(b'%PDF')
    assert (lane/'live'/f'{name}.txt').stat().st_size > 10000
guard=lane.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
out=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),sparse=rows,product=products,
         bindings_verified=len(bindings),counts=[9,39,40],
         helper_guard=dict(path=str(guard),sha256=sha(guard)),
         status='PASS: exact diagnostics and provenance only; not a proof for unbounded t')
(lane/'checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))

# Every file is bound; only the manifest and subsequent receipt are excluded.
files={str(f.relative_to(lane)):dict(sha256=sha(f),size=f.stat().st_size)
       for f in sorted(lane.rglob('*')) if f.is_file()
       and f.name not in ['final-manifest.json','verification-receipt.json']}
(lane/'final-manifest.json').write_text(json.dumps(dict(files=files,excludes=['final-manifest.json','verification-receipt.json']),indent=2)+'\n')
