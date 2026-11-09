from pathlib import Path
import hashlib,json,datetime
from fractions import Fraction as F
from itertools import combinations
P=Path(__file__).resolve().parent
def sha(f):return hashlib.sha256(f.read_bytes()).hexdigest()
manifest=json.loads((P/'manifest.json').read_text())
def verify_files():
    actual={str(f.relative_to(P)) for f in P.rglob('*') if f.is_file() and f.name not in ('manifest.json','receipt.json')}
    assert actual==set(manifest['files']), (actual^set(manifest['files']))
    for rel,h in manifest['files'].items():assert sha(P/rel)==h,rel
def bindings():
    rows=json.loads((P/'freeze.json').read_text())
    rows+= [json.loads(l) for l in (P/'freeze-new.jsonl').read_text().splitlines()]
    for r in rows:
        assert sha(Path(r['original']))==r['sha256'],r['original']
        assert sha(Path(r['copy']))==r['sha256'],r['copy']
    return len(rows)
verify_files();n=bindings()
# Execute only the deterministic rational calculation, without its write/print tail.
ns={'__file__':str(P/'leading.py')}
source=(P/'leading.py').read_text().split("(P/'leading-results.json').write_text")[0]
exec(compile(source,'leading-replay','exec'),ns)
assert json.loads(json.dumps(ns['out']))==json.loads((P/'leading-results.json').read_text())
assert ns['out']['monotone_three_cluster_cases']==980
assert not ns['out']['nonpositive_pivot_cases']
# Independent exact piecewise integration of the triangular splines.
def integral_cross(u,v):
    wu,wv=ns['weights'](u),ns['weights'](v)
    cuts=sorted(set(u+v));out=F(0)
    for left,right in zip(cuts,cuts[1:]):
        mid=F(left+right,2)
        # b_u(s) and sum_j wv_j*(s-vj)_+^3 on this piece.
        a=[sum(-wu[i]*u[i] for i in range(3) if u[i]<mid),sum(wu[i] for i in range(3) if u[i]<mid)]
        c=[sum(wv[i]*[F(-v[i]**3),F(3*v[i]**2),F(-3*v[i]),F(1)][k] for i in range(3) if v[i]<mid) for k in range(4)]
        for i,x in enumerate(a):
            for j,y in enumerate(c):out+=x*y*F(right**(i+j+1)-left**(i+j+1),i+j+1)
    return out
nodes=list(combinations(range(6),3))
for u in nodes:
    assert ns['diag'](u)==2*integral_cross(u,u)
    for v in nodes:assert ns['cross'](u,v)==integral_cross(u,v),(u,v)
verify_files();assert bindings()==n
receipt={'status':'PASS','time_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':sha(P/'manifest.json'),'manifest_files':len(manifest['files']),'original_copy_bindings_before_after':n,'exact_leading_replay_cases':980,'independent_exact_spline_integrals':420,'ordinary_source_result':'UNRESOLVED','counts':{'additional':9,'total':39,'next':40},'limitations':'Integrity and restricted leading-form checks only; no full Bernstein proof, interval negative witness, independent acceptance or complete current breadth clearance.'}
(P/'receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))
