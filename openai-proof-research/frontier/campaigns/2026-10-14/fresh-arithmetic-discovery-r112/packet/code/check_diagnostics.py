"""Read-only finite replay. No mathematical or contribution gate."""
import sys
sys.dont_write_bytecode = True
import json
from pathlib import Path
from fractions import Fraction as F
from math import isqrt
from diagnostic import diagram, matrix, rank_mod
from finite_repair import nullspace, uncollided

R = Path(__file__).resolve().parents[1]
records = json.loads((R/'scratch/line-peeling.json').read_text())
expected = {(d,m) for m in range(43,151)
            for d in range(isqrt(10*m*m)+1,isqrt(10*(m+1)*(m+1))-2)}
assert len(records) == len(expected) == 18
assert {(x['d'],x['m']) for x in records} == expected
for x in records:
    m=x['m']; cert=x['certificate']; rem=set(diagram(10,x['d'],m,F(cert['delta'])))
    chi=(x['d']+2)*(x['d']+1)//2-10*m*(m+1)//2
    assert chi==x['chi'] and x['mode']==('row' if chi>=0 else 'column')
    for i,(a,b,c,n) in enumerate(cert['lines']):
        cap=m-i
        assert cap>0 and (a or b)
        pts={p for p in rem if a*p[0]+b*p[1]==c}
        assert len(pts)==n and n>0
        assert n>=cap if x['mode']=='row' else n<=cap
        rem-=pts
    assert len(cert['lines'])==m if x['mode']=='row' else not rem

z=json.loads((R/'scratch/finite-repair.json').read_text())
S,I,A=matrix(13,11,3)
ns=nullspace(list(map(list,zip(*A))))
assert len(I)-len(ns)==z['rank_Q']==22
assert [[str(c) for c in v] for v in ns]==z['left_nullvectors']
for delta,rank in z['delta_tests']:
    assert rank_mod(matrix(13,11,3,F(delta))[2])==rank
assert rank_mod(uncollided(S,3,z['uncollided']['points']))==24
for x in json.loads((R/'scratch/diagnostic.json').read_text()):
    assert rank_mod(matrix(x['r'],x['d'],x['m'])[2])==x['rank_mod_1000003']
assert len(json.loads((R/'scratch/row_profiles.json').read_text()))==5353
print(json.dumps({'finite_replay':'matched','line_certificates':18,
                  'exact_rank_defect':22,'repaired_rank':24,
                  'limits':'finite diagnostics only; no unbounded proof or acceptance gate'}))
