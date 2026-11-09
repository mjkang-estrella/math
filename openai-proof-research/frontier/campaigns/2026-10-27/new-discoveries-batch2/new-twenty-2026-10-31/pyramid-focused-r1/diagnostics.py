"""Small exact witnesses only; not the old n=7 first-batch sweep. Python 3 stdlib."""
from fractions import Fraction
from itertools import product
import json
from pathlib import Path

Q={(0,0),(1,0),(1,1),(2,1),(3,1),(3,2)}
rows=[]
for ds in product(range(2),repeat=4):
    a=b=c=0
    for i,d in enumerate(ds):
        c += b-a+1-sum((i,j) in Q for j in range(a,b+1))
        a,b = (a,b+1-int((i,b) in Q)) if d==0 else (a+int((i,a) in Q),b+1)
    rows.append(dict(directions=ds,initial_residual=c,width_after_four=b-a+1))
assert sum(r['initial_residual'] for r in rows)==16
assert sum(r['width_after_four'] for r in rows)==28
# Recurrence base arithmetic for the ALREADY PUBLIC Horak--Kim sequence.
f=[0,1]
for _ in range(2,15):f.append(f[-1]+f[-2])
m={3:6,4:9,5:13,**{i:4*f[i-1] for i in range(6,15)}}
base=[dict(a=a,b=b,m_sum=m[a+b],product=m[a]*m[b]) for a in range(3,8) for b in range(a,8)]
assert all(x['m_sum']<x['product'] for x in base)
# Test the explicit two-round attack on the row-frozen RESPONSE POLICY.
# The input need not be row-uniform: only the returned directions are frozen.
checks=0
for k in range(1,11):
    n=k+1
    for ds in product(range(2),repeat=k):
        first={(i,0) for i in range(k)}
        x=0; second=set(); prefix=[(0,0)]
        for i in range(k):
            if (i,x) not in first: second.add((i,x))
            x+=ds[i];prefix.append((i+1,x))
        second.add((k,x))
        assert len(first)==k and len(second)<=k
        assert all(v in first|second for v in prefix)
        checks+=1
out={'purpose':'diagnostics for explicit symbolic obstructions and known fallback only; no discovery proof',
     'six_query_witness':{'queries':sorted(Q),'sixteen_answers':rows,
       'expected_initial_residual':'1','expected_width_after_four':'7/4',
       'expected_residual_n_ge_4':'1+7(n-4)/4+(n-4)(n-5)/2',
       'difference_from_T_n_minus_3':'1-n/4'},
     'row_frozen_attack':{'tested_k':'1..10','tested_first_answer_vectors':checks},
     'public_sequence_base_checks':base}
Path(__file__).with_name('diagnostics.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS: sixteen fixed-query answers, row-frozen policy attack, public-sequence bases')
