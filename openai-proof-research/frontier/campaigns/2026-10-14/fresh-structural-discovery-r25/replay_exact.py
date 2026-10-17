#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""Exact finite cross-checks, not a proof or contribution verdict."""
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parent

def rotate(x,n):return ((x<<1)&((1<<n)-1))|(x>>(n-1))
def canonical(x,n):
    vals=[]
    while x not in vals:vals.append(x);x=rotate(x,n)
    return min(vals)

def walsh(v):
    out=v[:];step=1
    while step<len(out):
        for start in range(0,len(out),step*2):
            for j in range(start,start+step):
                a,b=out[j],out[j+step];out[j]=a+b;out[j+step]=a-b
        step*=2
    return out

rows=[json.loads(s) for s in (ROOT/'cyclic-search.jsonl').read_text().splitlines()]
checked=0
for row in rows:
    if 'positive_orbit_reps' not in row:continue
    n=row['n'];pos=set(row['positive_orbit_reps'])
    table=[1 if canonical(x,n) in pos else -1 for x in range(1<<n)]
    assert all(table[x]==table[rotate(x,n)] for x in range(1<<n))
    w=walsh(table);d=max(s.bit_count() for s,v in enumerate(w) if v)
    lin=sum(w[1<<i] for i in range(n))
    assert d==row['actual_degree']<=row['d']
    assert lin==row['linear_numerator'] and w[0]==row['mean_numerator']
    assert not row['balanced_required'] or w[0]==0
    assert row['violates_sqrt']==(lin>0 and lin*lin>d*(1<<(2*n)))
    checked+=1

# Constraint positions for all possible selected leaves, not just one selector.
pairs=0
for q in range(5,21):
    for shift in range(1,q):
        for selected_a in range(1,q):
            ca={j:j for j in range(1,q) if j!=selected_a}
            for selected_b in range(1,q):
                cb={(j+shift)%q:j for j in range(1,q) if j!=selected_b}
                common=ca.keys() & cb.keys()
                assert len(common)>=q-4 and common
                assert all(ca[j]!=cb[j] for j in common)
                pairs+=1
# Carry permutation is one full cycle, including n=1 or r=1 endpoints.
for n in range(1,21):
    for r in range(1,21):
        seen=set();b=a=0
        while (b,a) not in seen:
            seen.add((b,a))
            b,a=((b+1,a) if b<r-1 else (0,(a+1)%n))
        assert (b,a)==(0,0) and len(seen)==n*r
print(json.dumps({'returned_tables_exactly_verified':checked,'search_rows':len(rows),'role_collision_cases':pairs,'carry_cycle_cases':400,'meaning':'finite exact cross-checks only; no general theorem or contribution verdict'},sort_keys=True))
