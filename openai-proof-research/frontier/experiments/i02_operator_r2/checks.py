"""Exact finite checks only. Universal conclusions require the written proofs."""
from pathlib import Path
from itertools import product, combinations
from fractions import Fraction as F
import json, runpy, shutil, hashlib
root=Path(__file__).resolve().parents[3]
out=Path(__file__).resolve().parent
original=root/'frontier/experiments/i02_crossfield_checks.py'
copy=out/'reproduce_crossfield.py'
shutil.copyfile(original,copy)
runpy.run_path(str(copy),run_name='__main__')
old=json.loads((root/'frontier/experiments/i02_crossfield_checks.json').read_text())
new=json.loads((out/'i02_crossfield_checks.json').read_text()) if (out/'i02_crossfield_checks.json').exists() else json.loads((out/'reproduce_crossfield.json').read_text())
# Original script uses an explicit output basename, safely relative to its copied __file__.
assert old==new
cover_checks=0
for k,m in [(1,1),(1,3),(2,2),(2,3)]:
    partial=[frozenset((i,v) for i,v in enumerate(w) if v>=0) for w in product(range(-1,m),repeat=k)]
    full=[s for s in partial if len(s)==k]
    covers=[g for mask in range(1<<len(partial)) if all(any((mask>>i)&1 and s<=f for i,s in enumerate(partial)) for f in full) for g in [[s for i,s in enumerate(partial) if (mask>>i)&1]]]
    for p in [F(0),F(1,2*m),F(1,m),F(1)]:
        cost=min(sum(p**len(s) for s in g) for g in covers)
        assert cost==min(F(1),(m*p)**k)
        cover_checks+=1

def a(j,x):
    k=j if j>=0 else -j-1
    if not k:return 10
    m=1
    while k>=8**m:m+=1
    n=2**m;t=x%n
    return 10*(k+1)+100*(n-2)+100*(t if j>=0 else n-1-t)
reflection_checks=0
for x in range(64):
    for j in range(-80,80):
        assert a(j,-1-x)==a(-j-1,x)
        reflection_checks+=1
for n in range(1,101):
    ds=[sum((j+r+1 if j+r>=0 else -j-r) for r in range(n)) for j in range(-2*n,2*n+1)]
    assert min(ds)==(n+1)**2//4
for m in range(1,50):
    assert min(sum(abs(j-2*r) for r in range(m)) for j in range(-2*m,2*m+1))==m*m//2
# Even-base unnormalised b exponent: exact finite recurrence, not a computation of L(x).
even_checks=0
for x in range(0,64,2):
    logs={0:0}
    for j in range(0,100):logs[j+1]=logs[j]+a(j,x)-a(j-1,x+1)
    for j in range(-1,-101,-1):logs[j]=logs[j+1]-a(j,x)+a(j-1,x+1)
    for j,val in logs.items():
        assert val<=560-45*abs(j)
        even_checks+=1
result=dict(status='passed',original_checks_reproduced_exactly=True,exhaustive_integral_cover_checks=cover_checks,dyadic_reflection_checks=reflection_checks,even_base_log_checks=even_checks,limitations='Finite support identities only; no conclusion about infinite cyclicity, normalizer truncations, or invariant subspaces follows from this computation.')
(out/'checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
