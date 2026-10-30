"""Falsify only the literal all-shape extension of source Theorem4.3."""
from itertools import combinations
from pathlib import Path
import sympy as S,json
L=Path(__file__).resolve().parent;q=S.Symbol('q')
nu=(2,2,1);cells={(i,j) for i,r in enumerate(nu) for j in range(r)}
def ribbon(a):
    rows=sorted({i for i,j in a})
    if rows!=list(range(min(rows),max(rows)+1)):return False
    lo=[];hi=[]
    for i in rows:
        js=sorted(j for h,j in a if h==i)
        if js!=list(range(min(js),max(js)+1)):return False
        lo.append(min(js));hi.append(max(js))
    if any(x<y for x,y in zip(lo,lo[1:])) or any(x<y for x,y in zip(hi,hi[1:])):return False
    for r in range(len(rows)-1):
        if len(set(range(lo[r],hi[r]+1))&set(range(lo[r+1],hi[r+1]+1)))!=1:return False
    return True
rs=[]
for size in range(1,6):
    for a in combinations(sorted(cells),size):
        a=frozenset(a)
        if any(j==0 for i,j in a) and ribbon(a):rs.append(a)
def tilings(left):
    if not left:yield ();return
    c=min(left)
    for a in rs:
        if c in a and a<=left:
            for rest in tilings(left-a):yield(a,)+rest
out={};count=0
for tiling in tilings(cells):
    count+=1;weight=1
    for a in tiling:
        head=min(a,key=lambda c:c[1]-c[0])
        assert len({j-i for i,j in a})==len(a)
        for i,j in a:
            leg=sum(j<r for r in nu[i+1:])
            weight*=1-q**(leg-len(a)) if (i,j)==head else q**leg-q**(-j)
    typ=tuple(sorted(map(len,tiling),reverse=True))
    out[typ]=out.get(typ,0)+weight
actual={tuple(x['partition']):S.sympify(x['coefficient'],locals={'q':q}) for x in json.loads((L/'independent-controls.json').read_text())['mu32_k1']}
rows=[]
for p in sorted(set(out)|set(actual),reverse=True):
    pred=S.factor(q**7*out.get(p,0)/(q-1)**5)
    residual=S.factor(pred-actual.get(p,0))
    rows.append(dict(partition=p,predicted=str(pred),actual=str(actual.get(p,0)),residual=str(residual)))
assert any(r['residual']!='0' for r in rows)
json.dump(dict(mu=[3,2],nu=nu,k=1,tilings=count,rows=rows,scope='Literal unchanged hook special-ribbon weights fail; not source counterexample; not exclusion of corrected tiling theories'),(L/'ribbon-route.json').open('w'),indent=2)
print(json.dumps(dict(tilings=count,mismatches=[r for r in rows if r['residual']!='0']),indent=2))
