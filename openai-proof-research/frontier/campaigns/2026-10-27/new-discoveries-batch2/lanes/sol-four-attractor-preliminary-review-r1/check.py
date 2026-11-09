"""Independent literal certificate; no candidate code or root output imported."""
from pathlib import Path
from itertools import combinations
import json,hashlib
D=Path(__file__).parent
w='010110010101100101101001101010011010'
def theta(s,t):return s[::-1] if t=='R' else ''.join('1' if c=='0' else '0' for c in s[::-1])
v='';steps=[]
for a,t in zip('00101','EEEER'):
    s=v+a
    # Independently test all appended strings by the equivalent overlapping reflection condition.
    valid=[k for k in range(len(s)+1) if s[len(s)-k:]==theta(s[len(s)-k:],t)]
    k=max(valid);v=s+theta(s[:len(s)-k],t)
    assert v==theta(v,t) and v.startswith(s)
    # Every shorter total length would force a longer fixed suffix, already ruled out.
    assert all(s[len(s)-j:]!=theta(s[len(s)-j:],t) for j in range(k+1,len(s)+1))
    steps.append(dict(letter=a,closure=t,longest_suffix=k,word=v))
assert v==w and [s['longest_suffix'] for s in steps]==[0,2,0,4,2]
factors={w[i:j] for i in range(36) for j in range(i+1,37)}
def starts(f):return [i for i in range(37-len(f)) if w[i:i+len(f)]==f]
def cover(f):return {j for i in starts(f) for j in range(i,i+len(f))}
fs=['001010','010101','101011','001011','101101','110100','110101','101010','010100','1100','0011']
expected=[[5],[6],[7],[13],[15],[17],[23],[24],[25],[3,11],[21,29]]
assert [starts(f) for f in fs]==expected
cov=[cover(f) for f in fs]
misses={}; cases={}; count=0
A=set(range(5,13));B=set(range(13,23));C=set(range(23,31))
for g in combinations(range(36),4):
    count+=1;G=set(g)
    missing=next((f for f,c in zip(fs,cov) if G.isdisjoint(c)),None)
    assert missing is not None
    misses[missing]=misses.get(missing,0)+1
    if all(G&b for b in [A,B,C]):
        key=tuple(len(G&b) for b in [A,B,C]);cases[str(key)]=cases.get(str(key),0)+1
        assert key in [(1,1,1),(2,1,1),(1,2,1),(1,1,2)]
upper={5,10,18,21,28}
assert all(upper & cover(f) for f in factors)
out=dict(word=w,length=36,steps=steps,distinct_nonempty_factors=len(factors),four_subsets=count,missing_histogram=misses,block_cases=cases,eleven=[dict(factor=f,starts=starts(f),coverage=sorted(cover(f))) for f in fs],upper=sorted(upper),all_checks=True)
(D/'check-results.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
