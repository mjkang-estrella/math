# Author: Myeongjin Kang. No affiliation. SPDX-License-Identifier: MIT
import runpy,random,itertools as it,json
from pathlib import Path
root=Path(__file__).resolve().parent
counts=runpy.run_path(str(root/'explore.py'))['counts']
def ov(a,b):return max(k for k in range(min(len(a),len(b))+1) if a[len(a)-k:]==b[:k])
def exact(inputs, fixed_boost=False):
    req,V,alpha,m=counts(inputs, fixed_boost=fixed_boost)
    reps=sorted(s for s in req if s<=s[::-1])
    rows=[]
    for bits in it.product((0,1),repeat=len(reps)):
        words=[s[::-1] if b else s for s,b in zip(reps,bits)]
        best=None
        for p in it.permutations(range(len(words))):
            if not p:out=''
            else:
                out=words[p[0]]
                for i,j in zip(p,p[1:]):out+=words[j][ov(words[i],words[j]):]
            row=(len(out),p,out)
            if best is None or row<best:best=row
        rows.append(dict(bits=bits,length=best[0],order=best[1],word=best[2]))
    return dict(inputs=inputs,representatives=reps,counts=m,W_sym=sum(m[a] for a in alpha),OPT_RC=min(r['length'] for r in rows),orientation_rows=rows)
if __name__=='__main__':
    rng=random.Random(3737128)
    for trial in range(15000):
        inputs=[''.join(rng.choice('abc') for _ in range(rng.randrange(3,10))) for _ in range(rng.randrange(2,5))]
        d=exact(inputs)
        if d['W_sym']<d['OPT_RC']:
            print(json.dumps(dict(seed=3737128,trial=trial,**d),indent=2,sort_keys=True));break
    else:print(json.dumps(dict(status='no counterexample in bounded search',seed=3737128,proposals=15000)))
