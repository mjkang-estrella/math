"""Exact Abel-prefix diagnostic in Q(sqrt(17)); not a source theorem."""
import resource, json, hashlib
from pathlib import Path
from fractions import Fraction as F
from functools import cmp_to_key
resource.setrlimit(resource.RLIMIT_AS, (512*1024**2,)*2)
resource.setrlimit(resource.RLIMIT_CPU, (35,)*2)
Z=(F(0), F(0)); O=(F(1), F(0))
def add(x,y): return (x[0]+y[0],x[1]+y[1])
def neg(x): return (-x[0],-x[1])
def sub(x,y): return add(x,neg(y))
def scale(x,a): return (x[0]*a,x[1]*a)
def mul(x,y): return (x[0]*y[0]+17*x[1]*y[1],x[0]*y[1]+x[1]*y[0])
def power(x,n):
    ans=O
    while n:
        if n%2: ans=mul(ans,x)
        x=mul(x,x);n//=2
    return ans
def sign(x):
    a,b=x
    if b==0:return (a>0)-(a<0)
    if a==0:return (b>0)-(b<0)
    if a*b>0:return (a>0)-(a<0)
    d=a*a-17*b*b
    return ((d>0)-(d<0))*((a>0)-(a<0))
def enc(x):return [str(x[0]),str(x[1])]
p=Path(__file__).resolve().parent
src=p.parent/'root-log-arctangent-candidate-r1'/'exponential-terms.json'
raw=json.loads(src.read_text())
def read(key):return {tuple(map(F,r['lambda'])):tuple(map(F,r['coefficient'])) for r in raw[key]}
U,V=read('U'),read('V')
freq=sorted([x for x in U.keys()|V.keys() if sign(x)>0],key=cmp_to_key(lambda x,y:-sign(sub(x,y))))
for x in freq:
    assert U.get(x,Z)==U.get(neg(x),Z)
    assert V.get(x,Z)==neg(V.get(neg(x),Z))
trials=[]; success=None
for N in range(10,302,2):
    acc=[Z,Z,Z];rows=[]
    for lam in freq:
        u,v=U.get(lam,Z),V.get(lam,Z)
        lv=mul(lam,v);weight=power(lam,N-2)
        terms=[add(add(mul(u,power(lam,2)),scale(lv,N)),scale(u,2*N*(N-1))),add(lv,scale(u,4*N-2)),scale(u,2)]
        acc=[add(acc[i],mul(weight,terms[i])) for i in range(3)]
        rows.append({'frequency':enc(lam),'prefix':list(map(enc,acc)),'signs':list(map(sign,acc))})
    bad=[(i,j) for i,r in enumerate(rows) for j,s in enumerate(r['signs']) if s<0]
    trials.append({'N':N,'negative_prefixes':bad})
    if not bad:
        success={'N':N,'rows':rows};break
out={'input_sha256':hashlib.sha256(src.read_bytes()).hexdigest(),'trials':trials,'success':success,'scope':'Exact finite prefix certificate; requires Abel summation argument and independent exponential identity verification.'}
(p/'checks.json').write_text(json.dumps(out,indent=2))
print(json.dumps({'first_success':None if success is None else success['N'],'trials':len(trials),'last_failures':trials[-1]['negative_prefixes']}))
