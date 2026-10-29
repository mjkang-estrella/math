import os
for name in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS'):
    os.environ[name]='1'
import resource
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(35,35))
import random,json,time
from pathlib import Path

def mul(a,b):
    c=0
    while b:
        low=b&-b;c ^= a << (low.bit_length()-1);b ^= low
    return c
def square(a):
    c=0
    while a:
        low=a&-a;c |= 1 << (2*(low.bit_length()-1));a ^= low
    return c
def relation(vs):
    piv={}
    for j,v in enumerate(vs):
        mask=1<<j
        while v:
            d=v.bit_length()-1
            if d not in piv:piv[d]=(v,mask);break
            w,m=piv[d];v ^= w;mask ^=m
        if not v:return mask
    return None
def fmt(t):return 'x' if t is None else 'F('+fmt(t[0])+','+fmt(t[1])+')'

rng=random.Random(732934)
def tree(n):
    if n==1:return None
    k=rng.randrange(max(1,n//3),min(n-1,2*n//3+1)+1)
    return tree(k),tree(n-k)
def data(t):
    if t is None:return 2,[(0,1)]
    a,wa=data(t[0]);b,wb=data(t[1]);bb=square(b)
    if max(2*(a.bit_length()-1),3*(b.bit_length()-1))>8000:raise OverflowError
    return square(a)^mul(bb,b),[(l+1,mul(a,w)) for l,w in wa]+[(l,mul(bb,w)) for l,w in wb]

start=time.monotonic();done=0;skip=0;failure=None
for j in range(2000):
    if time.monotonic()-start>20:break
    n=rng.randrange(12,51);t=tree(n)
    try:p,ws=data(t)
    except OverflowError:skip+=1;continue
    done+=1
    for l in set(v[0] for v in ws):
        ids=[i for i,v in enumerate(ws) if v[0]==l]
        rel=relation([ws[i][1] for i in ids])
        if rel is not None:
            failure={'n':n,'tree':fmt(t),'L':l,'positions':[ids[j] for j in range(len(ids)) if rel>>j&1]}
            break
    if failure:break
out={'checked':done,'skipped_degree_cap':skip,'failure':failure,'seed':732934,
     'scope':'Bounded characteristic-criterion falsification only; not source isolation.'}
Path(__file__).with_name('checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out))
