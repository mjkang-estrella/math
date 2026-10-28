#!/usr/bin/env python3
"""Bounded exact Kronecker search. Finite evidence only unless a witness is found."""
import argparse,json,math,random,resource,time
from pathlib import Path

resource.setrlimit(resource.RLIMIT_AS,(1024**3,1024**3))
p=argparse.ArgumentParser();p.add_argument('--max-index',type=int,default=16)
p.add_argument('--samples',type=int,default=1200);args=p.parse_args()
N=args.max_index;K=6
M=math.comb(2*N+1,N)**2
bound=math.factorial(K)*M**K
bits=(2*bound+1).bit_length();base=1<<bits;mask=base-1
G=[[0]*(2*N+3) for _ in range(2*N+2)]
G[0][0]=1
for n in range(1,2*N+2):
    G[n][0]=1
    for k in range(1,n+1):
        G[n][k]=G[n-1][k]+(G[n-1][k-1]<<(bits*(n-k)))

def entry(kind,n,k):
    if k>n:return 0
    if kind=='B':return G[n][k]**2
    num=G[n+1][k]*G[n][k]
    den=((1<<(bits*(k+1)))-1)//(base-1)
    q,r=divmod(num,den);assert not r
    return q

matrices={kind+shape:[[entry(kind,n+(k if shape=='square' else 0),k)
    for k in range(N+1)] for n in range(N+1)]
    for kind in ['A','B'] for shape in ['triangle','square']}

def det(A):
    a=[row[:] for row in A];size=len(a);prev=1;sgn=1
    for k in range(size-1):
        if a[k][k]==0:
            row=next((i for i in range(k+1,size) if a[i][k]),None)
            if row is None:return 0
            a[k],a[row]=a[row],a[k];sgn=-sgn
        pivot=a[k][k]
        for i in range(k+1,size):
            for j in range(k+1,size):
                num=a[i][j]*pivot-a[i][k]*a[k][j]
                a[i][j],rem=divmod(num,prev);assert rem==0
        prev=pivot
        for i in range(k+1,size):a[i][k]=0
    return sgn*a[-1][-1]

def coefficients(value):
    out=[]
    while value:
        digit=value&mask
        if digit>base//2:digit-=base
        assert abs(digit)<=bound
        out.append(digit);value=(value-digit)>>bits
        assert len(out)<(2*N+1)**2*K+1
    return out

assert coefficients(det([[matrices['Atriangle'][r][c] for c in [0,1,2]] for r in [1,2,3]]))==[0,0,0,2,2,2,1]
assert coefficients(det([[matrices['Btriangle'][r][c] for c in [0,1,2]] for r in [1,2,3]]))==[0,0,2,6,6,4,1]
rng=random.Random(261028691);counts={name:0 for name in matrices};zeros=0
start=time.monotonic();witness=None
for test in range(args.samples):
    name=list(matrices)[test%4];A=matrices[name]
    k=rng.choice([3,3,4,4,5,6]);rows=sorted(rng.sample(range(N+1),k));cols=sorted(rng.sample(range(N+1),k))
    if 'triangle' in name and any(r<c for r,c in zip(rows,cols)):continue
    val=det([[A[r][c] for c in cols] for r in rows]);co=coefficients(val);counts[name]+=1
    if not co:zeros+=1
    bad=next((i for i,c in enumerate(co) if c<0),None)
    if bad is not None:
        witness={'matrix':name,'rows':rows,'cols':cols,'degree':bad,'coefficient':str(co[bad]),'coefficients':list(map(str,co))}
        break
result={'status':'NEGATIVE WITNESS' if witness else 'no counterexample in finite sample; not a proof',
    'max_index':N,'requested_samples':args.samples,'checked':counts,'zero_minors':zeros,
    'integer_base_bits':bits,'coefficient_abs_bound':str(bound),'source_anchor_checks':2,
    'witness':witness,'elapsed_seconds':round(time.monotonic()-start,3),'memory_limit_bytes':1024**3}
Path(__file__).with_name('search-result.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
