"""Finite diagnostics only; no external modules, no numerical proof."""
import os, resource, json, itertools, random
from pathlib import Path
for k in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS','NUMEXPR_NUM_THREADS'):
    os.environ[k]='1'
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
resource.setrlimit(resource.RLIMIT_CPU,(25,25))

def heights(K):
    n=[0]
    for k in range(1,K+1): n.append(k*k*(n[-1]+k+10))
    return n

def anchor(j): return '01'*j+'00'
def internal(w,n):
    if w == ('01'*((len(w)+1)//2))[:len(w)]: return True
    # Every non-spine internal word must start at one of the attached bushes.
    return any(len(w)<n[j] and w.startswith(anchor(j)) for j in range(1,len(n)) if len(anchor(j))<=len(w))
def leaf(w,n):
    return bool(w) and not internal(w,n) and internal(w[:-1],n)
def family(k,n,bits):
    H=n[k-1]+3; R=n[k]-(2*k+2)-H; B,r=divmod(R,k)
    assert len(bits)==(k-2)*B
    tail=''.join('11'+bits[i*(k-2):(i+1)*(k-2)] for i in range(B))+'1'*(r+H)
    return anchor(k)+tail

def verify_word(w,k,n):
    assert len(w)==n[k] and leaf(w,n) and w.endswith('111')
    # Source LIS: inspect ALL proper suffixes, not only contexts.
    assert all(not internal(w[i:],n) for i in range(1,len(w)))
    assert internal('',n)
    assert w.find('01'*k,2*k+2)==-1
    return len(w)-1  # Literal cascade exponent, every q is 1/2.

r={'status':'PASS','proof':False,'limits':{'address_bytes':512*1024**2,'cpu_seconds':25,'threads':1}}
# Exhaust all family completions in a small independently chosen finite-bush model.
toy=[0,6,10,36]
k=3; B=(toy[k]-(2*k+2)-(toy[k-1]+3))//k
count=0
for b in itertools.product('01',repeat=(k-2)*B):
    verify_word(family(k,toy,''.join(b)),k,toy);count+=1
r['exhaustive_toy_completions']=count
# Actual infinite-tree parameters: later bushes cannot affect words shorter than their anchors;
# for these words, extra later anchors have greater alternating prefix than can occur.
n=heights(4); rng=random.Random(18042); actual=0
for k in [3,4]:
    B=(n[k]-(2*k+2)-(n[k-1]+3))//k; f=(k-2)*B
    for bits in ['0'*f,'1'*f]+[''.join(rng.choice('01') for _ in range(f)) for z in range(4)]:
        verify_word(family(k,n,bits),k,n);actual+=1
r['actual_checked_words']=actual
r['actual_heights']=n
# Exact exponent bound and recurrence identities to k=100 (integers only).
n=heights(100); records=[]
for k in range(3,101):
    a=2*k+2; H=n[k-1]+3; B,rem=divmod(n[k]-a-H,k)
    D=n[k]-1-(k-2)*B
    assert D>=0 and B>=0
    assert k*D <= 2*n[k]+k*(a+H+k)
    assert k*k*n[k-1] <= n[k]
    # D/n_k <= 2/k + 1/k^2 + (3k+5)/n_k, no floating point.
    assert D*k*k <= (2*k+1)*n[k]+(3*k+5)*k*k
    if k in [3,4,10,30,100]: records.append({'k':k,'n':n[k],'D':D,'free_bits':(k-2)*B})
r['integer_bound_cases']=98;r['bounds']=records
Path(__file__).with_name('checks.json').write_text(json.dumps(r,indent=2))
print(json.dumps({k:v for k,v in r.items() if k!='bounds'},indent=2))
