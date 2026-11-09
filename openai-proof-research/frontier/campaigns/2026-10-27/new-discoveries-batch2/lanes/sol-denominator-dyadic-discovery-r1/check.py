"""Small exact falsifiers and algebra checks, NOT a verification range proof."""
import os
for key in ('OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS'):
    os.environ[key] = '1'
import resource
resource.setrlimit(resource.RLIMIT_AS, (512*1024**2, 512*1024**2))
resource.setrlimit(resource.RLIMIT_CPU, (30,30))
from pathlib import Path
from fractions import Fraction
from math import comb
import json, datetime

def product(lengths):
    a=[1]
    for m in lengths:
        for i in range(1,m+1):
            b=a+[0]*i
            for k,v in enumerate(a): b[k+i]+=v
            a=b
    return a

def val(a,k): return a[k] if 0<=k<len(a) else 0

def delta(a,k): return val(a,k)**2-val(a,k-1)*val(a,k+1)

def sparse(a,s,L):
    b=[0]*(len(a)+(L-1)*s)
    for u in range(L):
        for k,v in enumerate(a): b[k+u*s]+=v
    return b

def mixed(a,k,s,u,v):
    return (2*val(a,k-u*s)*val(a,k-v*s)
       -val(a,k-1-u*s)*val(a,k+1-v*s)
       -val(a,k-1-v*s)*val(a,k+1-u*s))

def layers(n,t=None):
    a=[]
    while n and (t is None or len(a)<t): a.append(n);n//=2
    return a

# Only two actual dyadic blocks and one small artificial input; validate every
# index of the exact identity, including zero extensions and boundaries.
identities=[]
for lengths,s,L in [([8,4,2,1],9,2),([16,8,4,2],17,2),([3],2,4)]:
    a=product(lengths);b=sparse(a,s,L)
    for k in range(-1,len(b)+1):
        diagonal=sum(delta(a,k-u*s) for u in range(L))
        cross=sum(mixed(a,k,s,u,v) for u in range(L) for v in range(u+1,L))
        assert delta(b,k)==diagonal+cross
    identities.append({'lengths':lengths,'s':s,'L':L,'identity_at_all_indices':True})
a=product([8,4,2,1]);b=product([9,4,2,1]);assert b==sparse(a,9,2)
witness={'input':'D_8 = B_(4,8)', 'step':'D_9 = D_8 (1+x^9)',
 'a0_a1':a[:2], 'a8_a9_a10':a[8:11], 'mixed_at_k9':mixed(a,9,9,0,1),
 'old_delta9':delta(a,9), 'old_delta0':delta(a,0), 'new_delta9':delta(b,9)}
assert witness['mixed_at_k9']==-206 and witness['new_delta9']==1023
assert all(delta(a,k)>=0 for k in range(1,len(a)-1))
assert all(delta(b,k)>=0 for k in range(1,len(b)-1))
# Explicitly preserve the old arbitrary-four-factor falsifier.
c=product([1,1,1,4]);assert c[2:5]==[7,9,12] and delta(c,3)==-3
# Source small cases are a base check only; no enlarged n sweep.
small={str(n):[k for k in range(1,len(a)-1) if delta(a,k)<0]
       for n in range(1,10) for a in [product(layers(n))]}
assert [int(n) for n,v in small.items() if v]==[3,5,6,7]
# Check exact first coefficients and variance for each of the four proposed
# families at its initial block, rather than testing a parameter range.
initial=[]
for t in range(4,8):
    ns=layers(2**(t-1),t);a=product(ns)
    assert a[1]==t and a[2]==comb(t,2)+t-1
    assert a[1]**2-2*a[2]==2-t<0
    total=sum(a);N=len(a)-1
    var=sum(Fraction((2*k-N)**2,4)*v for k,v in enumerate(a))/total
    formula=sum(Fraction(m*(m+1)*(2*m+1),24) for m in ns)
    assert var==formula
    initial.append({'t':t,'lengths':ns,'a1':a[1],'a2':a[2],
       'poisson_ULC_margin_at_1':2-t,'variance':str(var)})
# Stabilization mod x^(K+1) is checked at one prescribed K in each family.
K=6
for t in range(4,8):
    m=2**(t-1)*K
    a=product(layers(m,t))[:K+1]
    assert a==product([K]*t)[:K+1]
result={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'status':'exact route diagnostics only; full conjecture unresolved','credit':0,
 'identity_checks':identities,'actual_block_mixed_term_counterexample':witness,
 'old_arbitrary_four_counterexample':{'coefficients_2_3_4':c[2:5],'delta3':delta(c,3)},
 'small_source_cases_1_through_9':small,'initial_family_ULC_and_variance_checks':initial,
 'stabilization_check':{'K':K,'t':[4,5,6,7]}}
Path(__file__).with_name('checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result,indent=2))
