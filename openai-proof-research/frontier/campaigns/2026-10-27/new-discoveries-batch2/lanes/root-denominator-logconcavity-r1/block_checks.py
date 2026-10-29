import resource, os, json, math, itertools
from pathlib import Path
resource.setrlimit(resource.RLIMIT_AS,(512*1024**2,512*1024**2))
for name in ['OPENBLAS_NUM_THREADS','OMP_NUM_THREADS','MKL_NUM_THREADS']: os.environ[name]='1'
def product(ns):
    a=[1]
    for n in ns:
        for k in range(1,n+1):
            b=a+[0]*k
            for j,x in enumerate(a): b[j+k]+=x
            a=b
    return a
def bad(a):
    return [(j,a[j-1:j+2],a[j]**2-a[j-1]*a[j+1]) for j in range(1,len(a)-1) if a[j]**2<a[j-1]*a[j+1]]
def denominator_step(a,n):
    b=n;v=0
    while b%2==0: b//=2;v+=1
    L=2**(v+1);r=[0]*(len(a)+(L-1)*b)
    for j in range(len(r)):
        r[j]=(r[j-b] if j>=b else 0)+(a[j] if j<len(a) else 0)-(a[j-L*b] if 0<=j-L*b<len(a) else 0)
    return r
records=[]
for t in range(4,8):
    first=2**(t-1);checked=0
    for n in range(first,161):
        ns=[n//2**i for i in range(t)]
        a=product(ns);assert not bad(a),(t,n,bad(a)[:1]);checked+=1
    records.append({'t':t,'first_n':first,'last_n':160,'all_coefficients_checked':True,'instances':checked})
# Independently compare binary layer product to geometric-step recurrence.
a=[1];exceptions=[]
for n in range(1,65):
    a=denominator_step(a,n)
    ns=[];m=n
    while m:ns.append(m);m//=2
    assert a==product(ns),n
    if bad(a):exceptions.append(n)
assert exceptions==[3,5,6,7]
# Exact initial obstruction, valid whenever every block length is >=3.
for t in range(1,12):
    a=product([3]*t)
    assert a[1]==t and a[2]==t*(t+1)//2
    assert a[3]==t*(t*t+3*t+8)//6
    assert 12*(a[2]**2-a[1]*a[3])==t*t*(t*t-13)
# Every number of binary layers >=4 splits into lengths from {4,5,6,7}.
for L in range(4,10000):
    q,r=divmod(L,4);parts=[4]*(q-1)+[4+r]
    assert sum(parts)==L and all(4<=x<=7 for x in parts)
# Counterexample to allowing arbitrary four block lengths.
a=product([1,1,1,4]); assert bad(a)
result={'status':'finite diagnostics only; full source unresolved','dyadic_block_checks':records,'literal_denominator_crosschecks_through':64,'source_exceptions':exceptions,'initial_obstruction_formula':'12 Delta_2=t^2(t^2-13), all block lengths >=3','arbitrary_four_blocks_counterexample':{'lengths':[1,1,1,4],'failures':bad(a)},'credit':0}
Path(__file__).with_name('block-checks.json').write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps(result))
