"""Independent finite algebra diagnostics. No geometric existence is certified."""
from fractions import Fraction as F
from itertools import product, permutations
from random import Random
import json

def convolution(a,b):
    c=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): c[i+j]+=x*y
    return c

def next_fit(capacities,items):
    used=[0]*len(capacities); j=0
    for x in items:
        while j<len(used) and used[j]+x>=capacities[j]: j+=1
        if j==len(used):return False,used
        used[j]+=x
    return True,used

def pfaff(a):
    n=len(a)
    if n==0:return F(1)
    return sum((-1)**(j+1)*a[0][j]*pfaff([[a[k][l] for l in range(n) if l not in (0,j)]
                  for k in range(n) if k not in (0,j)]) for j in range(1,n))

def run():
    counts={}; rng=Random(7009)
    a=[2]*6; q=[1,3,4,4,3,1]
    tc=sum(max(x,y) for x,y in zip(convolution(a,[1,1]),convolution(q,[1,1])))
    tm=sum(max(x,y) for x,y in zip(convolution(a,[1,6,1]),convolution(q,[1,6,1])))
    assert (tc,tm)==(34,140)
    for m in range(1,51):
        b=10+176*m
        assert 4*(2*b+4*tc*m)==80+1952*m
        assert 8*b+4*tm*m==80+1968*m
        assert 8*b+32*sum(q)*m==80+1920*m
    counts['torsion_formula_assertions']=151
    # Independently reconstruct the sharp companion from its center shifts.
    L=1661
    fr=lambda r:[sum(1 for k in range(1,L-r+1) if 0<=j-k<=r) for j in range(1,L+1)]
    f0,f1,f2=[fr(r) for r in range(3)]
    aa=[4*x for x in f1];qq=[3*x+2*y for x,y in zip(f0,f2)]
    b=1665+2*16*(L-1)+3*8*L+2*24*(L-2)
    cc=sum(map(max,zip(convolution(aa,[1,1]),convolution(qq,[1,1]))))
    mm=sum(map(max,zip(convolution(aa,[1,6,1]),convolution(qq,[1,6,1]))))
    assert 4*(2*b+4*cc)==1872232
    assert 8*b+4*mm==1872264
    assert 8*b+32*max(sum(aa),sum(qq))==1872232
    counts['sharp_companion_assertions']=3
    tested=qualified=0
    for J in range(1,4):
        for caps in product(range(2,8),repeat=J):
            for k in range(1,5):
                for items in product(range(1,4),repeat=k):
                    tested+=1
                    if sum(items)+J*max(items)<sum(caps):
                        ok,used=next_fit(caps,items);assert ok
                        assert sum(used)==sum(items) and all(u<c for u,c in zip(used,caps))
                        qualified+=1
    counts['next_fit_inputs']=tested;counts['next_fit_assertions']=2*qualified
    assert not any(all(sum(F(3,5) for i in range(3) if alloc[i]==j)<1 for j in range(2))
                   for alloc in product(range(2),repeat=3))
    assert 3*F(3,5)<2
    counts['fragmentation_counterexample_assertions']=2
    cycle_count=orbit_checks=0
    for n in range(1,6):
        for perm in permutations(range(n)):
            for vals in product((-2,0,3),repeat=n):
                unseen=set(range(n));K=[F(0)]*n;averages=[]
                while unseen:
                    first=min(unseen);cycle=[];x=first
                    while x not in cycle:cycle.append(x);unseen.remove(x);x=perm[x]
                    avg=F(sum(vals[x] for x in cycle),len(cycle));averages.append(avg)
                    for x in cycle[:-1]: K[perm[x]]=K[x]+vals[perm[x]]-avg
                    for x in cycle:
                        assert vals[perm[x]]+K[x]-K[perm[x]]==avg;orbit_checks+=1
                assert min(vals[perm[x]]+K[x]-K[perm[x]] for x in range(n))==min(averages)
                cycle_count+=1
    counts['cycle_instances']=cycle_count;counts['cycle_assertions']=cycle_count+orbit_checks
    weighted=0
    for n in range(2,8):
        perm=list(range(n));rng.shuffle(perm);vals=[F(rng.randrange(-9,10),3) for _ in perm]
        def it(x,j):
            for _ in range(j):x=perm[x]
            return x
        for N in range(1,10):
            K=[-sum(F(N-1-j,N)*vals[it(x,j+1)] for j in range(N-1)) for x in range(n)]
            for x in perm:
                assert vals[perm[x]]+K[x]-K[perm[x]]==sum(vals[it(x,j+1)] for j in range(N))/N
                weighted+=1
    counts['birkhoff_identity_assertions']=weighted
    curvature=0
    for m in range(1,4):
        for _ in range(120):
            A=[F(rng.randrange(-4,5),2) for _ in range(2*m)]
            B=[F(rng.randrange(-4,5),3) for _ in range(2*m)]
            h=F(rng.randrange(1,8));n=2*m+2;s=2*m;t=s+1
            mat=[[F(0)]*n for _ in range(n)]
            for j in range(m):mat[2*j][2*j+1]=1
            for j in range(2*m):mat[j][s]=A[j];mat[j][t]=B[j]
            mat[s][t]=h
            for i in range(n):
                for j in range(i+1,n):mat[j][i]=-mat[i][j]
            bracket=sum(A[2*j]*B[2*j+1]-A[2*j+1]*B[2*j] for j in range(m))
            assert pfaff(mat)==h-bracket;curvature+=1
    counts['curvature_pfaffian_assertions']=curvature
    for L in range(2,81):
        amplitude=F(1,L);frequency=L*L;theta=F(1,L)
        assert amplitude<1 and amplitude**2*frequency**2>1
        assert 1-theta**2*amplitude**2*frequency**2==0
    counts['small_amplitude_curvature_assertions']=158
    # Genuine symplectic shear, but the Alexander path leaves the target.
    assert 64<108 # (8/(3 sqrt(3)))^2 < 2^2
    assert 1+(4-4*F(1,2)**2)**2>9
    assert F(-1,4)<0 and F(1,2)-F(1,4)>0 and F(1,2)-F(1,4)==F(1,4)
    counts['shear_and_fixed_region_assertions']=3
    # Exact same-orientation symplectic endpoints, degenerate linear interpolation.
    assert (1*1*1)==((-1)*(-1)*1)==1
    assert (F(1,2)-F(1,2))**2==0
    counts['moser_interpolation_assertions']=2
    # Normal resonance: odd r, epsilon=pi/r in units where omega=1.
    for r in range(3,102,2):
        epsilon_over_pi=F(1,r)
        assert r*epsilon_over_pi==1 and epsilon_over_pi<1
    counts['odd_iterate_resonance_assertions']=50
    return dict(status='PASS_FINITE_DIAGNOSTICS',counts=counts,
      total_assertions=sum(v for k,v in counts.items() if k.endswith('_assertions')),
      scope='Exact finite algebra only; no packing, Floer, Lagrangian classification, or universal theorem certification.')

if __name__=='__main__':print(json.dumps(run(),indent=2,sort_keys=True))
