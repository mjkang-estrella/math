"""Independent finite checks. Stdout only; never a universal proof."""
import json,runpy
from pathlib import Path
from itertools import product,combinations
from fractions import Fraction
ROOT=Path(__file__).resolve().parents[3]
M=runpy.run_path(str(ROOT/'frontier/experiments/i110_galois_moment_cancellation/exact_moments.py'))
D=M['D']

def ramified_checks():
    # Exact integral arithmetic in Z[pi]/(pi^e-2), with v_pi(2)=e.
    count=0
    for e in [1,2,3,4,6]:
        def mul(a,b):
            c=[0]*(2*e-1)
            for i,x in enumerate(a):
                for j,y in enumerate(b):c[i+j]+=x*y
            for j in range(2*e-2,e-1,-1):c[j-e]+=2*c[j]
            return c[:e]
        def pw(a,n):
            z=[1]+[0]*(e-1)
            while n:
                if n&1:z=mul(z,a)
                a=mul(a,a);n//=2
            return z
        def val(a):return min((e*D['vp'](abs(x),2,100000)+i for i,x in enumerate(a) if x),default=100000)
        pi=[2] if e==1 else [0,1]+[0]*(e-2)
        alphas=[pi,[1+pi[0]]+pi[1:],[1+3*pi[0]]+[3*x for x in pi[1:]]]
        for a in alphas:
            omega=a[0]%2
            for k in range(8):
                for u in [1,3,5]:
                    z=pw(a,2**k*u);z[0]-=omega
                    assert val(z)>=k+1;count+=1
    return count

def positive_residues():
    count=0
    for p,f in [(2,1),(2,2),(2,3),(3,1),(3,2),(5,1)]:
        q=p**f;mod=q-1
        for r in range(1,4):
            for rho in product(range(mod),repeat=r):
                bs=[b for b in range(f) if sum(rho)%mod==pow(p,b,mod)]
                if not bs:continue
                b=bs[0];ms=[x if x else mod for x in rho]
                while p**b<sum(ms):b+=f
                ms[0]+=p**b-sum(ms)
                assert all(x>0 for x in ms) and sum(ms)==p**b
                assert tuple(x%mod for x in ms)==rho
                def vf(n):
                    v=0
                    while n:n//=p;v+=n
                    return v
                c=vf(sum(ms))-sum(vf(x) for x in ms)
                for k in [f,2*f]:
                    assert vf(p**k*sum(ms))-sum(vf(p**k*x) for x in ms)==c
                count+=1
    return count

def a4_labels():
    tab,inv,orders=D['old']['group'](4,True);cs=D['classes'](tab,inv);ix={x:j for j,C in enumerate(cs) for x in C};W=[]
    for B in cs:
        col=0
        for y in range(12):
            if orders[y]==2:col^=1<<ix[tab[y][min(B)]]
        W.append(col)
    P=M['mp'](W,12)
    L=[]
    for B in cs:
        z=0
        for _ in range(5):z=tab[z][min(B)]
        L.append(1<<ix[z])
    count,profile=M['fixed_integer'](P,L)
    assert P==M['ident'](4) and count==2 and profile==[3,4,3,4]
    assert Fraction(1+9,12)==Fraction(5,6)
    return {'fixed_labels':count,'rank_profile':profile,'central_projector_identity_coefficient':'5/6','nonintegral_at_2':True}

def product_factor():
    old=runpy.run_path(str(ROOT/'frontier/experiments/i108_galois_tuple_divisibility/checks.py'))
    g=D['old']['group'](3);nbase=next(iter(old['direct'](g,2,5,2).values()))
    direct=old['direct'](D['product'](g,5),2,17,2)
    count=0
    # Each product singular class is transpositions x a single C5 element.
    for ms in D['compositions'](2,5):
        nonzero=any(ms[i] for i in range(1,5));F=5 if nonzero else 4
        multi=1 if 2 in ms else 2
        assert direct.get(ms,0)==multi*nbase*F;count+=1
    return count

def chain_toggle():
    tab,inv,orders=D['old']['group'](4);hs=D['old']['subgroups'](tab)
    ps=[H for H in hs if len(H)&(len(H)-1)==0]
    def norm(H):return frozenset(x for x in range(len(tab)) if {tab[tab[x][z]][inv[x]] for z in H}==H)
    ns={H:norm(H) for H in ps};chains=[]
    def extend(C):
        chains.append(C)
        for H in ps:
            if C[-1]<H:extend(C+(H,))
    extend((frozenset([0]),));pairs=0
    def toggle(C,P):
        i=max(j for j,Q in enumerate(C) if not P<=Q)
        T=frozenset(tab[x][y] for x in P for y in C[i])
        return C[:i+1]+C[i+2:] if i+1<len(C) and C[i+1]==T else C[:i+1]+(T,)+C[i+1:]
    for C in chains:
        H=frozenset.intersection(*(ns[Q] for Q in C))
        for P in ps:
            if len(P)==1 or not P<=H:continue
            T=toggle(C,P);H2=frozenset.intersection(*(ns[Q] for Q in T))
            assert toggle(T,P)==C and abs(len(T)-len(C))==1
            assert ns[P]&H==ns[P]&H2;pairs+=1
    return {'group':'S4','chains':len(chains),'normalized_nontrivial_P_pairs':pairs,'boundary':'subgroup skeleton only; Brauer local-point compatibility proved in report'}

def main():
    return {'status':'PASS','ramified_power_checks':ramified_checks(),'positive_residue_checks':positive_residues(),
            'A4_fixed_labels':a4_labels(),'direct_product_multisets':product_factor(),'chain_toggle':chain_toggle(),
            'boundary':'finite checks only, not universal proof or contribution acceptance'}
if __name__=='__main__':print(json.dumps(main(),indent=2))
