"""I119 exact finite checks. No I/O in run(); no universal proof certification."""
import sys
sys.dont_write_bytecode = True
from fractions import Fraction as F
from itertools import product, permutations


def mass(bits, rates):
    p=F(1)
    for b,r in zip(bits,rates):p*=r if b else 1-r
    return p


def families(n):
    return [tuple(a for a in range(1<<n) if f>>a&1)
            for f in range(1,1<<(1<<n))
            if all(not(f>>a&1) or all(f>>b&1 for b in range(1<<n) if b&a==b)
                   for a in range(1<<n))]


def matroid(fam,n):
    return all(a.bit_count()>=b.bit_count() or any(
        (a|1<<i) in fam for i in range(n) if (b>>i&1) and not(a>>i&1))
        for a in fam for b in fam)


def opt(v,fam,allow=None):
    if allow is None:allow=(1<<len(v))-1
    return max(sum(x for i,x in enumerate(v) if a>>i&1)
               for a in fam if a&allow==a)


def greedy(v,s,fam,order):
    a=0
    for e in order:
        if v[e]>0 and v[e]>=s[e] and (a|1<<e) in fam:a|=1<<e
    return sum(v[e] for e in range(len(v)) if a>>e&1)


def prob_event(ev,rates):
    return sum(mass(bits,rates) for bits in product((0,1),repeat=len(rates))
               if ev(bits))


def poly_add(a,b):
    return [(a[i] if i<len(a) else F(0))+(b[i] if i<len(b) else F(0))
            for i in range(max(len(a),len(b)))]


def poly_mul(a,b):
    c=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b):c[i+j]+=x*y
    return c


def event_poly(ev,c,delta):
    out=[F(0)]
    for bits in product((0,1),repeat=len(c)):
        if not ev(bits):continue
        p=[F(1)]
        for b,x,d in zip(bits,c,delta):p=poly_mul(p,[x,d] if b else [1-x,-d])
        out=poly_add(out,p)
    return out


def run():
    checks={};triples=list(product((0,1),repeat=3));cnt=0
    for K in [1,2,3,4,8,16,64]:
        for t in [F(1,1024),F(1,64),F(1,4)]:
            a=F(3,4)*(1-t);p=1-a/2
            for r in [F(1,K),F(1),F(K)]:
                B=a+(1-a)*r;Z=1-p+p*r
                law={z:mass(z,[F(1,2),F(1,4),t])*(r if any(z) else 1)/Z for z in triples}
                pr=lambda pred:sum(v for z,v in law.items() if pred(z))
                assert sum(law.values())==1
                assert pr(lambda z:z[0])==r/(2*Z)
                h0=pr(lambda z:not z[0]);assert h0==B/(2*Z)
                assert pr(lambda z:not z[0] and z[1])/h0==r/(4*B)
                assert pr(lambda z:not z[0] and z[2])/h0==t*r/B
                h00=pr(lambda z:not z[0] and not z[1])
                assert pr(lambda z:not z[0] and not z[1] and z[2])/h00==t*r/(1-t+t*r)
                assert Z*pr(lambda z:not z[0] and z[1])==r/8
                assert Z*pr(lambda z:not any(z))==a/2
                omega=a/B
                assert omega*pr(lambda z:not z[0] and z[1])==a*r/(8*B*Z)
                assert B*Z/r==a*a/(2*r)+a*(1-a/2)+a*(1-a)/2+(1-a)*(1-a/2)*r
                assert B*Z/r<=K and a*r/(8*B*Z)>=a/(8*K)
                cnt+=1
    checks['original_rates_and_aggregate_cancellation']=cnt

    cnt=0
    for K in [1,2,3,8,32]:
        q=F(1,K+1)
        for d in [F(K,K+1),F(1,K*(K+1))]:
            assert all(x/K<=y<=K*x for x,y in [(d,q),(1-d,1-q)])
            for n in [1,2,3,8,32]:
                total=sum(d*(1-q)**j for j in range(n))
                assert total==d/q*(1-(1-q)**n)
                if d==F(1,K*(K+1)):assert 2*total/K<=F(2,K*K)
                cnt+=1
        eps=F(1,K**3);p=F(5,8)
        q1=p*K/(1-p+p*K);q2=p/(K*(1-p)+p)
        val=(1-q1)*(q2+(1-q2)*eps)
        assert val<=F(1,K*K)+eps/K
    checks['original_two_sided_obstructions']=cnt

    cnt=0
    for K in [F(1),F(3,2),F(2),F(7),F(128)]:
        c=K/(K+1)
        # Integrals of both affine segments, in exact arithmetic.
        integ=c*c/(2*K)+(1-c)*(1+1/(K+1))/2
        assert integ==1/(K+1)
        assert c/K==1-K+K*c
        assert c/K+K*(1-c)==1
        cnt+=1
    checks['two_sided_cdf_integrals_and_sharpness_density']=cnt

    fs=families(3);assert len(fs)==19
    states=list(product(range(3),repeat=3));vals=[F(0),F(1),F(2)]
    laws=[([F(1,3)]*3,[F(1,3)]*3,1),
          ([F(1,2),F(1,3),F(1,6)],[F(1,4),F(1,3),F(5,12)],3),
          ([F(1,4),F(1,2),F(1,4)],[F(1,2),F(1,4),F(1,4)],2)]
    cnt=0
    for D,Q,K in laws:
        assert all(d/K<=q<=K*d for d,q in zip(D,Q))
        for fam in fs:
            rhs=lhs=F(0)
            for vv in states:
                v=[vals[i] for i in vv];pv=D[vv[0]]*D[vv[1]]*D[vv[2]]
                rhs+=pv*opt(v,fam)
                for ss in states:
                    s=[vals[i] for i in ss];ps=Q[ss[0]]*Q[ss[1]]*Q[ss[2]]
                    allow=sum(1<<i for i in range(3) if v[i]>=s[i])
                    lhs+=pv*ps*opt(v,fam,allow)
            assert lhs>=rhs/(K+1)
            cnt+=1
    checks['L119_all_downward_closed_families_ties_loops']=cnt

    mats=[f for f in fs if matroid(f,3)];assert len(mats)==16
    cnt=0
    for fam in mats:
        for v in product([F(0),F(1),F(2)],repeat=3):
            for s in product([F(0),F(1),F(2)],repeat=3):
                allow=sum(1<<i for i in range(3) if v[i]>0 and v[i]>=s[i])
                rank=max(a.bit_count() for a in fam if a&allow==a)
                benchmark=opt(v,fam,allow)
                for order in permutations(range(3)):
                    rew=greedy(v,s,fam,order)
                    assert rew>=rank and 2*rew>=benchmark
                    cnt+=1
    checks['F119_every_order_on_all_three_label_matroids']=cnt

    # Finite uniform-matroid flag computation, even with no threshold rejections.
    cnt=0;n=5;r=2;eps=F(1,4);bits=list(product((0,1),repeat=n));expected=F(0)
    for s in bits:
        basis=sorted(range(n),key=lambda e:(-s[e],e))[:r]
        layers=[{basis[0]},set(range(n))-{basis[0]}]
        assert layers[0].isdisjoint(layers[1]) and set.union(*layers)==set(range(n))
        for v in bits:
            cap=sum(min(1,sum(v[e] for e in layer)) for layer in layers)
            expected+=mass(s,[eps]*n)*mass(v,[eps]*n)*cap
            assert cap<=sum(v[e] for e in basis[:-1])+1
            cnt+=1
    assert expected<=(r-1)*eps+1
    for r in range(3,65):
        n=r**3;mean=F(n,r);var=mean*(1-F(1,r))
        assert var/(mean-r)**2<=F(1,(r-1)**2)
    checks['sample_basis_flag_capacity_instances']=cnt

    # Enumerate selected-after-mask residuals over every family containing empty.
    cnt=0
    for omega in product([F(1,4),F(1,2),F(3,4)],repeat=3):
        for code in range(1,256,2):
            fam=[a for a in range(8) if code>>a&1];N=len(fam)
            expected=F(0)
            for ob in triples:
                omask=sum(1<<i for i,b in enumerate(ob) if b)
                z=max(sum(omega[i] for i in range(3) if a>>i&1)
                      for a in fam if a&omask==a)
                expected+=mass(ob,[1-u for u in omega])*z
            z=F(N-1,N+1)
            # A rational lower bound on log N; passing this is a stronger finite check.
            log_lower=2*sum(z**(2*j+1)/F(2*j+1) for j in range(30))
            assert expected<=1+log_lower
            cnt+=1
    checks['heterogeneous_adaptive_residual_families']=cnt

    # Exact integrated pivotal derivatives for all decreasing Boolean events on 3 bits.
    cnt=0
    for fam in fs:
        ev=lambda b:sum(1<<i for i,x in enumerate(b) if x) in fam
        for c in [[F(1,8)]*3,[F(1,4),F(1,2),F(3,4)]]:
            for depart in triples:
                t=F(1,2);delta=[max(F(0),t-x) if j else F(0) for x,j in zip(c,depart)]
                derivative=[F(0)]
                for i in range(3):
                    if not delta[i]:continue
                    others=[j for j in range(3) if j!=i]
                    def pivotal(b):
                        lo=[0]*3;hi=[0]*3
                        for j,x in zip(others,b):lo[j]=hi[j]=x
                        hi[i]=1
                        return ev(lo) and not ev(hi)
                    pp=event_poly(pivotal,[c[j] for j in others],[delta[j] for j in others])
                    derivative=poly_add(derivative,[delta[i]*x for x in pp])
                integ=sum(x/F(j+1) for j,x in enumerate(derivative))
                p=prob_event(ev,c);upper=prob_event(ev,[x+d for x,d in zip(c,delta)])
                h=prob_event(ev,[t if j else x for x,j in zip(c,depart)])
                assert p-upper==integ and h>=p-integ
                cnt+=1
    checks['exact_multiaffine_pivotal_integrals']=cnt

    cnt=0
    for theta in [F(1,17),F(1,5),F(1,2),F(4,5),F(16,17)]:
        for beta in [F(1,32),F(1,17),F(1,5),F(1,2)]:
            A=theta*beta/((1-theta)*(1-beta));B=beta
            assert (1-theta)*(1-beta)*A==theta*B==theta*beta
            assert (A<=1)==(beta<=1-theta)
            cnt+=1
    checks['biased_exchange_mass_balance']=cnt
    return {'status':'PASS','arithmetic':'Fraction and integers only','checks':checks,
            'scope':'finite diagnostics only; not universal proof or contribution certification'}


if __name__=='__main__':
    import json
    print(json.dumps(run(),indent=2,sort_keys=True))
