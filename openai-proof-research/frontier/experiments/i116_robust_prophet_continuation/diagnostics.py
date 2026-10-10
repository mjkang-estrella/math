"""Exact finite diagnostics for I116. No file writes or network; not universal proof."""
import sys
sys.dont_write_bytecode = True
from fractions import Fraction as F
from itertools import product, permutations


def mass(bits, rates):
    z=F(1)
    for b,p in zip(bits,rates): z*=p if b else 1-p
    return z


def families(n):
    return [tuple(a for a in range(1<<n) if f>>a&1)
            for f in range(1,1<<(1<<n))
            if all(not(f>>a&1) or all(f>>b&1 for b in range(1<<n) if b&a==b)
                   for a in range(1<<n))]


def opt(weights, family, allowed=None):
    if allowed is None: allowed=(1<<len(weights))-1
    return max(sum(w for i,w in enumerate(weights) if a>>i&1)
               for a in family if a&allowed==a)


def greedy(weights, family):
    a=0
    for i in sorted(range(len(weights)),key=lambda i:(-weights[i],i)):
        if weights[i]>0 and (a|(1<<i)) in family: a|=1<<i
    return a


def is_matroid(fam):
    return all(a.bit_count()>=b.bit_count() or
               any((a|(1<<i)) in fam for i in range(3) if b>>i&1 and not a>>i&1)
               for a in fam for b in fam)


def padd(a,b):
    return [ (a[i] if i<len(a) else 0)+(b[i] if i<len(b) else 0)
             for i in range(max(len(a),len(b))) ]


def pneg(a): return [-x for x in a]

def pmul(a,b):
    c=[F(0)]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        for j,y in enumerate(b): c[i+j]+=x*y
    return c


def det(a,b,c,d): return padd(pmul(a,d),pneg(pmul(b,c)))

def peval(a,u):
    z=F(0)
    for c in reversed(a): z=z*u+c
    return z


def run():
    checks={}
    triples=list(product((0,1),repeat=3))
    cnt=0
    for m in range(9):
        K=2**m;t=F(1,2**140*K**12);a=F(3,4)*(1-t);p=1-a/2
        for r in [F(1,K),F(1),F(K)]:
            Z=1-p+p*r
            law={b:mass(b,[F(1,2),F(1,4),t])*(r if any(b) else 1)/Z for b in triples}
            pr=lambda pred:sum(v for b,v in law.items() if pred(b))
            assert sum(law.values())==1
            h0=pr(lambda b:not b[0]);h00=pr(lambda b:not b[0] and not b[1])
            assert h0==(a+(1-a)*r)/(2*Z)
            assert pr(lambda b:b[0])==r/(2*Z)
            assert pr(lambda b:not b[0] and b[1])/h0==(r/4)/(a+(1-a)*r)
            assert pr(lambda b:not b[0] and b[2])/h0==t*r/(a+(1-a)*r)
            assert pr(lambda b:not b[0] and not b[1] and b[2])/h00==t*r/(1-t+t*r)
            cnt+=1
        cm=t/(K*(1-t)+t);cp=K*t/(1-t+K*t)
        assert cp/cm==K*K*(1-t+t/K)/(1-t+K*t)
        assert cp/cm>=F(K*K,3)
        D=[F(K,K+1),F(1,K+1)];Q=list(reversed(D));values=[F(2),F(7)]
        joint_d=joint_u=F(0)
        for j in range(2):
            r=Q[j]/D[j];Z=1-p+p*r
            for b in triples:
                joint=D[j]*mass(b,[F(1,2),F(1,4),t])*(r if any(b) else 1)
                if not b[0] and b[1]: joint_d+=values[j]*joint
                if not any(b): joint_u+=values[j]*joint
        assert joint_d==sum(w*q for w,q in zip(values,Q))/8
        assert joint_u==(1-p)*sum(w*d for w,d in zip(values,D))
    checks['exact_posterior_rates']=cnt
    checks['moment_cancellation_and_guard_spread']=9

    cnt=0
    for K in [2,4,8,16,32,64]:
        eps=F(1,K**3)
        for p in [F(5,8),F(2,3),F(3,4)]:
            q=[p*K/(1-p+p*K),(p/K)/(1-p+p/K)]
            val=F(0)
            for mask in product((0,1),repeat=2):
                rewards=[]
                threshold=max([w for w,b in zip([F(1),eps],mask) if b] or [F(0)])
                for order in permutations(range(2)):
                    reward=F(0)
                    for i in order:
                        if not mask[i] and [F(1),eps][i]>threshold:
                            reward=[F(1),eps][i];break
                    rewards.append(reward)
                val+=mass(mask,q)*min(rewards)
            assert val==(1-q[0])*(q[1]+(1-q[1])*eps)
            assert val<=F(1,K*K)+eps/K<=F(2,K*K)
            cnt+=1
    checks['conditional_maximum_order_enumerations']=cnt

    # L116: enumerate all 19 nonempty downward-closed families on 3 labels,
    # including loops/nonmatroids, and rational Bernoulli laws with ties.
    fs=families(3);assert len(fs)==19
    bits=list(product((0,1),repeat=3));cnt=0
    for K in [1,2,4]:
        for d,q in product([F(1,4),F(1,2),F(3,4)],repeat=2):
            if not all(dd/K<=qq<=K*dd for dd,qq in [(d,q),(1-d,1-q)]):continue
            for weights in [(1,2,3),(2,2,2)]:
                for fam in fs:
                    original=retained=F(0)
                    for vb in bits:
                        v=[w*b for w,b in zip(weights,vb)];vp=mass(vb,[d]*3)
                        original+=vp*opt(v,fam)
                        for sb in bits:
                            s=[w*b for w,b in zip(weights,sb)];sp=mass(sb,[q]*3)
                            allowed=sum(1<<i for i in range(3) if v[i]>=s[i])
                            retained+=vp*sp*opt(v,fam,allowed)
                    assert retained>=original/(2*K)
                    cnt+=1
    checks['local_filter_downward_closed_instances']=cnt

    # Non-Bernoulli, tied and multi-valued local filter checks on two labels.
    fs2=families(2);cnt=0
    laws=[tuple(F(v,6) for v in (i,j,6-i-j)) for i in range(1,5) for j in range(1,6-i)]
    states=list(product(range(3),repeat=2));values=[0,1,5]
    for D,Q in product(laws,repeat=2):
        K=max([F(1)]+[q/d for q,d in zip(Q,D)])
        for fam in fs2:
            lhs=rhs=F(0)
            for vs in states:
                v=[values[i] for i in vs];pv=D[vs[0]]*D[vs[1]]
                rhs+=pv*opt(v,fam)
                for ss in states:
                    s=[values[i] for i in ss];ps=Q[ss[0]]*Q[ss[1]]
                    allow=sum(1<<i for i in range(2) if v[i]>=s[i])
                    lhs+=pv*ps*opt(v,fam,allow)
            assert lhs>=rhs/(2*K)
            cnt+=1
    checks['local_filter_multivalued_instances']=cnt

    mats=[f for f in fs if is_matroid(f)];cnt=0
    for fam in mats:
        for ds,qs,K in [([F(1,4),F(1,2),F(3,4)],[F(1,2)]*3,2),([F(1,2)]*3,[F(1,2)]*3,1)]:
            pe=[F(0)]*3;qe=[F(0)]*3
            for sb in bits:
                s=[(i+1)*sb[i] for i in range(3)];ps=mass(sb,qs)
                b=greedy(s,fam)
                for e in range(3):
                    if b>>e&1:qe[e]+=ps
                for vb in bits:
                    pv=mass(vb,ds)
                    for e in range(3):
                        w=s.copy();w[e]=(e+1)*vb[e]
                        if greedy(w,fam)>>e&1:pe[e]+=ps*pv
            for e in range(3): assert qe[e]/K<=pe[e]<=K*qe[e]
            for A in range(8):
                rank=max(a.bit_count() for a in fam if a&A==a)
                assert sum(pe[e] for e in range(3) if A>>e&1)<=K*rank
            cnt+=1
    checks['sample_greedy_matroid_rank_budgets']=cnt
    c1=c2=both=F(0)
    for sb,vb in product(bits,repeat=2):
        p=F(1,64);x=vb[0] and not sb[1] and not sb[2];y=vb[1] and not sb[2]
        c1+=p*x;c2+=p*y;both+=p*(x and y)
    assert (c1,c2,both)==(F(1,8),F(1,4),F(1,16)) and both!=c1*c2
    assert 3*F(1,2)>1
    checks['activation_dependence_and_conditional_budget_counterexample']=1

    cnt=0
    for K in [1,2,4,8,16,32]:
        q=F(1,K+1)
        for d in [F(K,K+1),F(1,K*(K+1))]:
            assert all(dd/K<=qq<=K*dd for dd,qq in [(d,q),(1-d,1-q)])
            for n in [1,2,5,10,32]:
                count=sum(d*(1-q)**j for j in range(n))
                assert count==d/q*(1-(1-q)**n)
                if d==F(1,K*(K+1)):assert 2*count/K<=F(2,K*K)
                cnt+=1
    checks['two_sided_candidate_thinning_instances']=cnt

    cnt=0
    for a,b in product([F(0),F(1,2),F(1)],repeat=2):
        for r0,r1 in product([-2,0,3],repeat=2):
            P=[[a,1-a],[b,1-b]];Q=1
            for row in P:
                for x in row:Q*=x.denominator
            M=[[[Q*(int(i==j)-P[i][j]),Q*P[i][j]] for j in range(2)] for i in range(2)]
            R=[[F(0),F(Q*r0)],[F(0),F(Q*r1)]]
            den=det(M[0][0],M[0][1],M[1][0],M[1][1])
            nums=[det(R[0],M[0][1],R[1],M[1][1]),det(M[0][0],R[0],M[1][0],R[1])]
            W=max(1,abs(r0),abs(r1));A0=2*(Q*(3+W))**2;H=(W+4)*A0;N=32*H*H;u=F(1,N)
            assert all(sum(abs(x) for x in poly)<=A0 for poly in [den]+nums)
            d=N**2*peval(den,u);assert d.denominator==1 and d and abs(d)<=A0*N**2
            vals=[peval(num,u)/peval(den,u) for num in nums]
            assert all((v*d).denominator==1 for v in vals)
            gap=F(1,A0*N**3);eps=gap/8
            expr=[u*w+(1-u)*v for w,v in product([-2,0,3],vals)]
            for x,y in product(expr,repeat=2): assert x==y or abs(x-y)>=gap
            approx=[u*w+(1-u)*(v+(eps if j==0 else -eps)) for w in [-2,0,3] for j,v in enumerate(vals)]
            assert expr[max(range(len(expr)),key=lambda i:approx[i])]==max(expr)
            ell=next(i for i,c in enumerate(den) if c)
            assert all(all(c==0 for c in num[:ell]) for num in nums)
            gains=[num[ell]/den[ell] for num in nums]
            expected=[F(r0),F(r1)] if a==1 and b==0 else [(b*r0+(1-a)*r1)/(b+1-a)]*2
            assert gains==expected
            cnt+=1
    checks['stochastic_pair_common_gaps_and_exact_gains']=cnt
    return {'status':'PASS','arithmetic':'Fraction and integers only','scope':'finite diagnostics only; no universal-proof or novelty certification','checks':checks}


if __name__=='__main__':
    import json
    print(json.dumps(run(),indent=2,sort_keys=True))
