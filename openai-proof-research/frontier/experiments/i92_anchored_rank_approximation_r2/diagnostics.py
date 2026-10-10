#!/usr/bin/env python3
"""Independent finite checks. No files written; not a universal proof."""
from fractions import Fraction as F
from itertools import permutations, product
import json

def run():
    cases=checks=loopcases=ties=zeros=signed=0
    # Direct path enumeration, not the author's capped-record recurrence.
    for nv in range(1,4):
        for ps in product(list(permutations(range(nv))),repeat=2):
            inc=[]; out=[[] for _ in range(nv)]
            for perm in ps:
                for x,y in enumerate(perm):
                    e=len(inc);inc.extend([(x,y,e+1),(y,x,e)])
                    out[x].append(e);out[y].append(e+1)
            for flags in product((0,1),repeat=2*nv):
                for cross in (0,1):
                    for n in (2,3):
                        def paths(e,j,remaining):
                            x,y,rev=inc[e]
                            if not flags[2*x+j]:return []
                            ans=[]
                            for k in range(2):
                                if not flags[2*y+k] or (j!=k and not cross):continue
                                ans.append(1)
                                if remaining>1:
                                    for f in out[y]:
                                        if f!=rev:
                                            ans.extend(1+t for t in paths(f,k,remaining-1))
                            return ans
                        rec={(e,j):max([0]+paths(e,j,n)) for e in range(len(inc)) for j in range(2)}
                        bad={(x,j):max(rec[e,j] for e in out[x])==n for x in range(nv) for j in range(2)}
                        ex={(e,j):bad[inc[e][0],j] or all(rec[e,j]>rec[f,j] for f in out[inc[e][0]] if f!=e) for e in range(len(inc)) for j in range(2)}
                        for x in range(nv):
                            for j in range(2):
                                if not bad[x,j]:
                                    assert sum(ex[e,j] for e in out[x])<=1
                                    vals=[rec[e,j] for e in out[x]]
                                    zeros+=max(vals)==0;ties+=vals.count(max(vals))>1
                            for mu in ((F(2),F(-1)),(F(-3,2),F(5,2)),(F(0),F(0))):
                                tv=sum(map(abs,mu));w=sum(abs(mu[j])*bad[x,j] for j in range(2))
                                avg=sum(abs(mu[j])*ex[e,j] for e in out[x] for j in range(2))/4
                                assert avg<=tv/4+F(3,4)*w;signed+=1
                        for e,(x,y,rev) in enumerate(inc):
                            assert inc[rev]==(y,x,e)
                            for j,k in product(range(2),repeat=2):
                                if flags[2*x+j] and flags[2*y+k] and (j==k or cross):
                                    assert ex[e,j] or ex[rev,k];checks+=1
                        cases+=1;loopcases+=any(x==y for x,y,_ in inc)
    # A regular 9-vertex fixture whose compatible subgraph is a four-leaf star.
    # Unlike the tiny permutation fixtures, this exercises positive good records,
    # positive ties at the root, and the exact n=2 bad / n=3 good boundary.
    undirected=[(0,j) for j in range(1,5)]
    undirected += [(j,5+k) for j in range(1,5) for k in range(4) if k!=j-1]
    undirected += [(5,6),(7,8)]
    inc=[];out=[[] for _ in range(9)]
    for x,y in undirected:
        e=len(inc);inc.extend([(x,y,e+1),(y,x,e)]);out[x].append(e);out[y].append(e+1)
    assert all(len(es)==4 for es in out)
    fixture=[]
    for n in (2,3,4):
        def walks(e,remaining):
            x,y,rev=inc[e]
            if x>4 or y>4:return []
            ans=[1]
            if remaining>1:
                for f in out[y]:
                    if f!=rev:ans.extend(1+t for t in walks(f,remaining-1))
            return ans
        rec=[max([0]+walks(e,n)) for e in range(len(inc))]
        bad=[max(rec[e] for e in out[x])==n for x in range(9)]
        ex=[bad[x] or all(rec[e]>rec[f] for f in out[x] if f!=e) for e,(x,y,rev) in enumerate(inc)]
        assert all(rec[e]==1 for e in out[0]) and not bad[0] and not any(ex[e] for e in out[0])
        assert all(bad[x]==(n==2) for x in range(1,5))
        for e,(x,y,rev) in enumerate(inc):
            if x<=4 and y<=4:assert ex[e] or ex[rev]
        fixture.append(dict(n=n,root_records=[rec[e] for e in out[0]],bad_leaves=sum(bad[1:5]),exceptional_leaf_counts=[sum(ex[e] for e in out[x]) for x in range(1,5)]))
    # Select the observable AFTER choosing both distributions, maximizing the gap.
    probs=[tuple(F(x,4) for x in a) for a in product(range(5),repeat=3) if sum(a)==4]
    adaptive=clipped=0
    for P,Q in product(probs,repeat=2):
        tv=sum(abs(p-q) for p,q in zip(P,Q))/2
        g=[F(7) if p>q else F(0) for p,q in zip(P,Q)]
        assert sum((p-q)*v for p,q,v in zip(P,Q,g))==7*tv;adaptive+=1
        for weights in product((F(0),F(1,2),F(20)),repeat=3):
            cap=[min(F(7),w) for w in weights]
            assert sum((p-q)*v for p,q,v in zip(P,Q,cap))<=7*tv;clipped+=1
    # Explicit failure of dropping the cap in a putative V*TV transfer.
    P=(F(1,10),F(9,10));Q=(F(0),F(1));raw=(F(100),F(0))
    raw_gap=sum((p-q)*v for p,q,v in zip(P,Q,raw))
    assert raw_gap>F(1,10) and sum((p-q)*min(F(1),v) for p,q,v in zip(P,Q,raw))==F(1,10)
    # Auerbach basis with overlapping signed supports in l1^3.
    u=(F(1,2),F(1,2),F(0));v=(F(1,2),F(-1,2),F(0));env=tuple(abs(x)+abs(y) for x,y in zip(u,v))
    envelope_checks=0
    for a,b in product(range(-4,5),repeat=2):
        w=tuple(a*x+b*y for x,y in zip(u,v));norm=sum(map(abs,w))
        assert norm==max(abs(a),abs(b)) and sum(env)==2
        assert all(abs(x)<=norm*z for x,z in zip(w,env));envelope_checks+=1
    diffuse=[]
    for N in (2,7,32,257):
        coeff=tuple(F((-1)**j,N) for j in range(N))
        assert sum(map(abs,coeff))==1
        augmented=(-sum(coeff),)+coeff
        assert sum(augmented)==0
        for a in (F(-3),F(0),F(5,2)):
            mu=(F(1)+a*augmented[0],)+tuple(a*x for x in augmented[1:])
            assert sum(mu)==1
        diffuse.append(dict(N=N,one_dimensional_envelope_mass=1,tail_mass_outside_half=str(F(N-N//2,N))))
    constants=[];radial=0
    # Radial records in an ACTUAL source-compatible colored tree ball.
    # The report proves occurrence by the source local limit, not by this loop.
    for p in range(1,9):
        L=10*p;R=30*p;K=10*p*(R+1);D=K+2*L+5;B=4*R+D;V=1+4*p*B;delta=20*V+2
        theta=F(3,8)-F(2*p,4*L)-F(V,delta)-F(1,40)
        assert theta>F(1,4) and theta-F(1,16)>F(3,16)
        assert F(2*p*R+1,K)<=F(1,5) and R>2*L and D-4==K+2*L+1
        q=D-4;n=2*q+1
        for t in range(q+1):
            away=q-t;toward=q+t if t else q
            assert toward<n and away<n
            assert (toward>away)==(t>0)
            if t<q:
                child_toward=q+t+1
                assert child_toward>q-t-1
                assert child_toward==1+toward
            radial+=1
        constants.append(dict(p=p,V=V,delta=delta,theta=str(theta),tree_compatible_radius=q,cutoff=n))
    return dict(status='PASS_FINITE_DIAGNOSTICS_ONLY',direct_path_cases=cases,endpoint_checks=checks,loop_cases=loopcases,zero_good_records=zeros,tied_good_records=ties,positive_record_fixture=fixture,signed_average_checks=signed,adaptive_tv_extremizers=adaptive,clipped_tv_checks=clipped,unclipped_counterexample_gap=str(raw_gap),overlapping_envelope_checks=envelope_checks,diffuse=diffuse,radial_source_formula_checks=radial,constants=constants)
if __name__=='__main__':print(json.dumps(run(),indent=2,sort_keys=True))
