"""Exact finite diagnostics only; no universal-proof or novelty certification.
Import and execution are read-only. Run with python -B to prevent bytecode.
"""
import sys
sys.dont_write_bytecode = True
from fractions import Fraction as F
from itertools import product, permutations
import json


def mass(bits, rates):
    ans = F(1)
    for b, q in zip(bits, rates):
        ans *= q if b else 1-q
    return ans


def run():
    counts = {}
    triples = list(product((0, 1), repeat=3))
    kernels = 0
    for m in range(9):
        K = 2**m
        t = F(1, 2**140*K**12)
        rates = (F(1, 2), F(1, 4), t)
        p = 1-mass((0,0,0), rates)
        for r in (F(1,K), F(1), F(K)):
            z = 1-p+p*r
            law = {b:mass(b,rates)*(r if any(b) else 1)/z for b in triples}
            assert sum(law.values()) == 1
            prob = lambda f: sum(v for b,v in law.items() if f(b))
            h = prob(lambda b:b[0])
            assert F(1,2*K) <= h <= 1-F(1,2*K)
            assert p/K <= prob(any) <= 1-(1-p)/K
            for hb in (0,1):
                ph = prob(lambda b:b[0]==hb)
                assert prob(lambda b:b[0]==hb and b[1])/ph >= F(1,4*K)
                assert prob(lambda b:b[0]==hb and b[2])/ph <= K*t
                if hb==0:
                    assert prob(lambda b:b[0]==0 and (b[1] or b[2]))/ph <= 1-F(1,2*K)
                for db in (0,1):
                    phd = prob(lambda b:b[:2]==(hb,db))
                    c = prob(lambda b:b[:2]==(hb,db) and b[2])/phd
                    assert t/K <= c <= K*t
                    if hb or db:
                        assert c == t
            kernels += 1
    counts['posterior_kernels'] = kernels

    # All 20 increasing Boolean events on three coordinates, including constants.
    events = [tuple((code>>i)&1 for i in range(8)) for code in range(256)]
    events = [a for a in events if all(not a[i] or a[j]
              for i in range(8) for j in range(8) if i & j == i)]
    assert len(events)==20
    bit = lambda x,i:(x>>i)&1
    hybrid_checks=0
    for rates in ((F(1,4),F(1,2),F(3,4)), (F(2,3),F(1,3),F(4,5))):
        for s in (min(rates), min(rates)/2):
            pc = [mass([bit(x,i) for i in range(3)],rates) for x in range(8)]
            pt = [mass([bit(x,i) for i in range(3)],(s,)*3) for x in range(8)]
            for a in events:
                fail = sum(pc[x] for x in range(8) if not a[x])
                for order in permutations(range(3)):
                    joint = F(0)
                    for x in range(8):
                        queried=[]
                        compatible=list(range(8))
                        for i in order:
                            if len({a[y] for y in compatible})==1:
                                break
                            queried.append(i)
                            compatible=[y for y in compatible if bit(y,i)==bit(x,i)]
                        # Complete transcript determines ordinary event.
                        assert len({a[y] for y in compatible})==1
                        if a[x]:
                            continue
                        for y in range(8):
                            h=x
                            for i in queried:
                                h=(h & ~(1<<i)) | (bit(y,i)<<i)
                            if not a[h]:
                                joint += pc[x]*pt[y]
                    assert joint >= fail*fail
                    hybrid_checks+=1
    counts['dominated_hybrid_events_query_orders_rates'] = hybrid_checks

    for m in range(65):
        K=2**m
        B=2**32*K**4
        kap=2**100*K**8
        t=F(1,2**140*K**12)
        s=t/K
        gamma=F(1,2**16*K)
        delta=F(1,2**28*K**3)
        eps=F(1,kap)+2*delta+K*t*kap+(1+K*t*kap)/(B-1)
        assert eps <= F(1,2**25*K**3) <= gamma/(16*K*K)
        # ln(2)<=1; these stronger integer inequalities verify the stated bounds.
        assert 100+8*m <=108*K
        assert F(1000*(100+8*m),kap) <= delta/(4*K)
        assert delta*kap/(4*K) >= 28+3*m
        assert 4*K*K*s*gamma <= 1
        assert s*gamma/(32*K*kap*B)==F(1,2**293*K**27)
        assert s*gamma/(128*K*kap*B)==F(1,2**295*K**27)
    counts['parameter_instances_m_0_through_64']=65

    calibration=0
    for D,Q,K in (((F(1,4),F(3,4)),(F(1,2),F(1,2)),2),
                  ((F(3,4),F(1,4)),(F(1,2),F(1,2)),2),
                  ((F(1,3),F(2,3)),(F(1,4),F(3,4)),2)):
        retained=[Q[i]*(D[i]/Q[i]/K) for i in range(2)]
        assert sum(retained)==F(1,K)
        assert [x*K for x in retained]==list(D)
        calibration+=1
    counts['calibration_identities']=calibration

    prefix=0
    for n in range(1,7):
        for allowed in range(1<<n):
            for q in (F(1,2),F(1,8),F(1)):
                probs=[]
                live=F(1)
                for j in range(n):
                    pj=live*q if bit(allowed,j) else F(0)
                    probs.append(pj)
                    live-=pj
                assert sum(probs)<=1
                geometric=sum(sum(F(2)**(j-h)*probs[j] for j in range(h+1))
                              for h in range(n))
                assert geometric <=2*sum(probs)
                for h in range(n):
                    # Enumerate actual independent Bernoulli values up to the cutoff.
                    reward=F(0)
                    for x in range(1<<(h+1)):
                        px=mass([bit(x,i) for i in range(h+1)],(q,)*(h+1))
                        chosen=next((j for j in range(h+1) if bit(x,j) and bit(allowed,j)),None)
                        if chosen is not None:
                            reward+=px*F(2)**(chosen-n+1)
                    assert reward==sum(F(2)**(j-n+1)*probs[j] for j in range(h+1))
                prefix+=1
    counts['rank_one_prefix_policy_instances']=prefix
    return {'status':'PASS','arithmetic':'fractions.Fraction and integers only',
            'scope':'finite diagnostics, not proof or substantiality certification','checks':counts}

if __name__=='__main__':
    print(json.dumps(run(),indent=2,sort_keys=True))
