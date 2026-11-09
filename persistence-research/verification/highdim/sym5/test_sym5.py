"""Deep-pin positive controls and certificate-level mutation/tamper tests."""
import sys
sys.dont_write_bytecode = True
import collections
import importlib.util
import json
import math
import pathlib
import random

H = pathlib.Path(__file__).resolve().parent
sys.path.insert(0, str(H))
from gen_sym import Generator
from check_sym5 import Checker
from coverage_distinct import finite_partition_test, finite_position_test

def write(path, meta, node):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(meta)+'\n'+json.dumps(node)+'\n')

def rejected(path, fragment):
    try:
        Checker(path, 0).run()
    except ValueError as e:
        assert fragment in str(e), str(e)
        return str(e)
    raise AssertionError('accepted tamper: '+str(path))

def make_meta(g, M, pt):
    return dict(k='meta', format='nd-sym', version=1, domain='unordered',
                scope='class', groups=[list(x) for x in g.groups], K=g.K,
                qmin=g.qmin, dim=g.dim, pin2=g.pin2, pin_digits=g.pin_digits,
                root={'m':M, 'r':g.nested(g.key(pt, M))})

def planted(t, k, a, w, coefficients=(9,18)):
    q=max(k,t+1)
    qs=tuple(range(q,q+len(coefficients)))
    L=q+len(coefficients)
    N=2**t*3**a*7**w
    K=N-10**L-sum(c*10**e for c,e in zip(coefficients,qs))
    if K<=0 or K%5==0 or (K & -K)!=2**t: return None
    return K,q,(L,)+qs,N

def main():
    rng=random.Random(53041)
    controls=checks=pairs=0
    # k<t0, k=t0, k>t0; q=qmin and L=qmin for the dimension-one controls.
    edges=collections.Counter()
    for k in (1,2,3,4,5,6):
        for t in (0,1,2,3,4,6,8):
            for cs in ((),(9,18)):
                for use_pin2 in (False,True):
                    a=35+rng.randrange(8); w=8+rng.randrange(6)
                    spec=planted(t,k,a,w,cs)
                    assert spec is not None
                    K,q,pt,N=spec
                    q=max(q,t+3) if use_pin2 else q
                    # Replant if pin2 raises the floor.
                    qs=tuple(range(q,q+len(cs))); pt=(q+len(cs),)+qs
                    while N<=10**pt[0]+sum(c*10**v for c,v in zip(cs,qs)):
                        a+=1;N*=3
                    K=N-10**pt[0]-sum(c*10**v for c,v in zip(cs,qs))
                    g=Generator(cs,K,q,pin_digits=k,pin2=use_pin2,supply=[])
                    D=5**k*2**max(k-t,0)
                    assert (N//2**t-K//2**t)%D==0
                    A,W=g.pin_periods
                    assert (a%A,w%W) in g.pin_pairs
                    path=H/'controls'/'context.jsonl'
                    meta=make_meta(g,1,pt)
                    write(path,meta,dict(id=0,p=-1,k='l',m=1,r=meta['root']['r'],x={'prime':11}))
                    c=Checker(path,0)
                    assert c.decimal_periods==g.pin_periods
                    assert set(c.pin_representatives)==set(g.pin_pairs)
                    # Independent direct Cartesian enumeration is affordable at k<=3.
                    if k<=3:
                        expected={(i,j) for i in range(A) for j in range(W)
                                  if pow(3,i,D)*pow(7,j,D)%D==K//2**t%D
                                  and (not g.pin2 or pow(3,i,8)*pow(7,j,8)%8==K//2**t%8)}
                        assert expected==set(g.pin_pairs)
                    pairs+=len(g.pin_pairs)
                    for M in (1,2,6,12,30,42,126,210):
                        r=g.key(pt,M); cr=c.key(pt,M)
                        ga,gw=g.sig(r,M)
                        for p in (11,13,19,31,37,41,43,73):
                            d,o3,o7=(pow_order(b,p) for b in (10,3,7))
                            e=(p,d,o3,o7,math.lcm(o3,o7))
                            assert not g.forbidden(N%p,e,ga,gw)
                            if M%d==0:
                                assert not g.test(e,r,ga,gw)
                            assert not c.killed(p,cr,M)
                            checks+=1
                    controls+=1
                    edges['k<t0' if k<t else 'k=t0' if k==t else 'k>t0']+=1
    # Reject over-pinning before constructing any cycles.
    bad=dict(meta,pin_digits=meta['qmin']+1)
    over=H/'tamper'/'k_gt_qmin.jsonl'
    write(over,bad,dict(id=0,p=-1,k='l',m=1,r=bad['root']['r'],x={'prime':11}))
    over_result=rejected(over,'decimal pin depth')
    try: Generator([],1,4,supply=[],pin_digits=5)
    except AssertionError: pass
    else: raise AssertionError('generator accepted k>qmin')

    # Deliberately UNSOUND mutation: apply the 2^k modulus to Y, forgetting
    # to divide its 2-part by 2^t0. Produce a false kill of a planted solution.
    namespace={'__file__':str(H/'gen_sym.py'),'__name__':'wrong_modulus_generator'}
    source=(H/'gen_sym.py').read_text()
    correct='mod=5**self.pin_digits*2**max(0,self.pin_digits-self.t0)'
    assert correct in source
    exec(compile(source.replace(correct,'mod=5**self.pin_digits*2**self.pin_digits'),
                 'WRONG_MODULUS_MUTATION','exec'),namespace)
    K,q,pt,N=planted(2,4,38,10,(9,))
    good=Generator([9],K,q,pin_digits=4,pin2=False,supply=[])
    mutant=namespace['Generator']([9],K,q,pin_digits=4,pin2=False,supply=[])
    p=11;M=math.lcm(6*3**38*7**10,pow_order(10,p))
    r=good.key(pt,M);a,w=good.sig(r,M)
    e=(p,pow_order(10,p),pow_order(3,p),pow_order(7,p),math.lcm(pow_order(3,p),pow_order(7,p)))
    assert not good.test(e,r,a,w) and mutant.test(e,r,a,w)
    meta=make_meta(good,M,pt)
    wrong=H/'tamper'/'misdivided_modulus_false_kill.jsonl'
    node=dict(id=0,p=-1,k='l',m=M,r=meta['root']['r'],x={'prime':p})
    write(wrong,meta,node)
    mutation_result=rejected(wrong,'false prime kill')
    # Same genuine point, correctly recorded as an exact size leaf, must pass.
    positive=H/'controls'/'genuine_size_solution.jsonl'
    node['x']={'sz':[a[0],w[0]],'sol':[list(pt)]}
    write(positive,meta,node)
    size_result=Checker(positive,pt[0]).run()
    assert list(pt) in size_result['solutions']
    out=dict(result='PASS',planted_instances=controls,class_prime_tests=checks,
             wrong_kills=0,edge_cases=dict(edges),enumerated_pairs=pairs,
             k_gt_qmin_rejected=over_result,misdivided_modulus_rejected=mutation_result,
             genuine_size_solution=size_result,
             partition=finite_partition_test(),position_partition=finite_position_test())
    # context.jsonl is only a constructor fixture, deliberately not a certificate.
    (H/'controls'/'context.jsonl').unlink()
    (H/'test_results.json').write_text(json.dumps(out,indent=1)+'\n')
    print(json.dumps({k:v for k,v in out.items() if k not in ('genuine_size_solution',)}))

def pow_order(b,p):
    z=b%p;n=1
    while z!=1: z=z*b%p;n+=1
    return n

if __name__=='__main__': main()
