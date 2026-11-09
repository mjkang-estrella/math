#!/usr/bin/env python3
"""Positive, tamper, and orbit-partition tests. All output stays under sym/."""
import collections
import copy
import itertools
import json
import math
import pathlib
import sys
sys.dont_write_bytecode=True
HERE=pathlib.Path(__file__).resolve().parent
sys.path.insert(0,str(HERE))
from gen_sym import Generator,valuation
from check_sym import Checker,verify_finite_box
from run_experiments import save

LEVEL1=[12,14,15,16,18,21,24,32,42,81,112,14112,111132]
LEVEL2=[27,28,35,36,48,63,64,72,84,126,128,135,144,162,192,216,224,243,315,324,432,441,1134,1176,1323,1372,1728,2187,4116,13122,131712,33718272]


def factor(n):
    exps=[]
    for p in (2,3,5,7):
        e=0
        while n%p==0: n//=p;e+=1
        exps.append(e)
    assert n==1
    return exps


def positives():
    # Smooth lattice generation is separate from both position-box enumerators.
    vals=set()
    for a in range(30):
        for b in range(19):
            for c in range(13):
                for d in range(11):
                    n=2**a*3**b*5**c*7**d
                    if n<10**9: vals.add(n)
    l1=sorted(n for n in vals if n>=10 and 1<=math.prod(map(int,str(n)))<=9)
    l2=sorted(n for n in vals if math.prod(map(int,str(n))) in LEVEL1)
    assert l1==LEVEL1,(l1,LEVEL1)
    assert l2==LEVEL2,(l2,LEVEL2)
    specs=[]; checked=[]; classes=[]; finite_floor=[]
    for n in LEVEL1+LEVEL2:
        digs=list(map(int,str(n)[::-1]))
        S=sum((d-1)*10**q for q,d in enumerate(digs[:3]))
        pairs=sorted((9*(d-1),q) for q,d in enumerate(digs) if q>=3 and d!=1)
        cs=tuple(c for c,q in pairs); point=(len(digs),)+tuple(q for c,q in pairs)
        K=9*S-1; B=max(8,len(digs))
        five=factor(n)[2]>0
        found=set()
        # Generator-side box enumerates labelled permutations, then canonicalizes.
        for L in range(1,B+1):
            for qs in itertools.permutations(range(3,L),len(cs)):
                if any(cs[i]==cs[i+1] and qs[i]>=qs[i+1] for i in range(len(cs)-1)): continue
                X=10**L+K+sum(c*10**q for c,q in zip(cs,qs))
                if X<=0: continue
                y=X
                for p in ((2,3,5,7) if five else (2,3,7)):
                    while y%p==0: y//=p
                if y==1: found.add((L,)+qs)
        spec={'label':'COMPUTED','member':n,'level':1 if n in LEVEL1 else 2,'S_low':S,
              'K':K,'coefs':cs,'qmin':3,'Lmax':B,'required_point':point,
              'allowed_primes':[2,3,5,7] if five else [2,3,7],
              'solutions':[list(p) for p in sorted(found)]}
        checked.append(verify_finite_box(spec)); specs.append(spec)
        # Replay actual slicing. Some members lie BELOW the required final floor.
        free=list(pairs); floors=[3]*len(free); K2=K
        while True:
            t=valuation(K2,2)
            i=next((i for i,v in enumerate(floors) if v<=t),None)
            if i is None: break
            c,q=free[i]
            if q<=t:
                K2+=c*10**q;free.pop(i);floors.pop(i)
            else: floors[i]=t+1
        qmin=max(3,valuation(K2,2)+1)
        pt=(len(digs),)+tuple(q for c,q in free)
        if five or pt[0]<qmin or any(q<qmin for q in pt[1:]):
            finite_floor.append({'member':n,'K':K2,'qmin':qmin,'point':pt,'five_mode':five})
            continue
        a,w=factor(9*n)[1],factor(9*n)[3]
        M=6*3**max(0,a-1)*7**w
        g=Generator([c for c,q in free],K2,qmin,seconds=20)
        r=g.key(pt,M)
        g.run((),root=(r,M))
        fn=HERE/'controls'/f'member_{n}.jsonl'
        g.write(fn,scope='class',extra={'member':n,'original_configuration':[S,list(cs)]})
        check=Checker(fn,max(8,len(digs))).run()
        assert list(pt) in check['solutions']
        classes.append({'member':n,'file':str(fn.relative_to(HERE)),'check':check})
    save(HERE/'positive_boxes.json',specs)
    return {'label':'COMPUTED','smooth_lattice_bound':10**9,'level1':l1,'level2':l2,
            'finite_boxes':checked,'exact_class_certificates':classes,'below_floor_or_five':finite_floor}


def partition():
    records=[]
    for coefs in ([9,9,9],[9,9,54,54],[9,18,54],[]):
        g=Generator(coefs,89,3)
        g.new(g.zero(),1,-1)
        g.nodes[0].update(k='l',x={'prime':11})
        spec=HERE/'tamper/partition_spec.jsonl'
        spec.parent.mkdir(exist_ok=True)
        g.write(spec)
        checker=Checker(spec,10)
        for M in (1,2,3):
            parents={g.key(p,M) for p in itertools.product(range(M),repeat=len(coefs)+1)}
            for f in (2,3):
                expected=collections.defaultdict(set)
                for pt in itertools.product(range(M*f),repeat=len(coefs)+1):
                    expected[g.key(pt,M)].add(g.key(pt,M*f))
                for r in parents:
                    got=list(g.lifts_of(r,M,f))
                    assert len(got)==len(set(got))==g.lift_count(r,f)
                    assert set(got)==expected[r]
                    def nested(flat):
                        z=g.nested(flat)
                        return (z[0],)+tuple(tuple(v) for v in z[1:])
                    independently=list(checker.children(nested(r),M,M*f))
                    assert len(independently)==len(set(independently))
                    assert set(independently)=={nested(v) for v in expected[r]}
                records.append({'coefs':coefs,'M':M,'factor':f,'parents':len(parents),
                                'labelled_children':(M*f)**(len(coefs)+1),'orbit_children':sum(map(len,expected.values()))})
    return records


def tamper():
    source=HERE/'smoke.jsonl'
    raw=[json.loads(s) for s in source.read_text().splitlines()]
    positive=HERE/'controls/member_111132.jsonl'
    pr=[json.loads(s) for s in positive.read_text().splitlines()]
    mutations=[]
    def add(name,base,mut):
        r=copy.deepcopy(base);mut(r);mutations.append((name,r))
    add('missing-lifts',raw,lambda r:r[1].update(rest=[]))
    add('false-prime',raw,lambda r:r[1].update(k='l',x={'prime':11}))
    add('composite-prime',raw,lambda r:r[1].update(k='l',x={'prime':9}))
    add('wrong-multiplicity',raw,lambda r:r[0]['groups'][0].__setitem__(1,2))
    add('wrong-root',raw,lambda r:r[0]['root'].update(m=2))
    add('duplicate-id',raw,lambda r:r.append(copy.deepcopy(r[-1])))
    add('orphan-node',raw,lambda r:r.append(dict(r[-1],id=999999,p=999998)))
    add('bad-parent',raw,lambda r:r[2].update(p=99999))
    add('child-outside-parent',raw,lambda r:r[2]['r'].__setitem__(0,1-r[2]['r'][0]))
    add('noncanonical-residue',raw,lambda r:r[2]['r'][1].__setitem__(0,2))
    add('duplicate-child',raw,lambda r:r[1]['c'].append(r[1]['c'][0]))
    add('missing-positive',pr,lambda r:r[1]['x'].update(sol=[]))
    add('false-positive',pr,lambda r:r[1]['x']['sol'].append([7]))
    add('wrong-size-exponent',pr,lambda r:r[1]['x']['sz'].__setitem__(0,r[1]['x']['sz'][0]+1))
    add('invalid-decimal-pin',pr,lambda r:r[0].update(pin_digits=4))
    add('invalid-mod8-floor',pr,lambda r:r[0].update(pin2=True))
    results=[]
    for name,r in mutations:
        p=HERE/'tamper'/f'{name}.jsonl';p.parent.mkdir(exist_ok=True)
        p.write_text(''.join(json.dumps(n)+'\n' for n in r))
        try: Checker(p,10).run()
        except (ValueError,KeyError,TypeError,IndexError) as e:
            results.append({'test':name,'result':'REJECTED','reason':str(e)})
        else: raise AssertionError('tamper accepted: '+name)
    # An unaligned sumset leaf must be independently accepted.
    for K in range(1,150):
        if K%5==0 or valuation(K,2)>=8: continue
        g=Generator([],K,8,pin2=False,pin_digits=0)
        r=g.zero();a,w=g.sig(r,1);e=g.sumkill(r,1,a,w)
        if e:
            g.new(r,1,-1);g.nodes[0].update(k='l',x={'prime':e[0]})
            p=HERE/'controls/sumset.jsonl';g.write(p)
            c=Checker(p,12).run()
            assert c['stats']['sumset_checks']==1
            results.append({'test':'positive-unaligned-sumset','result':'PASS','K':K,'prime':e[0],'check':c})
            # Replacing it by a composite still fails even in the sumset path.
            break
    else: raise AssertionError('no unaligned control')
    return results


def arithmetic_soundness():
    """True small-box smooth points cannot be killed, with either pin option.
    Also compare the generator's reused signatures with a fully fresh checker.
    """
    cases=0; signature_cases=0; true_points=0; reused_cases=0
    source=HERE/'smoke.jsonl'
    for coefs,K,qmin in (([9,9,9],89,3),([18],98,3),([],188,3),([],206,3)):
        for pin in (0,3):
            g=Generator(coefs,K,qmin,pin_digits=pin)
            g.new(g.zero(),1,-1)
            g.nodes[0].update(k='l',x={'prime':11})
            fn=HERE/'tamper/arithmetic_spec.jsonl'
            g.write(fn)
            checker=Checker(fn,8)
            for M in (1,2,3,6,12,18):
                for flat in itertools.islice(g.lifts_of(g.zero(),1,M),200):
                    nested=g.nested(flat)
                    cr=(nested[0],)+tuple(tuple(v) for v in nested[1:])
                    a,w=g.sig(flat,M);aa,ww=checker.signature(cr,M)
                    assert a==(aa[0],aa[0] if aa[1] else None)
                    assert w==(ww[0],ww[0] if ww[1] else None)
                    signature_cases+=1
                    for e in g.aligned(M,a,w)[:4]:
                        assert g.test(e,flat,a,w)==checker.killed(e[0],cr,M)
                        cases+=1
            for M in (1,2,3):
                for flat in itertools.islice(g.lifts_of(g.zero(),1,M),4):
                    for f in (2,3):
                        alive,used=g.expand(flat,M,f)
                        for rr,a,w in alive:
                            nested=g.nested(rr)
                            cr=(nested[0],)+tuple(tuple(v) for v in nested[1:])
                            aa,ww=checker.signature(cr,M*f)
                            assert a==(aa[0],aa[0] if aa[1] else None)
                            assert w==(ww[0],ww[0] if ww[1] else None)
                            reused_cases+=1
            for L in range(qmin,9):
                for qs in itertools.permutations(range(qmin,L),len(coefs)):
                    X=10**L+K+sum(c*10**q for c,q in zip(g.coefs,qs))
                    y=X
                    for p in (2,3,7):
                        while y%p==0:y//=p
                    if y!=1:continue
                    true_points+=1
                    for M in (1,2,3,6,12,18,36,42):
                        r=g.key((L,)+qs,M);a,w=g.sig(r,M)
                        assert g.kill(r,M,a,w) is None
                        assert g.sumkill(r,M,a,w) is None
    return {'label':'COMPUTED','generator_checker_kills_compared':cases,
            'signatures_compared':signature_cases,'reused_signatures_compared':reused_cases,
            'true_smooth_points':true_points}


def main():
    for f in HERE.glob('*.py'): compile(f.read_text(),str(f),'exec')
    p=positives()
    save(HERE/'positive_results.json',p)
    r={'label':'COMPUTED','positive_counts':{'level1':len(p['level1']),'level2':len(p['level2']),
       'finite_boxes':len(p['finite_boxes']),'exact_classes':len(p['exact_class_certificates'])},
       'partition_tests':partition(),'tamper_tests':tamper(),'arithmetic_soundness':arithmetic_soundness()}
    save(HERE/'test_results.json',r)
    print(json.dumps({'label':'COMPUTED','result':'PASS','positive_counts':r['positive_counts'],
                      'partition_tests':len(r['partition_tests']),'tamper_tests':len(r['tamper_tests'])}))

if __name__=='__main__': main()
