"""Independent R2 identities. No candidate imports or writes. Stdlib only.
Finite checks supplement the all-order proof in the review; they do not prove it.
Run with PYTHONDONTWRITEBYTECODE=1.
"""
from collections import Counter, defaultdict
from fractions import Fraction as Q
from functools import lru_cache
from itertools import combinations
from pathlib import Path
from decimal import Decimal, localcontext
import json, math

OUT = Path(__file__).resolve().parent
ROOT = OUT.parents[2]

def enum(vertices, edges):
    if not vertices:
        return [frozenset()]
    v = min(vertices)
    ans = []
    for label, ends in edges.items():
        if v not in ends:
            continue
        w = next(u for u in ends if u != v)
        if w in vertices:
            ans += [M | {label} for M in enum(vertices - {v, w}, edges)]
    return ans

def complete(n, duplicate=False):
    pairs = list(combinations(range(n), 2))
    if duplicate:
        pairs += [(0, 3), (1, 4), (0, 1)]
    return {i: frozenset(e) for i, e in enumerate(pairs)}

def means(edges, law):
    return {e: sum((p for M, p in law.items() if e in M), Q()) for e in edges}

def project(law, labels):
    ans = defaultdict(Q)
    for M, p in law.items():
        ans[M & labels] += p
    return dict(ans)

def child(vertices, edges, retain):
    z = max(vertices) + 1
    ee = {e: uv if uv <= retain else frozenset((next(iter(uv & retain)), z))
          for e, uv in edges.items() if uv & retain}
    return retain | {z}, ee, z

@lru_cache(None)
def factors(n):
    out = Counter()
    d = 2
    while d*d <= n:
        while n % d == 0:
            out[d] += 1
            n //= d
        d += 1 if d == 2 else 2
    if n > 1:
        out[n] += 1
    return out

def entropy(values):
    """Exact rational coefficients of log(prime), with no float arithmetic."""
    ans = defaultdict(Q)
    for p in values:
        if p:
            for prime, k in factors(p.numerator).items():
                ans[prime] -= p*k
            for prime, k in factors(p.denominator).items():
                ans[prime] += p*k
    return {a: b for a, b in ans.items() if b}

def combine(*terms):
    ans = defaultdict(Q)
    for coefficient, term in terms:
        for prime, k in term.items():
            ans[prime] += coefficient*k
    return {a: b for a, b in ans.items() if b}

def quantities(edges, law, root):
    x = means(edges, law)
    return (entropy(x.values()), entropy(law.values()),
            entropy(1-p for p in x.values()),
            entropy(1-p for e, p in x.items() if root not in edges[e]))

def glue_tests():
    result = []
    for n, duplicated in [(6, False), (6, True), (8, False), (8, True)]:
        vertices = set(range(n)); edges = complete(n, duplicated)
        for size in sorted({3, n-3}):
            side = set(range(size))
            cut = {e for e, uv in edges.items() if len(uv & side) == 1}
            atoms = [M for M in enum(vertices, edges) if len(M & cut) == 1]
            weights = [math.prod(1+e % 3 for e in M) for M in atoms]
            law = dict(zip(atoms, (Q(w, sum(weights)) for w in weights)))
            # Face Gibbs law: max entropy at its own means by finite KL.
            rootrows = []
            for root in vertices:
                retain = side if root in side else vertices-side
                v1, e1, z1 = child(vertices, edges, retain)
                v2, e2, z2 = child(vertices, edges, vertices-retain)
                l1 = project(law, set(e1)); l2 = project(law, set(e2))
                assert set(l1) == set(enum(v1, e1))
                assert set(l2) == set(enum(v2, e2))
                q = {e: means(edges, law)[e] for e in cut}
                for M, p in law.items():
                    e = next(iter(M & cut))
                    assert p == l1[M & set(e1)]*l2[M & set(e2)]/q[e]
                F, H, B, W = quantities(edges, law, root)
                F1, H1, B1, W1 = quantities(e1, l1, root)
                F2, H2, B2, W2 = quantities(e2, l2, z2)
                hq = entropy(q.values()); bq = entropy(1-p for p in q.values())
                for a, b, c, separator in [(F,F1,F2,hq),(H,H1,H2,hq),(B,B1,B2,bq)]:
                    assert not combine((1,a),(-1,b),(-1,c),(1,separator))
                assert not combine((1,W),(-1,W1),(-1,W2))
                charged = Counter(e for e, uv in edges.items() if root not in uv)
                charges = Counter(e for e, uv in e1.items() if root not in uv)
                charges.update(e for e, uv in e2.items() if z2 not in uv)
                assert charges == charged
                rootrows.append({'root': root, 'other_root': z2, 'charged_labels': sorted(charged)})
            result.append({'n': n, 'duplicated': duplicated, 'side_size': size,
                           'atoms': len(law), 'roots': rootrows})
    return result

def collapse_tests():
    simple = complete(4); edges = {}; cls = {}; activities = {}
    for a, uv in simple.items():
        for j in range(1+a % 3):
            e = len(edges); edges[e] = uv; cls[e] = a; activities[e] = j+1
    atoms = enum(set(range(4)), edges)
    weights = [math.prod(activities[e] for e in M) for M in atoms]
    law = dict(zip(atoms, (Q(w,sum(weights)) for w in weights)))
    collapsed = defaultdict(Q)
    for M, p in law.items():
        collapsed[frozenset(cls[e] for e in M)] += p
    x = means(edges, law); y = means(simple, collapsed)
    F,H,_,_ = quantities(edges,law,0); f,h,_,_ = quantities(simple,collapsed,0)
    assert not combine((1,F),(-1,H),(-1,f),(1,h))
    for a in simple:
        assert sum(x[e] for e in edges if cls[e] == a) == y[a]
    return {'labelled_atoms':len(law),'collapsed_atoms':len(collapsed),
            'deficit_difference_prime_log_coefficients':{},
            'class_masses':{str(a):str(p) for a,p in y.items()}}

def klee(m):
    vertices = {0,1}; edges = {e:frozenset((0,1)) for e in range(3)}; colors = {e:e for e in range(3)}
    for _ in range(m-1):
        v = min(vertices); ports = [e for e, uv in edges.items() if v in uv]
        a,b = max(vertices)+1,max(vertices)+2; tri = [v,a,b]
        vertices |= {a,b}
        for t,e in zip(tri,ports):
            edges[e] = frozenset((t,next(iter(edges[e]-{v}))))
        first = len(edges)
        for j in range(3):
            edges[first+j] = frozenset(tri)-{tri[j]}; colors[first+j] = colors[ports[j]]
    return vertices, edges, colors

def decompose(vertices,edges,x,root,root_was_contracted=False):
    for size in range(3,len(vertices)-2,2):
        for tup in combinations(sorted(vertices),size):
            S = set(tup)
            if root not in S: continue
            C = {e for e,uv in edges.items() if len(uv&S)==1}
            if sum(x[e] for e in C) != 1: continue
            a,A,_ = child(vertices,edges,S); b,B,z = child(vertices,edges,vertices-S)
            l1,c1,r1 = decompose(a,A,x,root,root_was_contracted); l2,c2,r2 = decompose(b,B,x,z,True)
            return l1+l2,c1+c2,r1+r2+[root_was_contracted]
    return 1,Counter(e for e,uv in edges.items() if root not in uv),[]

def klee_tests():
    rows=[]
    for m in range(1,7):
        vertices,edges,colors=klee(m); s=len(edges)
        K=[[Q(2,9) if colors[i]==colors[j] else Q(-1,9) for j in edges] for i in edges]
        # Verify the entire matrix identity, not just a trace.
        assert all(sum(K[i][k]*K[k][j] for k in edges)==Q(m,3)*K[i][j] for i in edges for j in edges)
        assert sum(K[i][i] for i in edges)==Q(2*m,3)
        x={e:Q(1,3) for e in edges}; leaves=[]; rerooted=0
        for root in vertices:
            number,charged,history=decompose(vertices,edges,x,root)
            assert charged==Counter(e for e,uv in edges.items() if root not in uv)
            assert number==(1 if m==1 else m-1)
            leaves.append(number); rerooted+=sum(history)
        rows.append({'m':m,'roots':len(vertices),'leaves':leaves,
                     'normalized_second_variation':str(1-Q(m,4)),
                     'matrix_identity_K_squared_equals_m_over_3_K':True,
                     'splits_with_previously_contracted_root':rerooted})
    return rows

def fixed_tests():
    # All four root cases: retained/deleted, nonempty/empty residual.
    base=complete(4); atoms=enum(set(range(4)),base); law={M:Q(1,3) for M in atoms}
    e=dict(base); e[6]=frozenset((4,5)); e[7]=frozenset((0,4))
    lifted={M|{6}:p for M,p in law.items()}
    assert means(e,lifted)[7]==0
    for root in range(6):
        F,H,B,W=quantities(e,lifted,root); f,h,b,w=quantities(base,law,root if root<4 else 0)
        assert F==f and H==h and B==b
        assert W==(w if root<4 else B)
    emptylaw={frozenset():Q(1)}; deterministic={frozenset((0,)):Q(1)}
    assert quantities({0:frozenset((0,1))},deterministic,0)==({},{},{},{})
    assert quantities({},emptylaw,0)==({},{},{},{})
    return {'nonempty_residual_roots':6,'empty_residual':True,'zero_cross_edge':True}

def suspect():
    path=ROOT/'frontier/experiments/i25_matching_entropy_improvement/rooted-results.json'
    data=json.loads(path.read_text(),parse_float=Decimal)
    rows=[r for r in data['top'] if abs(r['rooted_ratio']-Decimal('1.367744980429948'))<Decimal('1e-12')]
    assert len(rows)==1
    r=rows[0]; edges={i:frozenset(uv) for i,uv in enumerate(r['edges'])}; atoms=enum(set(range(r['n'])),edges)
    answers=[]
    for precision in (100,180):
        with localcontext() as ctx:
            ctx.prec=precision
            logw=[sum((r['theta'][e] for e in M),Decimal(0)) for M in atoms]
            w=[(t-max(logw)).exp() for t in logw]; z=sum(w); p=[t/z for t in w]
            x=[sum((t for M,t in zip(atoms,p) if e in M),Decimal(0)) for e in edges]
            absent=[sum((t for M,t in zip(atoms,p) if e not in M),Decimal(0)) for e in edges]
            ent=lambda vals:sum((-t*t.ln() for t in vals if t),Decimal(0))
            H,F=ent(p),ent(x); W=ent(absent[e] for e in edges if r['v'] not in edges[e])
            answers.append({'precision':precision,'H':str(H),'F':str(F),'W':str(W),'ratio':str((F-H)/W)})
    with localcontext() as ctx:
        ctx.prec=200
        assert abs(Decimal(answers[0]['ratio'])-Decimal(answers[1]['ratio']))<Decimal('1e-75')
    return {'source':str(path.relative_to(ROOT)),'n':r['n'],'root':r['v'],'atoms':len(atoms),
            'answers':answers,'interpretation':'Exact stored decimal theta; precision agreement is not interval certification.'}

def run():
    trace=[]
    for m in range(3,21):
        for eps in [Q(1,10),Q(1,10**10),Q(1,10**30)]:
            c=Q(3,2)+eps
            assert (c-1)*m-c==Q(m-3,2)+eps*(m-1)>0
            trace.append([m,str(eps),str((c-1)*m-c)])
    result={'gluing':glue_tests(),'parallel_collapse':collapse_tests(),'klee':klee_tests(),
            'fixed_coordinates':fixed_tests(),'trace':trace,'suspect_recomputation':suspect(),
            'scope':'Exact finite identities and one high-precision diagnostic. Universal proof is written in the review.'}
    (OUT/'results.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps({'status':'PASS','gluing_cases':len(result['gluing']),
                      'gluing_roots':sum(len(r['roots']) for r in result['gluing']),
                      'klee_roots':sum(r['roots'] for r in result['klee']),
                      'trace_checks':len(trace),'suspect_ratio':result['suspect_recomputation']['answers'][1]['ratio'][:35]}))

if __name__=='__main__':
    run()
