"""335271 (Glynn-Haythorpe-Moeini, arXiv:1702.03075v2, Conjecture after Thm 'edges'):
exhaustive search for k-in-out digraphs of order 2k-1 with exactly 4k-4 arcs, in the tight normal form
forced by the source's proof of 'Any k-in-out graph of order 2k-1 contains at least 4k-4 directed edges'.

Normal form (see SUMMARY for the derivation): vertices 0..2k-2 labelled along a Hamiltonian path
0->1->...->2k-2 from i_1=0 to o_1=2k-2; type word = (I^p B O^r N)...(I^p B O^r) with a I's, a O's,
b=k-a B's, c=b-1 N's. Every X=I∪N vertex has exactly one extra out-arc, into I∪B; every Y=O∪N vertex has
exactly one extra in-arc, from O∪B; no other arcs.  Single visit condition is automatic in this form
(each incoming->outgoing path contains one more B than N).  We test the paired vertices condition:
the relation {(start,end): Hamiltonian path start in I∪B -> end in O∪B} must be a bijection I∪B -> O∪B.

usage: kinout.py k a pat_lo pat_hi OUTNAME   (a=-1: all a in 0..k-1 and all patterns)
output outputs/kinout/OUTNAME.json (never overwritten)
"""
import sys, json, itertools, time, os
k, a_arg, plo, phi, outname = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
D = '/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r248'
os.makedirs(D + '/outputs/kinout', exist_ok=True)
outp = f'{D}/outputs/kinout/{outname}.json'
if os.path.exists(outp):
    raise SystemExit('refusing to overwrite ' + outp)
n = 2 * k - 1


def compositions(total, parts):
    if parts == 1:
        yield (total,)
        return
    for x in range(total + 1):
        for rest in compositions(total - x, parts - 1):
            yield (x,) + rest


def patterns_for(a):
    b = k - a
    pats = []
    for ip in compositions(a, b):
        for op in compositions(a, b):
            w = []
            for s in range(b):
                w += ['I'] * ip[s] + ['B'] + ['O'] * op[s]
                if s < b - 1:
                    w.append('N')
            assert len(w) == n
            pats.append(''.join(w))
    return pats


def search(w):
    inc = [v for v in range(n) if w[v] in 'IB']
    outset = {v for v in range(n) if w[v] in 'OB'}
    X = [v for v in range(n) if w[v] in 'IN']
    Y = [v for v in range(n) if w[v] in 'ON']
    xopts = [[t for t in inc if t != u and t != u + 1] for u in X]
    yopts = [[s for s in outset if s != y and s != y - 1] for y in Y]
    base_succ = [[v + 1] if v + 1 < n else [] for v in range(n)]
    full = (1 << n) - 1
    tested = 0
    found = []
    for xs in itertools.product(*xopts):
        for ys in itertools.product(*yopts):
            tested += 1
            succ = [list(s) for s in base_succ]
            for u, t in zip(X, xs):
                succ[u].append(t)
            for y, s in zip(Y, ys):
                succ[s].append(y)
            ends_of = {}
            used_end = set()
            bad = False
            for s0 in inc:
                ends = set()
                stack = [(s0, 1 << s0)]
                while stack:
                    v, m = stack.pop()
                    if m == full:
                        if v in outset:
                            ends.add(v)
                            if len(ends) > 1:
                                break
                        continue
                    for t in succ[v]:
                        if not (m >> t) & 1:
                            stack.append((t, m | (1 << t)))
                if len(ends) != 1:
                    bad = True
                    break
                e = next(iter(ends))
                if e in used_end:
                    bad = True
                    break
                used_end.add(e)
                ends_of[s0] = e
            if bad:
                continue
            arcs = sorted((v, t) for v in range(n) for t in succ[v])
            assert len(arcs) == 4 * k - 4 and len(set(arcs)) == len(arcs)
            found.append({'pattern': w, 'arcs': arcs, 'pairs': sorted(ends_of.items())})
    return tested, found


t0 = time.time()
jobs = []
if a_arg == -1:
    for a in range(0, k):
        for w in patterns_for(a):
            jobs.append((a, w))
else:
    pats = patterns_for(a_arg)
    jobs = [(a_arg, w) for w in pats[plo:phi]]
per = {}
allfound = []
total = 0
for a, w in jobs:
    t, f = search(w)
    total += t
    per.setdefault(a, [0, 0, 0])
    per[a][0] += 1
    per[a][1] += t
    per[a][2] += len(f)
    allfound += f
res = {'k': k, 'a_arg': a_arg, 'pattern_range': [plo, phi] if a_arg != -1 else 'all', 'per_a_patterns_graphs_found': per,
       'graphs_tested': total, 'found_count': len(allfound), 'found_first': allfound[:20], 'seconds': round(time.time() - t0, 2)}
open(outp, 'x').write(json.dumps(res, indent=1) + '\n')
print(json.dumps({x: res[x] for x in res if x != 'found_first'}))
if allfound:
    print('example', allfound[0])
