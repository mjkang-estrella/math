"""335271 backtracking version of kinout.py (same normal form), exploiting monotonicity:
adding arcs only adds Hamiltonian paths, so a partial arc set that already has two incoming->outgoing
Hamiltonian paths with the same start and different ends, or different starts and the same end, can be pruned.
At leaves every incoming vertex must have a Hamiltonian path to an outgoing vertex.

usage: kinout_bt.py k a pat_lo pat_hi OUTNAME  (a=-1: all a, all patterns; output outputs/kinout/OUTNAME.json)
optional 6th arg: 'first:N' restrict first variable's option index to N (for chunking), e.g. first:0
"""
import sys, json, time, os
k, a_arg, plo, phi, outname = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]), sys.argv[5]
firstopt = None
if len(sys.argv) > 6 and sys.argv[6].startswith('first:'):
    firstopt = int(sys.argv[6][6:])
D = '/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r248'
os.makedirs(D + '/outputs/kinout', exist_ok=True)
outp = f'{D}/outputs/kinout/{outname}.json'
if os.path.exists(outp):
    raise SystemExit('refusing to overwrite ' + outp)
n = 2 * k - 1
full = (1 << n) - 1


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
            pats.append(''.join(w))
    return pats


nodes = 0


def relation(succ, inc, outset):
    """returns (ok, ends_of) ; ok False if conflict"""
    used = {}
    ends_of = {}
    for s0 in inc:
        ends = set()
        stack = [(s0, 1 << s0)]
        while stack:
            v, m = stack.pop()
            if m == full:
                if v in outset:
                    ends.add(v)
                    if len(ends) > 1:
                        return False, None
                continue
            for t in succ[v]:
                if not (m >> t) & 1:
                    stack.append((t, m | (1 << t)))
        if ends:
            e = next(iter(ends))
            if e in used:
                return False, None
            used[e] = s0
            ends_of[s0] = e
    return True, ends_of


def search(w):
    global nodes
    inc = [v for v in range(n) if w[v] in 'IB']
    outset = {v for v in range(n) if w[v] in 'OB'}
    vars_ = []  # (kind, vertex, options)
    for v in range(n):
        if w[v] in 'IN':
            vars_.append(('x', v, [t for t in inc if t != v and t != v + 1]))
        if w[v] in 'ON':
            vars_.append(('y', v, [s for s in sorted(outset) if s != v and s != v - 1]))
    succ = [[v + 1] if v + 1 < n else [] for v in range(n)]
    found = []

    def rec(i):
        global nodes
        nodes += 1
        ok, ends_of = relation(succ, inc, outset)
        if not ok:
            return
        if i == len(vars_):
            if len(ends_of) == len(inc):
                arcs = sorted((v, t) for v in range(n) for t in succ[v])
                assert len(arcs) == 4 * k - 4 and len(set(arcs)) == len(arcs)
                found.append({'pattern': w, 'arcs': arcs, 'pairs': sorted(ends_of.items())})
            return
        kind, v, opts = vars_[i]
        for j, o in enumerate(opts):
            if i == 0 and firstopt is not None and j != firstopt:
                continue
            if kind == 'x':
                succ[v].append(o)
                rec(i + 1)
                succ[v].pop()
            else:
                succ[o].append(v)
                rec(i + 1)
                succ[o].pop()
    rec(0)
    return found


t0 = time.time()
if a_arg == -1:
    jobs = [(a, w) for a in range(k) for w in patterns_for(a)]
else:
    jobs = [(a_arg, w) for w in patterns_for(a_arg)[plo:phi]]
per = {}
allfound = []
for a, w in jobs:
    f = search(w)
    per.setdefault(a, [0, 0])
    per[a][0] += 1
    per[a][1] += len(f)
    allfound += f
res = {'k': k, 'a_arg': a_arg, 'pattern_range': [plo, phi] if a_arg != -1 else 'all', 'first_option_restriction': firstopt,
       'per_a_patterns_found': per, 'nodes': nodes, 'found_count': len(allfound), 'found_first': allfound[:30],
       'seconds': round(time.time() - t0, 2)}
open(outp, 'x').write(json.dumps(res, indent=1) + '\n')
print(json.dumps({x: res[x] for x in res if x != 'found_first'}))
if allfound:
    print('example', allfound[0])
