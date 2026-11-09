# Tamper tests for check_sym_F: each corrupted copy must be REJECTED.   python3 -I tamper_F.py
import sys, json, os, copy, collections, random
sys.path.insert(0, '.')
import check_sym_F as F
sys.setrecursionlimit(10000)
SYM = '../highdim/sym/'
os.makedirs('tamper', exist_ok=True)
BR = 8

def load(path):
    return [json.loads(l) for l in open(path) if l.strip()]
def dump(lines, path):
    with open(path, 'w') as fh:
        for d in lines: fh.write(json.dumps(d, separators=(',', ':')) + '\n')
def run(lines, name):
    p = 'tamper/' + name + '.jsonl'; dump(lines, p)
    try:
        ct, cl, br = F.check(p, BR)
        return ('REJECTED' if ct.problems else 'ACCEPTED'), ct.problems[:2]
    except Exception as e:
        return 'REJECTED', ['exception %s: %s' % (type(e).__name__, e)]

def classify_leaves(lines):
    meta = lines[0]; ct = F.Cert(meta)
    out = []
    for d in lines[1:]:
        if d['k'] == 'l' and 'prime' in d['x']:
            cls = ct.mkcls(d['r']); ok, kind = ct.kills(d['x']['prime'], cls, d['m'])
            out.append((d['id'], d['x']['prime'], kind if ok else 'NOKILL'))
    return ct, out

results = []
def record(name, what, verdict, why):
    results.append(dict(name=name, what=what, verdict=verdict, detail=why))
    print('%-34s %-9s %s | %s' % (name, verdict, what, why[0][:110] if why else ''))

paths = json.load(open('tamper_targets.json'))
base = {}
for kind, path in paths.items():
    lines = load(path)
    v, why = run(lines, 'base_' + kind)
    record('base_' + kind, 'UNMODIFIED %s (must pass)' % os.path.basename(path), 'ACCEPTED' if v == 'ACCEPTED' else 'UNEXPECTED-REJECT', why)
    base[kind] = lines

smallprimes = [p for p in range(11, 400) if F.isprime(p)]

# ---------- sumset-kill leaf / rest primes
lines = base['sumset']
ct, leaves = classify_leaves(lines)
cand = [(i, p, k) for i, p, k in leaves if k.startswith('sumset')]
if cand:
    i, p, k = cand[0]
    nd = next(d for d in lines[1:] if d['id'] == i); cls = ct.mkcls(nd['r'])
    repl = [q for q in smallprimes if q != p and not ct.kills(q, cls, nd['m'])[0]]
    L2 = copy.deepcopy(lines); next(d for d in L2[1:] if d['id'] == i)['x']['prime'] = repl[0]
    v, why = run(L2, 'sumset_leaf_prime_swapped'); record('sumset_leaf_prime_swapped', 'sumset leaf %s prime %s(%s)->%s' % (i, p, k, repl[0]), v, why)
    # corrupt the leaf's own class so that the kill is invalid but headers stay consistent: flip one residue in leaf AND nothing else -> header mismatch expected
    L2 = copy.deepcopy(lines); d2 = next(d for d in L2[1:] if d['id'] == i)
    g = d2['r'][1]; g[0] = (g[0] + 1) % d2['m']; g.sort()
    v, why = run(L2, 'sumset_leaf_class_shifted'); record('sumset_leaf_class_shifted', 'sumset leaf %s residue shifted' % i, v, why)
else: print('no sumset leaf available')
# unsound variant: treating residues as exact exponents mod d (a single representative) instead of the full sumset
lines = base['sumset']
ct, leaves = classify_leaves(lines)
cand = [(i, p, k) for i, p, k in leaves if k.startswith('sumset')]
shown = 0
for i, p, k in cand:
    nd = next(d for d in lines[1:] if d['id'] == i); cls = ct.mkcls(nd['r']); M = nd['m']
    for q in smallprimes + [x for x in range(401, 5000) if F.isprime(x)]:
        d = F.order(10, q)
        if M % d == 0: continue
        T0 = (pow(10, cls[0], q) + ct.K + sum(c * pow(10, r, q) for c, g in zip(ct.coefs, cls[1:]) for r in g)) % q
        saved = ct.sumset
        ct.sumset = lambda pp, dd, gg, red, T0=T0: {T0}
        ct.killcache = {}
        rep_kills = ct.kills(q, cls, M)[0]
        ct.sumset = saved; ct.killcache = {}
        true_kills = ct.kills(q, cls, M)[0]
        if rep_kills and not true_kills:
            L2 = copy.deepcopy(lines); next(d_ for d_ in L2[1:] if d_['id'] == i)['x']['prime'] = q
            v, why = run(L2, 'sumset_single_representative'); record('sumset_single_representative', 'leaf %s: prime %s kills if residue is taken as the exponent (single rep) but not over the full sumset' % (i, q), v, why)
            shown += 1; break
    if shown: break
if not shown: print('NO single-representative counterexample found')
# remove sumset primes from a node's rest list
usable = None
for d in lines[1:]:
    if d['k'] == 'i' and d.get('rest'):
        usable = d
rest_nodes = [d for d in lines[1:] if d['k'] == 'i' and d.get('rest')]
done = False
for d in rest_nodes:
    # nodes whose rest list contains a prime with d(ord) not dividing m2 (sumset-type)
    un = [p for p in d['rest'] if p > 7 and F.order(10, p) and d['m2'] % F.order(10, p) != 0]
    if un:
        L2 = copy.deepcopy(lines); nd2 = next(x for x in L2[1:] if x['id'] == d['id'])
        nd2['rest'] = [p for p in nd2['rest'] if p not in un]
        v, why = run(L2, 'sumset_rest_primes_removed'); record('sumset_rest_primes_removed', 'node %s: dropped unaligned rest primes %s' % (d['id'], un), v, why); done = True; break
if not done: print('no node with unaligned rest primes')

# ---------- tail-coset kills
lines = base['tail']
ct, leaves = classify_leaves(lines)
cand = [(i, p, k) for i, p, k in leaves if k.endswith('tail') or k.endswith('both')]
meta = lines[0]
L2 = copy.deepcopy(lines); L2[0]['pin_digits'] = None
v, why = run(L2, 'tail_pin_removed'); record('tail_pin_removed', 'meta pin_digits 3 -> none (kills that need the coset must fail)', v, why)
L2 = copy.deepcopy(lines); L2[0]['pin_digits'] = 4
v, why = run(L2, 'tail_pin_too_wide'); record('tail_pin_too_wide', 'pin_digits=4 > min(3,qmin) (classic over-pin)', v, why)
L2 = copy.deepcopy(lines); L2[0]['qmin'] = 2
v, why = run(L2, 'tail_qmin_below_pin'); record('tail_qmin_below_pin', 'qmin=2 with pin_digits=3 (pin beyond minimum position)', v, why)
L2 = copy.deepcopy(lines); L2[0]['pin2'] = True; L2[0]['K'] = lines[0]['K'] + 2 ** 0 * 0
if cand:
    i, p, k = cand[0]
    nd = next(d for d in lines[1:] if d['id'] == i); cls = ct.mkcls(nd['r'])
    repl = [q for q in smallprimes if q != p and not ct.kills(q, cls, nd['m'])[0]]
    L2 = copy.deepcopy(lines); next(d for d in L2[1:] if d['id'] == i)['x']['prime'] = repl[0]
    v, why = run(L2, 'tail_leaf_prime_swapped'); record('tail_leaf_prime_swapped', 'tail-kill leaf %s prime %s(%s)->%s' % (i, p, k, repl[0]), v, why)
# wrong target for tail: change K by a multiple of 2 that keeps t0: K -> K+2*1000?? changes the whole equation -> tree must break
for dK in (9000, 18000):
    L2 = copy.deepcopy(lines); L2[0]['K'] = lines[0]['K'] + dK
    v, why = run(L2, 'tail_K_plus_%d' % dK); record('tail_K_plus_%d' % dK, 'K += %d (same K mod 9 and mod 1000: only the other primes see it)' % dK, v, why)
# K changes that alter K mod 9 are vacuous kills (v3(X)=0 contradicts the tail coset), shown as informational
L2 = copy.deepcopy(lines); L2[0]['K'] = lines[0]['K'] + 1000
v, why = run(L2, 'INFO_K_plus_1000'); record('INFO_K_plus_1000', 'INFORMATIONAL: K+=1000 changes K mod 9 => a=0 exact, impossible with the pin => vacuously closed', v, why)
L2 = copy.deepcopy(lines); L2[0]['pin2'] = not bool(lines[0].get('pin2'))
v, why = run(L2, 'INFO_pin2_flipped_with_tail'); record('INFO_pin2_flipped_with_tail', 'INFORMATIONAL: pin2 off while tail k=3,t0=0 (tail already implies mod 8)', v, why)
# pin2 on a certificate that has no tail pin: removing pin2 must break it
lines_p2 = base['pin2only']
L2 = copy.deepcopy(lines_p2); L2[0]['pin2'] = False
v, why = run(L2, 'pin2_removed_no_tail'); record('pin2_removed_no_tail', 'cert with pin2 only: pin2 -> false', v, why)
L2 = copy.deepcopy(lines_p2); L2[0]['qmin'] = 2
v, why = run(L2, 'pin2_qmin_too_small'); record('pin2_qmin_too_small', 'pin2 with qmin=2 < t0+3', v, why)

# ---------- multiset children
lines = base['multiset']
internal = [d for d in lines[1:] if d['k'] == 'i' and len(d['c']) >= 2]
# pick node whose child class has repeated residues in some group
def has_rep(d):
    return any(len(set(g)) < len(g) for g in d['r'][1:])
cands = [d for d in internal if has_rep(d)] or internal
d = cands[0]
byid = {x['id']: x for x in lines[1:]}
# (1) delete a child (a lift becomes unlisted; it must be killable by 'rest' which it is not)
L2 = copy.deepcopy(lines); nd2 = next(x for x in L2[1:] if x['id'] == d['id']); nd2['c'] = nd2['c'][1:]
v, why = run(L2, 'multiset_child_deleted'); record('multiset_child_deleted', 'node %s: first child removed from c' % d['id'], v, why)
# (2) duplicate a child
L2 = copy.deepcopy(lines); nd2 = next(x for x in L2[1:] if x['id'] == d['id']); nd2['c'] = nd2['c'] + [nd2['c'][0]]
v, why = run(L2, 'multiset_child_duplicated'); record('multiset_child_duplicated', 'node %s: duplicate child id' % d['id'], v, why)
# (3) child residue multiset replaced by another multiset that is NOT a lift (one entry moved by +M of parent mod)
c0 = byid[d['c'][0]]
L2 = copy.deepcopy(lines); cc = next(x for x in L2[1:] if x['id'] == c0['id'])
grp = None
for gi in range(1, len(cc['r'])):
    if cc['r'][gi]: grp = gi; break
cc['r'][grp][0] = (cc['r'][grp][0] + 1) % cc['m']; cc['r'][grp].sort()
v, why = run(L2, 'multiset_child_not_a_lift'); record('multiset_child_not_a_lift', 'child %s: one residue +1 (reduction mod parent changes)' % c0['id'], v, why)
# (4) child multiset replaced by a different genuine lift of the parent (another child's class) -> duplicate / wrong header
if len(d['c']) >= 2:
    c1 = byid[d['c'][1]]
    L2 = copy.deepcopy(lines); cc = next(x for x in L2[1:] if x['id'] == c0['id']); cc['r'] = copy.deepcopy(c1['r'])
    v, why = run(L2, 'multiset_child_class_swapped'); record('multiset_child_class_swapped', 'child %s given sibling %s class' % (c0['id'], c1['id']), v, why)
# (5) rest primes emptied at the node (all unlisted lifts then unkilled)
L2 = copy.deepcopy(lines); nd2 = next(x for x in L2[1:] if x['id'] == d['id']); nd2['rest'] = []
v, why = run(L2, 'multiset_rest_emptied'); record('multiset_rest_emptied', 'node %s: rest primes removed' % d['id'], v, why)
# (6) permute multiplicity: change a repeated residue pair {r,r} -> {r, r'} where r' is another lift of the same parent residue class (same reduction) but wrong at this child
dd = None
for x in lines[1:]:
    if x['k'] in ('i', 'l') and x['p'] != -1 and any(len(set(g)) < len(g) for g in x['r'][1:]):
        dd = x; break
if dd is not None:
    L2 = copy.deepcopy(lines); cc = next(x for x in L2[1:] if x['id'] == dd['id'])
    par = byid[dd['p']]
    for gi in range(1, len(cc['r'])):
        g = cc['r'][gi]
        if len(set(g)) < len(g):
            # replace one copy of the repeated residue r by r + (m_parent) mod m  (same parent residue; collapses multiplicity pattern)
            r0 = [v for v in g if g.count(v) > 1][0]
            idx = g.index(r0); g[idx] = (r0 + par['m2'] // (par['m2'] // par['m'] if par['m2'] % par['m'] == 0 else 1) ) % cc['m']
            g.sort(); break
    v, why = run(L2, 'multiset_repeat_split_wrong'); record('multiset_repeat_split_wrong', 'node %s: one copy of a repeated residue moved' % dd['id'], v, why)
json.dump(results, open('tamper_results.json', 'w'), indent=1)
bad = [r for r in results if r['name'].startswith('base_') and r['verdict'] != 'ACCEPTED' or (not r['name'].startswith('base_') and r['verdict'] != 'REJECTED')]
print('TOTAL', len(results), 'unexpected:', [r['name'] for r in bad])
