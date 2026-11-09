# sharper multiset-child tampers on a small certificate (deep nodes).  python3 -I tamper2_F.py
import sys, json, copy, collections
sys.path.insert(0, '.')
import check_sym_F as F
sys.setrecursionlimit(10000)
P = '../highdim/sym/certs/decimal_full/K5723_q3_c9_9_9_18_18.jsonl'
lines = [json.loads(l) for l in open(P)]
byid = {d['id']: d for d in lines[1:]}
out = []
def run(L2, name, what):
    p = 'tamper/' + name + '.jsonl'
    with open(p, 'w') as fh:
        for d in L2: fh.write(json.dumps(d, separators=(',', ':')) + '\n')
    try:
        ct, cl, br = F.check(p, 8); v = 'REJECTED' if ct.problems else 'ACCEPTED'; why = ct.problems[:1]
    except Exception as e:
        v = 'REJECTED'; why = ['exception %s' % e]
    print('%-34s %-9s %s | %s' % (name, v, what, (why or [''])[0][:120])); out.append(dict(name=name, what=what, verdict=v, detail=why))

# children (non-root-level) whose class has a repeated residue in some group, and whose sibling-with-{b,b+M} is absent
cands = []
for d in lines[1:]:
    if d['k'] in ('i', 'l') and d['p'] != -1:
        par = byid[d['p']]
        if par['p'] == -1: continue
        for gi in range(1, len(d['r'])):
            g = d['r'][gi]
            for b in set(g):
                if g.count(b) >= 2: cands.append((d, par, gi, b))
print('candidates', len(cands))
d, par, gi, b = cands[0]
M = par['m']; Q = par['m2']
sib = {tuple(map(tuple, byid[c]['r'][1:])) for c in par['c']}
print('child', d['id'], 'parent', par['id'], 'M', M, 'Q', Q, 'class', d['r'])
# T-a: {b,b} -> {b, b+M} (a different genuine lift of the parent class), the true lift becomes unlisted
for new_res in (b + M, b + 2 * M if Q // M > 2 else b + M):
    L2 = copy.deepcopy(lines); cc = next(x for x in L2[1:] if x['id'] == d['id']); g = cc['r'][gi]
    idx = g.index(b); g[idx] = new_res; g.sort()
    run(L2, 'ms_repeat_to_other_lift_%d' % new_res, 'child %s: one of the equal residues %s moved to the other lift %s (still a lift of the parent)' % (d['id'], b, new_res))
    break
# T-b: multiplicity of a parent residue NOT preserved: {b,b} -> {b, b'} with b' reducing to a different residue mod M
L2 = copy.deepcopy(lines); cc = next(x for x in L2[1:] if x['id'] == d['id']); g = cc['r'][gi]
idx = g.index(b); g[idx] = (b + 1) % Q; g.sort()
run(L2, 'ms_multiplicity_not_preserved', 'child %s: one copy of repeated residue %s replaced by %s (reduction mod %s changes)' % (d['id'], b, (b + 1) % Q, M))
# T-c: swap the residue multisets of two groups of different shape inside a child
L2 = copy.deepcopy(lines); cc = next(x for x in L2[1:] if x['id'] == d['id']); r = cc['r']
if len(r) >= 3 and r[1] != r[2] and len(r[1]) == len(r[2]): r[1], r[2] = r[2], r[1]
run(L2, 'ms_groups_swapped', 'child %s: residue multisets of groups 1,2 swapped (or unchanged if different sizes)' % d['id'])
# T-d: delete a deep child
L2 = copy.deepcopy(lines); nd = next(x for x in L2[1:] if x['id'] == par['id']); nd['c'] = [c for c in nd['c'] if c != d['id']]
run(L2, 'ms_deep_child_deleted', 'node %s: child %s removed' % (par['id'], d['id']))
# T-e: delete a deep child's subtree-less lift from rest (swap the order of kills irrelevant): replace 'rest' by only a prime that cannot kill
L2 = copy.deepcopy(lines); nd = next(x for x in L2[1:] if x['id'] == par['id']); nd['rest'] = [101]
run(L2, 'ms_deep_rest_weak', 'node %s: rest primes replaced by [101]' % par['id'])
json.dump(out, open('tamper2_results.json', 'w'), indent=1)
