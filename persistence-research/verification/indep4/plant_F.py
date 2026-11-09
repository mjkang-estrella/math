# Planted-solution test: change K so that a genuine smooth solution exists in the domain; the unchanged tree must be rejected.
import json, sys, copy, random
sys.path.insert(0, '.')
import check_sym_F as F
rnd = random.Random(5)
lines = [json.loads(l) for l in open('../highdim/sym/certs/decimal_full/K5723_q3_c9_9_9_18_18.jsonl')]
rej = 0
for trial in range(12):
    L = rnd.randrange(9, 14); pos = rnd.sample(range(3, L), 5)
    X0 = 10 ** L + sum(9 * 10 ** q for q in pos[:3]) + sum(18 * 10 ** q for q in pos[3:])
    while True:
        a = rnd.randrange(0, 60); w = rnd.randrange(0, 25); N = 3 ** a * 7 ** w
        if X0 < N < 4 * X0: break
    L2 = copy.deepcopy(lines); L2[0]['K'] = N - X0
    p = 'tamper/tmpP.jsonl'
    open(p, 'w').write(''.join(json.dumps(x) + '\n' for x in L2))
    ct, cl, br = F.check(p, 14)
    rej += bool(ct.problems)
    print(trial, 'planted L=%d positions=%s N=3^%d*7^%d' % (L, pos, a, w), 'REJECTED' if ct.problems else 'ACCEPTED')
print('rejected', rej, 'of 12')
