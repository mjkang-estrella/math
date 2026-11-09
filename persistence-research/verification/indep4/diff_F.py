# Differential test: my Cert.kills() vs M's Checker.killed() on random classes / parameters.  python3 -I diff_F.py [seed] [n]
import sys, json, random, os, tempfile, collections
sys.dont_write_bytecode = True
sys.path.insert(0, '.')
sys.path.insert(0, '../highdim/sym')
import check_sym_F as F
import check_sym as Msym          # M's checker (module import only; used as a black box)
seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
N = int(sys.argv[2]) if len(sys.argv) > 2 else 400
rnd = random.Random(seed)
tmp = tempfile.mkdtemp(prefix='diffF_')
def mk(groups, K, qmin, pin2, k):
    meta = dict(k='meta', format='nd-sym', version=1, domain='unordered', scope='full', groups=[list(g) for g in groups], K=K, qmin=qmin,
                dim=1 + sum(m for _, m in groups), pin2=pin2, root=dict(r=[0] + [[0] * m for _, m in groups], m=1))
    if k: meta['pin_digits'] = k
    path = os.path.join(tmp, 'c%d.jsonl' % rnd.randrange(10 ** 9))
    with open(path, 'w') as fh:
        fh.write(json.dumps(meta) + '\n')
        fh.write(json.dumps(dict(id=0, p=-1, m=1, r=meta['root']['r'], k='l', x=dict(prime=11))) + '\n')
    mine = F.Cert(meta); theirs = Msym.Checker(path, 6)
    assert not mine.problems, mine.problems
    return mine, theirs
primes = [p for p in range(11, 700) if F.isprime(p)] + [9901, 333667, 3541, 27961, 99990001, 98641, 73, 137, 101]
Ms = [1, 2, 4, 6, 12, 18, 36, 42, 72, 84, 126, 144, 216, 252, 432, 504, 756, 1008]
tot = 0; agree = 0; kills = collections.Counter(); dis = []
kinds = collections.Counter()
for it in range(N):
    if it and it % 5 == 0: print('PROGRESS', it, tot, agree, flush=True)
    t0 = rnd.choice([0, 0, 0, 1, 2, 3, 5])
    qmin = rnd.choice([t0 + 1, t0 + 2, t0 + 3, t0 + 3, max(3, t0 + 3)])
    qmin = max(qmin, t0 + 1)
    pin2 = qmin >= t0 + 3 and rnd.random() < 0.6
    k = rnd.choice([0, 0, 1, 2, 3]); k = min(k, qmin, 3)
    G = rnd.choice([1, 2, 3, 4])
    coefs = sorted(rnd.sample([9, 18, 27, 45, 54, 63, 72], G)); groups = [(c, rnd.choice([1, 1, 2, 3])) for c in coefs]
    while sum(m for _, m in groups) > 7: groups[0] = (groups[0][0], 1)
    K = (rnd.randrange(1, 4000) * 2 + 1) << t0
    if K % 5 == 0: K += 2 << t0
    mine, theirs = mk(groups, K, qmin, pin2, k)
    print('cert', it, groups, K, qmin, pin2, k, 'so far', tot, agree, flush=True)
    for M in rnd.sample(Ms, 5):
        for _ in range(20):
            cls = (rnd.randrange(M),) + tuple(tuple(sorted(rnd.randrange(M) for _ in range(m))) for _, m in groups)
            for p in rnd.sample(primes, 12):
                try: a = mine.kills(p, cls, M)[0]
                except OverflowError: kills['skipped-large-sumset'] += 1; continue
                b = theirs.killed(p, cls, M)
                tot += 1; agree += (a == b); kills[(a, b)] += 1
                if a != b: dis.append((groups, K, qmin, pin2, k, M, cls, p, a, b))
print('seed', seed, 'compared', tot, 'agree', agree, 'kill-pair counts (mine,theirs):', {str(k): v for k, v in kills.items()})
for x in dis[:10]: print('DISAGREE', x)
sys.exit(1 if dis else 0)
