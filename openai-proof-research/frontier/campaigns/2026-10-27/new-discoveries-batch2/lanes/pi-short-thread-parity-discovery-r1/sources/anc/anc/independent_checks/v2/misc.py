"""(1) carry-free identity of Section 11; (2) prop:blockedleg on random status-labelled gadgets
via direct brute force of the labelled-forest arrow game (Def. 3.3 / Lemma 3.2)."""
import random, sys
from raw import labelled_forest_grundy

# (1) identity
bad = 0
for n in range(0, 2001):
    lhs = {t ^ (n - t) for t in range(n + 1)}
    rhs = {e for e in range(n + 1) if (e - n) % 2 == 0 and (e & ((n - e) // 2)) == 0}
    if lhs != rhs:
        bad += 1
        if bad < 5:
            print('identity FAIL', n, sorted(lhs ^ rhs)[:10])
print('carry-free identity n<=2000: failures =', bad)

# (2) random gadgets
random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
NG = int(sys.argv[2]) if len(sys.argv) > 2 else 40
KMAX = int(sys.argv[3]) if len(sys.argv) > 3 else 8
tot_viol = 0
for g in range(NG):
    nK = random.randint(1, 6)
    edges = [(random.randrange(v), v) for v in range(1, nK)]
    status = [random.choice('nf') for _ in range(nK)]
    c = random.randrange(nK)
    status[c] = 'n'
    h = {}
    for k in range(1, KMAX + 1):
        nv = nK + k
        e2 = list(edges)
        prev = c
        for m in range(1, k + 1):
            e2.append((prev, nK + m - 1))
            prev = nK + m - 1
        st = status + ['n'] * (k - 1) + ['i']
        h[k] = labelled_forest_grundy(nv, e2, st)
        # reversal claim: far end 'o' gives same value
        st2 = status + ['n'] * (k - 1) + ['o']
        if labelled_forest_grundy(nv, e2, st2) != h[k]:
            print('reversal FAIL', g, k)
            tot_viol += 1
    viol = 0
    for k in range(2, KMAX + 1):
        forb = {h[k - 1]} | {h[kp] for kp in range(1, k - 1)} | {h[kp] ^ 1 for kp in range(1, k - 1)}
        if h[k] in forb:
            viol += 1
    tot_viol += viol
    print(f'gadget {g}: K edges={edges} status={"".join(status)} c={c} h={[h[k] for k in range(1, KMAX + 1)]} viol={viol}')
print('random gadgets: total violations =', tot_viol)
