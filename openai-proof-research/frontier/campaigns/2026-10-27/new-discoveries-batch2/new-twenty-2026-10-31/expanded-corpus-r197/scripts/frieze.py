"""Search for counterexamples to Banaian-Chen Conjecture 9.5 (arXiv:2106.06679, MathDB 350973):
infinite periodic frieze patterns of Type Lambda (quiddity m_{i-1,i+1} = sum_{p in A_i} lambda_p,
lambda_p = 2cos(pi/p)) that PASS the realizability test (Prop. 4.2) yet have a nonpositive entry
(other than a full zero row, which would make the frieze finite).
Float diagnostic only.  usage: frieze.py maxperiod maxp maxmult rows"""
import sys, math, itertools, json
N, PMAX, MULT, ROWS = map(int, sys.argv[1:5])
lam = {p: 2 * math.cos(math.pi / p) for p in range(3, PMAX + 1)}
atoms = []
for k in range(1, MULT + 1):
    atoms += list(itertools.combinations_with_replacement(range(3, PMAX + 1), k))

def passes(As):
    n = len(As)
    for i in range(n):
        if not set(As[i]) & set(As[(i + 1) % n]):
            return False
    for p in range(3, PMAX + 1):
        single = [a == (p,) for a in As]
        if all(single):
            continue
        if not any(single):
            continue
        # longest cyclic run of singletons {p}
        run = best = 0
        for s in single + single:
            run = run + 1 if s else 0
            best = max(best, run)
        if best > p - 2:
            return False
    return True

def skeletal(As):
    n = len(As)
    for p in range(3, PMAX + 1):
        single = [a == (p,) for a in As]
        if all(single):
            return False
        run = best = 0
        for x in single + single:
            run = run + 1 if x else 0
            best = max(best, run)
        if best >= p - 2:
            return False
    return True

def prop44ii(As):
    # exists choice p_{i,i+1} in A_i & A_{i+1} with: if |A_i|>1 and p_{i-1,i}=p_{i,i+1} then multiplicity>=2 in A_i
    n = len(As)
    opts = [sorted(set(As[i]) & set(As[(i + 1) % n])) for i in range(n)]
    def ok(ch):
        for i in range(n):
            a, b = ch[(i - 1) % n], ch[i]
            if len(As[i]) > 1 and a == b and As[i].count(a) < 2:
                return False
        return True
    return any(ok(ch) for ch in itertools.product(*opts))

def canon(As):
    n = len(As)
    rots = [tuple(As[i:] + As[:i]) for i in range(n)]
    rots += [tuple(reversed(r)) for r in rots]
    return min(rots)

found = []; checked = 0; finite = 0
for n in range(1, N + 1):
    seen = set()
    for As in itertools.product(atoms, repeat=n):
        As = list(As)
        if any(len(a) > 1 for a in As) and all(len(a) > 1 for a in As):
            continue  # all entries >= 2: positive by Prop. 9.2
        c = canon(As)
        if c in seen: continue
        seen.add(c)
        # primitive period only
        if any(n % d == 0 and As == As[d:] + As[:d] for d in range(1, n)):
            continue
        if not passes(As):
            continue
        checked += 1
        q = [sum(lam[p] for p in a) for a in As]
        # m[i][k] = m_{i, i+k}
        bad = None; zero_row = False
        rowsvals = []
        cur_prev = [0.0] * n; cur = [1.0] * n
        for k in range(2, ROWS + 2):
            nxt = []
            for i in range(n):
                j = i + k - 1           # m_{i,j+1} = c_j m_{i,j} - m_{i,j-1}, c_j = quiddity at j
                nxt.append(q[j % n] * cur[i] - cur_prev[i])
            if all(abs(x) < 1e-9 for x in nxt):
                zero_row = True; break
            if any(x < 1e-9 for x in nxt):
                bad = (k, [round(x, 6) for x in nxt]); break
            cur_prev, cur = cur, nxt
        if zero_row:
            finite += 1
            continue
        if bad:
            found.append(dict(skeletal=skeletal(As), prop44ii=prop44ii(As), A=As, quiddity=[round(x, 6) for x in q], first_nonpositive_row=bad))
print(json.dumps(dict(params=dict(maxperiod=N, pmax=PMAX, mult=MULT, rows=ROWS), checked=checked,
                      finite_friezes=finite, counterexample_count=len(found), skeletal_negatives=[f for f in found if f['skeletal']][:30], skeletal_count=sum(f['skeletal'] for f in found), examples=found[:10])))
