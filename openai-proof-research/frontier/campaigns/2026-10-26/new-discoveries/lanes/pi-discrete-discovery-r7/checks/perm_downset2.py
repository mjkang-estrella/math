"""Exact rank-sequence unimodality check for permutations (Vatter Conj 2.1 / MathDB 373197).
DP: S_i[k] = set of distinct patterns of length k in prefix of length i.
Update at position i with value v: S_i[k] = S_{i-1}[k] union {insert rank r=min(v,k-1) at end-rank of q: q in S_{i-1}[k-1]}.
Wait: appending value v AFTER a normalized pattern q of length k-1: normalized insertion index r = #{q_j < v} = min(v, k-1) is WRONG in general:
v is the actual value in pi; q entries are 0..k-2; r = min(v, k-1) counts q_j < v among 0..k-2 values = min(v, k-1). Correct.
"""
import sys, itertools, random, time

def rank_counts(perm):
    n = len(perm)
    S = [set() for _ in range(n+1)]
    S[0].add(())
    counts = [0]*(n+1)
    counts[0] = 1
    for i, v in enumerate(perm):
        newS = [set(x) for x in S]
        for k in range(1, i+2):
            r = min(v, k-1)
            add = {q[:r] + (r,) + q[r:] for q in S[k-1]}
            newS[k] |= add
        S = newS
        for k in range(i+2): counts[k] = len(S[k])
    return counts

def is_unimodal(a):
    n = len(a); i = 0
    while i+1 < n and a[i+1] >= a[i]: i += 1
    while i+1 < n and a[i+1] <= a[i]: i += 1
    return i == n-1

def syms(p):
    n = len(p)
    inv = [0]*n
    for i, v in enumerate(p): inv[v] = i
    comp = [n-1-v for v in p]
    rev = p[::-1]
    rc = comp[::-1]
    invc = [n-1-v for v in inv]
    return [p, tuple(comp), tuple(rev), tuple(rc), tuple(inv), tuple(invc),
            tuple(rev and inv[::-1]), tuple(inv[::-1])]

def main():
    mode = sys.argv[1]
    rng = random.Random(20261027)
    t0 = time.time()
    if mode == "exhaustive":
        lim = int(sys.argv[2])
        seen = set()
        for n in range(1, lim+1):
            cnt = 0
            for p in itertools.permutations(range(n)):
                if p in seen: continue
                seen.update(syms(p))
                cnt += 1
                c = rank_counts(p)
                if not is_unimodal(c):
                    print("COUNTEREXAMPLE:", p, c); return
            print(f"n={n}: {cnt} canonical perms checked, all unimodal ({time.time()-t0:.0f}s)")
    else:
        lo, hi, trials = int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4])
        viol = 0
        for t in range(trials):
            n = rng.randint(lo, hi)
            p = list(range(n)); rng.shuffle(p)
            c = rank_counts(p)
            if not is_unimodal(c):
                print("COUNTEREXAMPLE:", p, c); viol += 1; break
            if t % 50 == 49: print(f"{t+1} random perms ok ({time.time()-t0:.0f}s)")
        print(f"done: {trials} random perms in [{lo},{hi}], violations={viol}")

if __name__ == "__main__":
    main()
