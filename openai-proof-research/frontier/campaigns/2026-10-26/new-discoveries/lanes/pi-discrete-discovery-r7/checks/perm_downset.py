"""Search for a non-unimodal rank sequence (pattern counts) of a permutation.
Vatter 2602.16355 Conjecture 2.1 / MathDB 373197.
Rank sequence a_0..a_n: a_k = #{distinct patterns of length k}.
Pouzet-Rosenberg: a is weakly increasing up to n/2, so a violation needs
a_{k} < a_{k-1} for some k > n/2 (a dip after the middle).
"""
import sys, itertools, random

def rank_seq_fast(perm):
    """counts[k] = number of distinct patterns of length k, via DP over subsequences."""
    n = len(perm)
    # patterns represented as tuple of ranks; use dict keyed by length
    seen = [set() for _ in range(n+1)]
    seen[0].add(())
    # incremental: extend by inserting each new position? Simpler: iterate over all
    # subsequences via bitmask is 2^n; for n<=16 use recursive with memo on (prefix set)
    # Use the standard approach: for each subset... too slow. Use DP:
    # patterns of length k ending at position i: derived from patterns of length k-1
    # ending at j<i with smaller value. Represent pattern by its rank vector.
    # We do straightforward subset enumeration with early pruning for n<=18.
    counts = [0]*(n+1)
    counts[0] = 1
    for mask in range(1, 1 << n):
        k = bin(mask).count("1")
        sub = [perm[i] for i in range(n) if mask >> i & 1]
        # normalize
        order = {v: r for r, v in enumerate(sorted(sub))}
        seen[k].add(tuple(order[v] for v in sub))
    for k in range(1, n+1):
        counts[k] = len(seen[k])
    return counts

def is_unimodal(a):
    n = len(a)
    i = 0
    while i+1 < n and a[i+1] >= a[i]: i += 1
    while i+1 < n and a[i+1] <= a[i]: i += 1
    return i == n-1

def main():
    lim = int(sys.argv[1]) if len(sys.argv) > 1 else 11
    rng = random.Random(20261027)
    checked = 0
    for n in range(1, lim+1):
        for p in itertools.permutations(range(n)):
            checked += 1
            c = rank_seq_fast(p)
            if not is_unimodal(c):
                print("COUNTEREXAMPLE:", p, c); return
        print(f"all permutations up to n={n} checked ({checked} total), all unimodal")
    # random large
    viol = 0
    for trial in range(200000):
        n = rng.randint(12, 60)
        p = list(range(n)); rng.shuffle(p)
        # sample-based pattern counting via random subsequences is not exact;
        # use exact DP for n<=22 only
        if n <= 22:
            c = rank_seq_fast(p)
            checked += 1
            if not is_unimodal(c):
                print("COUNTEREXAMPLE:", p, c); viol += 1; break
    print(f"random exact checks (12<=n<=22): done, checked total {checked}, violations {viol}")

if __name__ == "__main__":
    main()
