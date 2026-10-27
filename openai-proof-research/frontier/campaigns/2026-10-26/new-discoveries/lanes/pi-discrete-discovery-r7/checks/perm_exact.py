"""Exact pattern-count unimodality check via bitmask enumeration (numpy).
a_k = #distinct normalized subsequences of length k. Violation iff a dips after
its peak; by Pouzet-Rosenberg a is increasing up to n/2, so check full sequence."""
import numpy as np, itertools, sys, random, time

def rank_counts_np(p):
    n = len(p)
    arr = np.array(p)
    counts = [1]
    for k in range(1, n+1):
        idx = np.array(list(itertools.combinations(range(n), k)), dtype=np.int64) if k>0 else None
        if k <= n:
            sub = arr[idx]  # (C(n,k), k)
            order = np.argsort(np.argsort(sub, axis=1), axis=1)
            pats = np.unique(order, axis=0)
            counts.append(len(pats))
    return counts

def is_unimodal(a):
    n=len(a); i=0
    while i+1<n and a[i+1]>=a[i]: i+=1
    while i+1<n and a[i+1]<=a[i]: i+=1
    return i==n-1

def main():
    rng = random.Random(42)
    t0=time.time()
    # exhaustive n<=10 with symmetry reduction
    for n in range(3, 11):
        cnt=0
        for p in itertools.permutations(range(n)):
            # canonical under dihedral-like 8 symmetries (inverse preserves counts too)
            s = [p, tuple(n-1-v for v in p), p[::-1], tuple(n-1-v for v in p[::-1])]
            inv=[0]*n
            for i,v in enumerate(p): inv[v]=i
            s.append(tuple(inv)); s.append(tuple(n-1-v for v in inv))
            s.append(tuple(inv[::-1])); s.append(tuple(n-1-v for v in inv[::-1]))
            if p != min(s): continue
            cnt+=1
            c = rank_counts_np(p)
            if not is_unimodal(c):
                print("COUNTEREXAMPLE:", p, c); return
        print(f"n={n}: {cnt} canonical checked, all unimodal ({time.time()-t0:.0f}s)")
    # random n in [11,22]
    for t in range(150):
        n = rng.randint(11,22)
        p = list(range(n)); rng.shuffle(p)
        c = rank_counts_np(p)
        if not is_unimodal(c):
            print("COUNTEREXAMPLE:", p, c); return
    print(f"150 random perms n in [11,22]: all unimodal ({time.time()-t0:.0f}s)")
    # structured families: layered with random compositions, n up to 30? bitmask 2^30 too big; cap 2^22
    for t in range(60):
        n = rng.randint(11,21)
        # layered: decreasing blocks
        comps = []; rem = n
        while rem>0:
            b = rng.randint(1, rem); comps.append(b); rem-=b
        p=[]; cur=n
        for b in comps:
            p.extend(range(cur-b, cur)); cur-=b
        c = rank_counts_np(p)
        if not is_unimodal(c):
            print("COUNTEREXAMPLE layered:", comps, c); return
    print(f"60 random layered perms n in [11,21]: all unimodal ({time.time()-t0:.0f}s)")

if __name__ == "__main__":
    main()
