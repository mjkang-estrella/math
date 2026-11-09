# r6 v1_H.py — certificate for Lemma H (all non-1 digits at positions >= 3)
# Checks:
#  (C1) mod-8 table: 3^u*7^w mod 8 for u,w parities; 7 iff (u even, w odd)
#  (C2) mod-5 table: 3^u*7^w == 1 (mod 5) iff w ≡ u (mod 4)
#  (C3) for every placement of {2,2},{2,3},{2,4},{3,3},{2,2,2} with all positions >= 3,
#       S ≡ 0 (mod 1000), hence 9n ≡ -1 (mod 8) and (mod 5) for L >= 4.
#  (C4) exhaustive brute-force cross-check: no 7-smooth member with all non-1
#       positions >= 3, for all multisets, L <= 60 (sanity, not the proof).
# Run: bash -c 'ulimit -v 3000000; python3 -I v1_H.py'

def factor7smooth(x):
    """return (t,u,w,cofactor) with x = 2^t 3^u 7^w * cofactor"""
    t = u = w = 0
    while x % 2 == 0: x //= 2; t += 1
    while x % 3 == 0: x //= 3; u += 1
    while x % 7 == 0: x //= 7; w += 1
    return t, u, w, x

print("== C1: 3^u*7^w mod 8, by parity ==")
ok = True
for ue in (0, 1):
    for we in (0, 1):
        u, w = ue, we  # parities
        # representative: u=0/1, w=0/1 works since 3^2≡1, 7^2≡1 mod 8
        val = (3**u * 7**w) % 8
        tag = ("u %s, w %s" % ("even" if ue == 0 else "odd", "even" if we == 0 else "odd"))
        hit = (val == 7)
        print(f"  {tag}: value={val}  {'<== ==7' if hit else ''}")
        if hit and not (ue == 0 and we == 1): ok = False
        if not hit and (ue == 0 and we == 1): ok = False
print("C1", "PASS" if ok else "FAIL")

print("== C2: 3^u*7^w ≡ 1 (mod 5) iff u ≡ w (mod 4) ==")
ok = True
for u in range(4):
    for w in range(4):
        val = (3**u * 7**w) % 5
        cond = (u % 4 == w % 4)
        if (val == 1) != cond: ok = False; print(f"  VIOLATION u={u} w={w} val={val}")
print("  (16 cases)")
print("C2", "PASS" if ok else "FAIL")

print("== C3: S ≡ 0 mod 1000 for all-multisets positions>=3; 9n ≡ -1 mod 8,5 ==")
multisets = {
    "{2,2}":   [1, 1],
    "{2,3}":   [1, 2],
    "{2,4}":   [1, 3],
    "{3,3}":   [2, 2],
    "{2,2,2}": [1, 1, 1],
}
ok = True
# enumerate all assignments of the c-values to positions all >= 3 (positions 3..8
# plus check pattern: any set of distinct positions >= 3 gives S ≡ 0 mod 1000 since
# each term c*10^p with p>=3 is divisible by 1000. Check the general claim directly:
for p in range(3, 12):
    for c in (1, 2, 3):
        if (c * 10**p) % 1000 != 0: ok = False
print("  each c*10^p (p>=3) divisible by 1000:", "PASS" if ok else "FAIL")
# so S ≡ 0 mod 8 and mod 5; with L>=4, 10^L ≡ 0 mod 40; 9n ≡ -1 mod 8 and mod 5.
ok = True
for L in range(4, 12):
    if 10**L % 8 != 0 or 10**L % 5 != 0: ok = False
print("  10^L ≡ 0 mod 8,5 for L>=4:", "PASS" if ok else "FAIL")

print("== C4: brute-force cross-check, all non-1 positions >= 3, L <= 60 ==")
found = []
for name, cvals in multisets.items():
    k = len(cvals)
    import itertools
    for L in range(4, 61):
        # choose k distinct positions in [3, L-1]
        for positions in itertools.combinations(range(3, L), k):
            for perm in set(itertools.permutations(cvals)):
                S = sum(c * 10**p for c, p in zip(perm, positions))
                x = 10**L + 9 * S - 1
                t, u, w, cof = factor7smooth(x)
                if cof == 1:
                    found.append((name, L, positions, perm, (t, u, w)))
print("  members found with all non-1 positions >= 3:", found if found else "NONE")
print("C4", "PASS" if not found else "FOUND ITEMS (must be none)")

print("done")
