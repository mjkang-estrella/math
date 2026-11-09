# r8 verify_a1.py — brute-force cross-check of the 17 all-low certificates.
# For each K: find ALL L <= 3000 with 10^L + K = 7-smooth (2^t 3^a 7^w), and compare
# with the union of sz-leaf recorded L (the certificates claim: exactly these, all <= t0).
# Run: bash -c 'ulimit -v 3000000; python3 -I verify_a1.py'
import json

KS = [98, 908, 989, 107, 917, 1079, 1808, 1889, 2708, 2789, 926, 1169, 197, 1817, 1979, 998, 116]
LB = 3000
ok = True
for K in KS:
    rec = set()
    for line in open(f"cert_K{K}.jsonl"):
        d = json.loads(line)
        if d.get("k") == "l" and "sz" in d["x"]:
            rec.update(d["x"]["L"])
    t0 = (K & -K).bit_length() - 1
    found = []
    x = 1
    for L in range(1, LB + 1):
        x *= 10
        y = x + K
        for p in (2, 3, 7):
            while y % p == 0:
                y //= p
        if y == 1:
            found.append(L)
    # also L = 0
    y = 1 + K
    for p in (2, 3, 7):
        while y % p == 0:
            y //= p
    if y == 1:
        found.append(0)
        found.sort()
    stat = "OK" if set(found) == rec and all(L <= t0 for L in found) else "MISMATCH"
    if stat != "OK":
        ok = False
    print(f"K={K}: t0={t0} brute(L<={LB})={found} recorded={sorted(rec)} {stat}")
print("ALL CONSISTENT" if ok else "FAILURE")
