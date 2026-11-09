# r8 verify_a2.py — brute-force cross-check of the 2-D one-far certificates.
# 1. For each of the 10 pairs: brute force all (L, q), 3 <= q < L <= 600, with
#    10^L + A*10^q + K 7-smooth; every such (L,q) with q >= qmin must be recorded
#    in the pair's certificate (sz leaves), and every recorded one must be found.
# 2. For the S_low=1 q=3 slice: brute force vs the recorded L of cert_K{9008,18008,27008}.
# 3. Global claim check: the only mixed solution is (S_low,A,q,L) = (1,27,3,5) -> 14112.
# Run: bash -c 'ulimit -v 3000000; python3 -I verify_a2.py'
import json

PAIRS = [(1, 9), (10, 9), (1, 18), (10, 18), (1, 27), (10, 27), (30, 27), (11, 9), (101, 9), (110, 9)]
LMAX = 600

def smooth237(x):
    for p in (2, 3, 7):
        while x % p == 0:
            x //= p
    return x == 1

def recs(fn):
    out = set()
    for i, line in enumerate(open(fn)):
        if i == 0:
            continue
        d = json.loads(line)
        if d.get("k") == "l" and "sz" in d["x"]:
            for z in d["x"]["L"]:
                out.add(tuple(z) if isinstance(z, list) else (z,))
    return out

ok = True
allsol = []
for S, A in PAIRS:
    K = 9 * S - 1
    t0 = (K & -K).bit_length() - 1
    qmin = max(3, t0 + 1)
    meta = json.loads(open(f"cert2d_S{S}_A{A}.jsonl").readline())
    assert (meta["A"], meta["K"], meta["qmin"]) == (A, K, qmin)
    R = recs(f"cert2d_S{S}_A{A}.jsonl")
    p10 = [10 ** i for i in range(LMAX + 2)]
    found = set()
    for L in range(qmin + 1, LMAX + 1):
        base = p10[L] + K
        for q in range(3, L):
            if smooth237(base + A * p10[q]):
                found.add((L, q))
    inscope = {(L, q) for (L, q) in found if q >= qmin}
    stat = "OK" if inscope == R else "MISMATCH"
    if stat != "OK":
        ok = False
    print(f"S={S} A={A} K={K} qmin={qmin}: brute(L<={LMAX},q>=qmin)={sorted(inscope)} recorded={sorted(R)} {stat}")
    # q=3 slice for K=8
    if K == 8:
        rs = {(L,) for (L,) in recs(f"cert_K{1000 * A + 8}.jsonl")}
        q3 = {(L,) for (L, q) in found if q == 3}
        stat2 = "OK" if q3 == rs else "MISMATCH"
        if stat2 != "OK":
            ok = False
        print(f"   q=3 slice (cert_K{1000*A+8}): brute={sorted(q3)} recorded={sorted(rs)} {stat2}")
    allsol += [(S, A, q, L) for (L, q) in found]
print("all solutions (S,A,q,L):", sorted(allsol))
for (S, A, q, L) in allsol:
    n = (10 ** L + A * 10 ** q + 9 * S - 1) // 9
    assert (10 ** L + A * 10 ** q + 9 * S - 1) % 9 == 0 and smooth237(n)
    print(f"  S={S} A={A} q={q} L={L}: n = {n}")
print("ALL CONSISTENT" if ok else "FAILURE")
