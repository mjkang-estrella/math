"""Independent method H ("top-max subtraction recursion"), written from the mathematics in
REVIEW.md section B, not from the r133 lane scripts.

Objects: ordered pairs (F, F') of binary plane forests on the common postorder positions
1..M, with r and s trees, together with a labelling w : [M] -> [M] (bijection) that
decreases from parent to child in BOTH forests.  XI[M][r][s] counts all such triples,
II[M][r][s] those whose pair is irreducible (no position c in [2, M] that starts a tree in
both forests).  P_n = XI[n][1][1] = II[n][1][1].

Facts used (proved in REVIEW.md):
 (i)  no comparability crosses a common cut, so a pair is the concatenation of a prefix
      pair and a last irreducible block, labellings shuffle: factor C(M, m2);
 (ii) in an irreducible pair every position lies below position M, so every admissible
      labelling has w(M) = M;
 (iii) KI[M][r][s] := #(pair, labelling) with w(M) = M equals
      sum_{t,u in {0,1,2}} mu(t) mu(u) XI[M-1][r-1+t][s-1+u], mu = (1, 2, 1)
      (delete the common last root), and also equals
      sum_{m2} C(M-1, m2-1) * sum XI[M-m2][r-r2][s-s2] * II[m2][r2][s2]
      (the label M sits at position M, inside the last block, which is irreducible).
Hence II[M] = KI[M] - sum_{m2<M} C(M-1, m2-1) conv, XI[M] = II[M] + sum_{m2<M} C(M, m2) conv.
No hook-length formula and no cumulative-count irreducibility criterion are used.

Usage: topmax.py N mode [checkpoint_in] [stop_M]
  mode 'naive' : plain integer 4-fold loops (for cross-checking)
  mode 'packed': rows packed into big integers (Kronecker substitution) for speed.
Range pruning: only r, s <= min(M, N+1-M) are needed for P_N."""
import sys, json, time
from math import comb

N = int(sys.argv[1])
mode = sys.argv[2]
ckpt_in = sys.argv[3] if len(sys.argv) > 3 and sys.argv[3] != '-' else None
stop_M = int(sys.argv[4]) if len(sys.argv) > 4 else N
MU = (1, 2, 1)
T0 = time.time()


def bound(M):
    return min(M, N + 1 - M)


XI = {0: [[1]]}
II = {0: [[0]]}
startM = 1
if ckpt_in:
    d = json.load(open(ckpt_in))
    assert d["N"] == N and d["mode_compatible"]
    XI = {int(k): [[int(x) for x in row] for row in v] for k, v in d["XI"].items()}
    II = {int(k): [[int(x) for x in row] for row in v] for k, v in d["II"].items()}
    startM = d["next_M"]


def get(A, M, r, s):
    a = A.get(M)
    if a is None or r >= len(a) or s >= len(a[r]) or r < 0 or s < 0:
        return 0
    return a[r][s]


def pack(row, W):
    v = 0
    for i in range(len(row) - 1, -1, -1):
        v = (v << W) | row[i]
    return v


def unpack(v, W, k):
    mask = (1 << W) - 1
    out = []
    for _ in range(k):
        out.append(v & mask)
        v >>= W
    return out


P = {}
for M in range(startM, stop_M + 1):
    Bm = bound(M)
    KI = [[0] * (Bm + 1) for _ in range(Bm + 1)]
    for r in range(1, Bm + 1):
        for s in range(1, Bm + 1):
            tot = 0
            for t in range(3):
                for u in range(3):
                    tot += MU[t] * MU[u] * get(XI, M - 1, r - 1 + t, s - 1 + u)
            KI[r][s] = tot
    C1 = [[0] * (Bm + 1) for _ in range(Bm + 1)]  # sum C(M-1,m2-1) conv
    C2 = [[0] * (Bm + 1) for _ in range(Bm + 1)]  # sum C(M,m2) conv
    if mode == "naive":
        for m2 in range(1, M):
            Ma = M - m2
            c1, c2 = comb(M - 1, m2 - 1), comb(M, m2)
            Ib, Xa = II[m2], XI[Ma]
            for r in range(1, Bm + 1):
                for s in range(1, Bm + 1):
                    acc = 0
                    for r2 in range(1, min(r - 1, len(Ib) - 1) + 1):
                        ra = r - r2
                        if ra >= len(Xa):
                            continue
                        rowI, rowX = Ib[r2], Xa[ra]
                        for s2 in range(1, min(s - 1, len(rowI) - 1) + 1):
                            sa = s - s2
                            if sa < len(rowX):
                                acc += rowX[sa] * rowI[s2]
                    if acc:
                        C1[r][s] += c1 * acc
                        C2[r][s] += c2 * acc
    else:
        mxX = max((x.bit_length() for k in XI if k < M for row in XI[k] for x in row), default=1)
        mxI = max((x.bit_length() for k in II if k < M for row in II[k] for x in row), default=1)
        W = mxX + mxI + M + 2 * (Bm + 1).bit_length() + 4
        pX = {k: [pack(row, W) for row in XI[k]] for k in XI if 1 <= k < M}
        pI = {k: [pack(row, W) for row in II[k]] for k in II if 1 <= k < M}
        A1 = [0] * (Bm + 1)
        A2 = [0] * (Bm + 1)
        for m2 in range(1, M):
            Ma = M - m2
            c1, c2 = comb(M - 1, m2 - 1), comb(M, m2)
            Ib, Xa = pI[m2], pX[Ma]
            for r in range(2, Bm + 1):
                acc = 0
                for r2 in range(1, min(r - 1, len(Ib) - 1) + 1):
                    ra = r - r2
                    if ra < len(Xa) and Ib[r2] and Xa[ra]:
                        acc += Xa[ra] * Ib[r2]
                if acc:
                    A1[r] += c1 * acc
                    A2[r] += c2 * acc
        for r in range(Bm + 1):
            if A1[r]:
                u1 = unpack(A1[r], W, Bm + 1)
                u2 = unpack(A2[r], W, Bm + 1)
                for s in range(Bm + 1):
                    C1[r][s] = u1[s]
                    C2[r][s] = u2[s]
    IIM = [[0] * (Bm + 1) for _ in range(Bm + 1)]
    XIM = [[0] * (Bm + 1) for _ in range(Bm + 1)]
    for r in range(1, Bm + 1):
        for s in range(1, Bm + 1):
            v = KI[r][s] - C1[r][s]
            assert v >= 0, (M, r, s)
            IIM[r][s] = v
            XIM[r][s] = v + C2[r][s]
    # symmetry sanity (swap the two forests)
    for r in range(1, Bm + 1):
        for s in range(1, Bm + 1):
            assert XIM[r][s] == XIM[s][r] and IIM[r][s] == IIM[s][r]
    XI[M], II[M] = XIM, IIM
    assert XIM[1][1] == IIM[1][1]
    P[M] = XIM[1][1]
    print("M", M, "B", Bm, "t", round(time.time() - T0, 2), "P", XIM[1][1], flush=True)

if stop_M < N:
    json.dump({"N": N, "mode_compatible": True, "next_M": stop_M + 1,
               "XI": {k: [[str(x) for x in row] for row in v] for k, v in XI.items()},
               "II": {k: [[str(x) for x in row] for row in v] for k, v in II.items()}},
              open(f"outputs/topmax_ckpt_N{N}_M{stop_M}.json", "w"))
    print("checkpoint written", stop_M)
else:
    PN = XI[N][1][1]
    print("P_%d" % N, PN)
    allP = {M: str(XI[M][1][1]) for M in sorted(XI) if M >= 1}
    json.dump({"N": N, "mode": mode, "P": allP}, open(f"outputs/topmax_P{N}_{mode}.json", "w"), indent=1)
