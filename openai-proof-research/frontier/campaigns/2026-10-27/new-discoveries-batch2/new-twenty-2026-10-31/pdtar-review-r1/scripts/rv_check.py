"""Independent reviewer checker for MathDB 353203 (lane pdtar-review-r1).

Written from scratch; does NOT import or read the proof lane's scripts.
Power domination follows the source definition (arXiv:2201.01798, Sec. 1):
P^0[S]=S, P^1[S]=N[S], P^i[S]=P^{i-1}[S] u {u : N(v)\\P^{i-1}[S]={u}, v in P^{i-1}[S]}
(simultaneous rounds). Fort: nonempty F with |N(v) n F| != 1 for all v not in F.

Subcommands
  exh s t [fix chunk_lo chunk_hi]  all graphs on A={0..s-1}, B={s..s+t-1};
        bit-sliced over graphs (one bit per graph). With fix>0 the top `fix`
        edge bits are fixed per chunk, chunks chunk_lo..chunk_hi-1.
  lemma0 n lo hi                     Lemma 0 on all graphs on n vertices with
                                     index in [lo,hi), every subset S.
"""
import sys, json, time, itertools, os
SKIP_L1A = os.environ.get("RV_SKIP_L1A") == "1"

def edges_of(n):
    return [(i, j) for i in range(n) for j in range(i + 1, n)]

def pc(x):
    return bin(x).count("1")

def slice_int(e, m):
    N = 1 << m
    if e < 3:
        return int.from_bytes(bytes([[0xAA, 0xCC, 0xF0][e]]) * (N // 8), "little")
    blk = (1 << e) // 8
    pat = b"\x00" * blk + b"\xff" * blk
    return int.from_bytes(pat * (N // (2 << e)), "little")

# ---------- per-graph primitives ----------
def nb_of(n, g, E):
    nb = [0] * n
    for e, (i, j) in enumerate(E):
        if (g >> e) & 1:
            nb[i] |= 1 << j
            nb[j] |= 1 << i
    return nb

def closure(n, nb, S):
    if S == 0:
        return 0
    P = S
    for v in range(n):
        if (S >> v) & 1:
            P |= nb[v]
    while True:
        add = 0
        for v in range(n):
            if (P >> v) & 1:
                r = nb[v] & ~P
                if r and (r & (r - 1)) == 0:
                    add |= r
        if not add:
            return P
        P |= add

def Nc(n, nb, X):
    r = X
    for v in range(n):
        if (X >> v) & 1:
            r |= nb[v]
    return r

def forts(n, nb):
    full = (1 << n) - 1
    out = []
    for F in range(1, full + 1):
        ok = True
        for v in range(n):
            if not (F >> v) & 1 and pc(nb[v] & F) == 1:
                ok = False
                break
        if ok:
            out.append(F)
    return out

# ---------- bit-sliced PD over all graphs ----------
def bs_pd(n, EM, S, ALL):
    P = [ALL if (S >> w) & 1 else 0 for w in range(n)]
    P1 = P[:]
    for v in range(n):
        if (S >> v) & 1:
            for w in range(n):
                if w != v:
                    P1[w] |= EM[v][w]
    P = P1
    while True:
        new = P[:]
        for v in range(n):
            Pv = P[v]
            if not Pv:
                continue
            ones = 0
            twos = 0
            xs = [0] * n
            for w in range(n):
                if w == v:
                    continue
                x = EM[v][w] & (ALL ^ P[w])
                xs[w] = x
                twos |= ones & x
                ones |= x
            ex = ones & (ALL ^ twos) & Pv
            if not ex:
                continue
            for w in range(n):
                if w != v and xs[w]:
                    new[w] |= ex & xs[w]
        if new == P:
            break
        P = new
    r = ALL
    for w in range(n):
        r &= P[w]
    return r

def set_bits(x):
    s = bin(x)[2:][::-1]
    return [i for i, c in enumerate(s) if c == "1"]

# ---------- lemma checks on one graph ----------
def lemma_checks(n, s, t, nb, flags, fl):
    A = (1 << s) - 1
    B = ((1 << n) - 1) ^ A
    Av = list(range(s)); Bv = list(range(s, n))
    beta = {a: nb[a] & B for a in Av}
    alpha = {b: nb[b] & A for b in Bv}
    res = {}
    need_forts = (flags["H12"] and not SKIP_L1A) or flags["HA"] or flags["HB"] or flags["H2"]
    FS = forts(n, nb) if need_forts else []
    NF = [(F, Nc(n, nb, F)) for F in FS]
    if flags["H12"] and not SKIP_L1A:
        ok = all(((A & ~N) == 0 and pc(N & B) >= 2) or ((B & ~N) == 0 and pc(N & A) >= 2) for F, N in NF)
        res["L1a"] = ok
    if flags["HA"]:
        res["L2A"] = all(any(N == (B | (1 << x) | (1 << y)) for F, N in NF) for x, y in itertools.combinations(Av, 2))
        res["L3A"] = all(beta[a] for a in Av)
        res["L4B"] = not any(pc(nb[b]) == 1 and (nb[b] & A) for b in Bv)
    if flags["HB"]:
        res["L2B"] = all(any(N == (A | (1 << x) | (1 << y)) for F, N in NF) for x, y in itertools.combinations(Bv, 2))
        res["L3B"] = all(alpha[b] for b in Bv)
        res["L4A"] = not any(pc(nb[a]) == 1 and (nb[a] & B) for a in Av)
    if flags["H2"]:
        deg1 = [a for a in Av if pc(beta[a]) == 1] + [b for b in Bv if pc(alpha[b]) == 1]
        if (s, t) != (3, 3):
            res["L5"] = not deg1
            res["Cor5p"] = all(pc(beta[a]) >= 2 for a in Av) and all(pc(alpha[b]) >= 2 for b in Bv)
            res["L6"] = all(beta[a] == B for a in Av)
            # Lemma 6 intermediate: every fort with N[Phi]=A+{b,b'} misses A
            res["L6int"] = all((F & A) == 0 for F, N in NF if (N & A) == A and pc(N & B) == 2 and (N & ~(A | B)) == 0 and pc(N) == s + 2)
        else:
            ok = True
            for a in Av:
                if pc(beta[a]) == 1:
                    c = beta[a].bit_length() - 1
                    ok &= (nb[a] & A) == (A ^ (1 << a))
                    ok &= alpha[c] == (1 << a)
                    ok &= all((nb[y] & A) == (1 << a) for y in Av if y != a)
                    ok &= (nb[c] & B) == (B ^ (1 << c))
                    ok &= all((nb[b] & B) == (1 << c) for b in Bv if b != c)
            for b in Bv:
                if pc(alpha[b]) == 1:
                    c = alpha[b].bit_length() - 1
                    ok &= (nb[b] & B) == (B ^ (1 << b))
                    ok &= beta[c] == (1 << b)
                    ok &= all((nb[y] & B) == (1 << b) for y in Bv if y != b)
                    ok &= (nb[c] & A) == (A ^ (1 << c))
                    ok &= all((nb[a] & A) == (1 << c) for a in Av if a != c)
            res["L5struct33"] = ok
            fl["deg1_33"] = fl.get("deg1_33", 0) + (1 if deg1 else 0)
        if all(beta[a] == B for a in Av):
            res["L7"] = all((nb[a] & A) == 0 for a in Av) and all((nb[b] & B) == 0 for b in Bv)
    return res

def is_K33_relabel(nb):
    # 6 vertices, 3-regular, bipartite with parts of size 3
    n = 6
    if any(pc(x) != 3 for x in nb):
        return False
    for P in itertools.combinations(range(6), 3):
        m = sum(1 << v for v in P)
        if all((nb[v] & m) == 0 for v in P) and all((nb[v] & m) == m for v in range(6) if v not in P):
            return True
    return False

def cmd_exh(s, t, fix=0, clo=0, chi=1):
    t0 = time.time()
    n = s + t
    E = edges_of(n)
    m_all = len(E)
    m = m_all - fix
    ALL = (1 << (1 << m)) - 1
    A = (1 << s) - 1
    B = ((1 << n) - 1) ^ A
    Av = list(range(s)); Bv = list(range(s, n))
    Kfam = None
    Knb = [B if v < s else A for v in range(n)]
    full = (1 << n) - 1
    Kpd = [closure(n, Knb, S) == full for S in range(full + 1)]
    tot = {}
    fails = {}
    examples = {}
    fl = {}
    h2_nonK = []
    for chunk in range(clo, chi):
        sl = [slice_int(e, m) for e in range(m)]
        EM = [[0] * n for _ in range(n)]
        for e, (i, j) in enumerate(E):
            if e < m:
                x = sl[e]
            else:
                x = ALL if (chunk >> (e - m)) & 1 else 0
            EM[i][j] = EM[j][i] = x
        del sl
        def AND_pd(sets, want):
            r = ALL
            for S in sets:
                p = bs_pd(n, EM, S, ALL)
                r &= p if want else (ALL ^ p)
                if not r:
                    break
            return r
        K1 = AND_pd([(1 << a) | (1 << b) for a in Av for b in Bv], True)
        K2A = AND_pd([A ^ (1 << x) for x in Av], True) if K1 else 0
        K2B = AND_pd([B ^ (1 << y) for y in Bv], True) if K1 else 0
        K3A = AND_pd([A ^ (1 << x) ^ (1 << y) for x, y in itertools.combinations(Av, 2)], False) if K1 else 0
        K3B = AND_pd([B ^ (1 << x) ^ (1 << y) for x, y in itertools.combinations(Bv, 2)], False) if K1 else 0
        # L1b bit-sliced: no isolated vertex among K1 graphs
        iso = 0
        for v in range(n):
            r = ALL
            for w in range(n):
                if w != v:
                    r &= ALL ^ EM[v][w]
            iso |= r
        HA = K1 & K2A & K3A
        HB = K1 & K2B & K3B
        H12 = K1 & K2A & K2B
        H2 = HA & HB
        for k, v in (("K1", K1), ("HA", HA), ("HB", HB), ("H12", H12), ("H2", H2), ("K1_and_isolated", K1 & iso)):
            tot[k] = tot.get(k, 0) + pc(v)
        surv = set_bits(HA | HB | (0 if SKIP_L1A else H12))
        base = chunk << m
        for gi in surv:
            g = base | gi
            nb = nb_of(n, g, E)
            flags = {"HA": (HA >> gi) & 1, "HB": (HB >> gi) & 1, "H12": (H12 >> gi) & 1, "H2": (H2 >> gi) & 1}
            res = lemma_checks(n, s, t, nb, flags, fl)
            for k, ok in res.items():
                tot["tested_" + k] = tot.get("tested_" + k, 0) + 1
                if not ok:
                    fails[k] = fails.get(k, 0) + 1
                    examples.setdefault(k, []).append(g) if len(examples.get(k, [])) < 5 else None
            if flags["H2"]:
                fam = all((closure(n, nb, S) == full) == Kpd[S] for S in range(1, full + 1))
                isK = nb == Knb
                if fam:
                    tot["FULL"] = tot.get("FULL", 0) + 1
                    if isK:
                        tot["FULL_isK"] = tot.get("FULL_isK", 0) + 1
                    elif (s, t) == (3, 3) and is_K33_relabel(nb):
                        tot["FULL_K33relabel"] = tot.get("FULL_K33relabel", 0) + 1
                    else:
                        fails["CORE_full_family_not_K"] = fails.get("CORE_full_family_not_K", 0) + 1
                        examples.setdefault("CORE", []).append(g)
                if not isK:
                    tot["H2_notK"] = tot.get("H2_notK", 0) + 1
                    if len(h2_nonK) < 20:
                        h2_nonK.append({"g": g, "nb": nb, "fullfamily": fam})
        print(f"chunk {chunk} done t={time.time()-t0:.1f}s K1={pc(K1)} HA={pc(HA)} HB={pc(HB)} H2={pc(H2)}", flush=True)
    out = {"cmd": "exh", "s": s, "t": t, "fix": fix, "chunks": [clo, chi], "graphs_covered": (chi - clo) << m,
           "totals": tot, "failures": fails, "fail_examples": examples, "flags": fl,
           "H2_but_not_K_examples": h2_nonK, "seconds": round(time.time() - t0, 1)}
    print(json.dumps(out, indent=1))

def cmd_lemma0(n, lo, hi):
    t0 = time.time()
    E = edges_of(n)
    full = (1 << n) - 1
    pairs = 0; bad = []
    nforts = 0
    for g in range(lo, hi):
        nb = nb_of(n, g, E)
        FS = forts(n, nb)
        nforts += len(FS)
        for S in range(0, full + 1):
            pd = S != 0 and closure(n, nb, S) == full
            NS = Nc(n, nb, S)
            fd = all(F & NS for F in FS)
            pairs += 1
            if pd != fd and len(bad) < 10:
                bad.append((g, S))
    out = {"cmd": "lemma0", "n": n, "range": [lo, hi], "graph_S_pairs": pairs, "forts_total": nforts,
           "mismatches": bad, "seconds": round(time.time() - t0, 1)}
    print(json.dumps(out))

if __name__ == "__main__":
    c = sys.argv[1]
    a = [int(x) for x in sys.argv[2:]]
    if c == "exh":
        cmd_exh(*a)
    elif c == "lemma0":
        cmd_lemma0(*a)
