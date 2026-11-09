#!/usr/bin/env python3
"""Independent F4-lift / interpolation / complement construction at order 2^n.
Usage: lift_check.py n OUT.json [--sample K] [--seed S]
Builds the seeds at order 2^(n-2) by iterating my own lift from the order-16
(n even) or order-32 (n odd) seed certificates, lifts once more, then realises
EVERY corrected degree at 2^n (or a random sample of K interior degrees plus all
endpoints when --sample is given) and checks each graph exactly."""
import json, os, sys, random, time, hashlib
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import xm

BASE = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", ".."))
F = os.path.join(BASE, "xor-magic-focused-r1"); X = os.path.join(BASE, "expanded-corpus-r90")
SEEDS = {(16, "closed"): ("outputs/base-16-4-1.json", "outputs/base-16-4-1-factors-"),
         (16, "open"): (os.path.join(X, "outputs/xor-16-5.json"), "outputs/xor-16-5-factors-"),
         (32, "closed"): ("outputs/seed-32-4-1.json", "outputs/seed-32-4-1-factors-"),
         (32, "open"): ("outputs/seed-32-5-0.json", "outputs/seed-32-5-0-factors-")}

def load_seed(m, typ):
    g, f = SEEDS[(m, typ)]
    g = g if os.path.isabs(g) else os.path.join(F, g); f = os.path.join(F, f)
    edges = [tuple(e) for e in json.load(open(g))["edges"]]
    M = json.load(open(f + "0.json"))["factors"]; C = json.load(open(f + "1.json"))["factors"]
    return edges, M, C

def holonomy_controls(L, rng, log):
    """Empirical test of the dichotomy: lift connected  <=>  c not in im D (for c in ker B)."""
    m, E = L.m, len(L.E)
    basis, rankB = xm.kernel_basis(L.B_rows(), E)
    # BD as an m x m matrix
    BD = [[0] * m for _ in range(m)]
    for e, (t, h, a) in enumerate(L.E):
        # B column e: 1 at t, a^-1 at h ; D row e: 1 at h, a at t
        Bc = {t: 1, h: xm.INV[a]}; Dr = {h: 1, t: a}
        for x, bx in Bc.items():
            for y, dy in Dr.items(): BD[x][y] ^= xm.MUL[bx][dy]
    kerBD, rankBD = xm.kernel_basis(BD, m)
    offdiag_ok = all(BD[t][h] != 0 and BD[h][t] != 0 for (t, h, a) in L.E)
    # injectivity of D: kernel of D (as E x m matrix)
    Drows = []
    for (t, h, a) in L.E:
        r = [0] * m; r[h] ^= 1; r[t] ^= a; Drows.append(r)
    kerD, _ = xm.kernel_basis(Drows, m)
    out = {"rank_B": rankB, "dim_ker_B": len(basis), "expected_dim_ker_B": (L.d // 2 - 1) * m if L.d % 2 == 0 else None,
           "E_minus_m": E - m, "dim_ker_D": len(kerD), "rank_BD": rankBD, "dim_imD_cap_kerB": len(kerBD),
           "BD_edge_entries_nonzero": offdiag_ok, "dim_ker_B_gt_dim_cap": len(basis) > len(kerBD)}
    trials = []
    # c = 0 and c in im D cap ker B must give a disconnected lift
    cands = [("zero", [0] * E)]
    for i in range(min(3, len(kerBD))):
        b = [0] * m
        for vec in kerBD:
            k = rng.randrange(4)
            for j, x in enumerate(vec): b[j] ^= xm.MUL[k][x]
        cands.append((f"imD_cap_kerB_{i}", L.D_apply(b)))
    for i in range(12):
        c = [0] * E
        for vec in basis:
            k = rng.randrange(4)
            for j, x in enumerate(vec): c[j] ^= xm.MUL[k][x]
        cands.append((f"random_kerB_{i}", c))
    for name, c in cands:
        inB = all(v == 0 for v in matmul(L.B_rows(), c))
        inD = L.in_image_D(c)
        g = L.build(c)
        r = xm.check_graph(4 * m, g, L.closed)
        trials.append({"name": name, "in_ker_B": inB, "in_im_D": inD, "components": r["components"],
                       "zero_sums": r["zero_sums"], "dichotomy_holds": (r["components"] == 1) == (not inD)})
    out["trials"] = trials
    out["all_dichotomy"] = all(t["dichotomy_holds"] and t["in_ker_B"] and t["zero_sums"] for t in trials)
    return out

def matmul(rows, c):
    res = []
    for r in rows:
        s = 0
        for a, b in zip(r, c):
            if a and b: s ^= xm.MUL[a][b]
        res.append(s)
    return res

def lift_once(m, edges, M, C, closed, rng, log, controls=False):
    L = xm.Lift(m, edges, M, C, closed)
    rec = {"m": m, "d": L.d, "closed": closed, "F_cycles": [len(c) for c in L.cycles]}
    assert any(len(c) % 3 for c in L.cycles), "seed hypothesis fails"
    c, st = xm.choose_c(L, rng); rec["choose_c"] = st
    g = L.build(c)
    r = xm.check_graph(4 * m, g, closed); rec["lift_check"] = r
    Mf, Cf = L.lifted_factors()
    okM = xm.check_decomposition(4 * m, g, Mf); okC = xm.check_decomposition(4 * m, xm.complement(4 * m, g), Cf)
    cyc = [len(x) for x in xm.two_factor_cycles(4 * m, Mf[0], Mf[1])]
    base_cyc = sorted(len(x) for x in L.cycles)
    rec.update(lift_G_decomposition=okM, lift_complement_decomposition=okC, num_Cf=len(Cf),
               expected_num_Cf=4 * m - 1 - L.d, lifted_F_cycles=sorted(cyc),
               lifted_cycle_pattern_ok=all(cyc.count(Lc) >= base_cyc.count(Lc) for Lc in base_cyc if Lc % 3),
               lifted_has_cycle_not_div_3=any(x % 3 for x in cyc))
    if controls: rec["holonomy_controls"] = holonomy_controls(L, rng, log)
    ok = r["ok"] and okM[0] and okC[0] and rec["lifted_has_cycle_not_div_3"] and len(Cf) == 4 * m - 1 - L.d
    rec["ok"] = ok
    return L, g, Mf, Cf, rec

def main():
    n = int(sys.argv[1]); out = sys.argv[2]
    sample = int(sys.argv[sys.argv.index("--sample") + 1]) if "--sample" in sys.argv else None
    seed = int(sys.argv[sys.argv.index("--seed") + 1]) if "--seed" in sys.argv else 372205 + n
    rng = random.Random(seed); xm.f4_selftest(); t0 = time.process_time()
    N = 2 ** n; m = N // 4
    m0 = 16 if n % 2 == 0 else 32
    res = {"n": n, "N": N, "rng_seed": seed, "lifts": [], "degrees": {}, "complements": {}}
    lifts = {}
    for typ in ("closed", "open"):
        edges, M, C = load_seed(m0, typ); mm = m0
        while True:
            L, g, Mf, Cf, rec = lift_once(mm, edges, M, C, typ == "closed", rng, None, controls=(mm <= 64))
            rec["type"] = typ; res["lifts"].append(rec)
            assert rec["ok"], rec
            if 4 * mm == N: break
            edges, M, C, mm = g, Mf, Cf, 4 * mm
        lifts[typ] = L
    # realise every corrected degree
    targets = []
    for D in range(5, N - 4, 2): targets.append(("open", D))
    for D in range(4, N - 5, 2): targets.append(("closed", D))
    interior = [t for t in targets if not ((t[0] == "open" and t[1] >= N - 7) or (t[0] == "closed" and t[1] >= N - 6))]
    if sample is not None:
        must = [t for t in interior if t[1] in (4, 5, 6, 7, 8, 9, N - 8, N - 9)]
        rest = [t for t in interior if t not in must]
        interior = must + rng.sample(rest, min(sample, len(rest)))
    built = {}
    for typ, D in interior:
        L = lifts[typ]; d = L.d; mm = L.m; s = (D - d) // 2
        assert (D - d) % 2 == 0 and d <= D <= 4 * mm - 4 - d
        jlo, jhi = max(0, -(-(s - d) // 2)), min(mm - 1 - d, s // 2)
        assert jlo <= jhi, (D, s)
        j = rng.randint(jlo, jhi); k = s - 2 * j; assert 0 <= k <= d
        K = rng.sample(range(d), k); J = rng.sample(range(mm - 1 - d), j)
        g = L.interpolate(K, J)
        r = xm.check_graph(N, g, typ == "closed")
        r.update(k=k, j=j, degree_formula=d + 2 * k + 4 * j)
        assert r["degree"] == D == r["degree_formula"], (typ, D, r)
        res["degrees"][f"{typ}-{D}"] = {kk: r[kk] for kk in ("ok", "degree", "components", "zero_sums", "simple", "k", "j")}
        if (typ, D) in (("closed", 4), ("closed", 6), ("open", 5)): built[(typ, D)] = g
    # endpoint complements: open N-5 = comp(closed 4), open N-7 = comp(closed 6), closed N-6 = comp(open 5)
    for (typ, D), (ctyp, cD) in {("closed", 4): ("open", N - 5), ("closed", 6): ("open", N - 7), ("open", 5): ("closed", N - 6)}.items():
        g = built[(typ, D)]; comp = xm.complement(N, g)
        r = xm.check_graph(N, comp, ctyp == "closed"); assert r["degree"] == cD
        res["degrees"][f"{ctyp}-{cD}"] = {kk: r[kk] for kk in ("ok", "degree", "components", "zero_sums", "simple")}
        res["degrees"][f"{ctyp}-{cD}"]["via"] = f"complement of {typ}-{D}"
    expected = {f"open-{D}" for D in range(5, N - 4, 2)} | {f"closed-{D}" for D in range(4, N - 5, 2)}
    res["covered_all_degrees"] = expected <= set(res["degrees"])
    res["num_degrees_checked"] = len(res["degrees"]); res["num_degrees_expected"] = len(expected)
    res["all_checked_ok"] = all(v["ok"] for v in res["degrees"].values()) and all(l["ok"] for l in res["lifts"])
    res["all_holonomy_controls_ok"] = all(l["holonomy_controls"]["all_dichotomy"] for l in res["lifts"] if "holonomy_controls" in l)
    res["cpu_seconds"] = round(time.process_time() - t0, 2)
    json.dump(res, open(out, "w"), indent=1, sort_keys=True)
    print(json.dumps({k: v for k, v in res.items() if k not in ("degrees", "lifts")}))
    for l in res["lifts"]:
        print(l["type"], l["m"], "->", 4 * l["m"], "ok", l["ok"], "F", sorted(l["F_cycles"])[:6], "liftedF", l["lifted_F_cycles"][:6],
              "c", l["choose_c"], "hol", {k: v for k, v in l.get("holonomy_controls", {}).items() if k != "trials"})

if __name__ == "__main__":
    main()
