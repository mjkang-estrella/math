#!/usr/bin/env python3
# Copyright 2026 Myeongjin Kang, no affiliation. MIT License.
"""Independent finite controls for the staircase manuscript review.

Written from the frozen main.tex text only. It imports no package, candidate,
proof-review or contribution-review code. Finite checks support the review;
they are not premises of the all-m theorem.
"""
import itertools
import json
import math
import random
import sys


def positions(m):
    return [(i, j) for i in range(1, m + 1) for j in range(1, m + 2 - i)]


def setup(m):
    B = positions(m)
    idx = {x: k for k, x in enumerate(B)}
    rows = [[idx[(i, j)] for j in range(1, m + 2 - i)] for i in range(1, m + 1)]
    cols = [[idx[(i, j)] for i in range(1, m + 2 - j)] for j in range(1, m + 1)]
    beta = tuple(m + 2 - i - j for i, j in B)
    b0 = tuple(j for i, j in B)
    w = tuple((m + 1 - i, m + 2 - i - j) for i, j in B)
    D = sorted((r, a) for r in range(1, m + 1) for a in range(1, r + 1))
    return B, idx, rows, cols, beta, b0, w, D


def perm_sign(p):
    inv = sum(1 for x in range(len(p)) for y in range(x + 1, len(p)) if p[x] > p[y])
    return -1 if inv % 2 else 1


def alt_vector(blocks, N):
    """Literal definition of alt: sigma in S_r puts letter sigma(k) at d_k."""
    vec = {(): 1}
    word = {}
    pieces = []
    for blk in blocks:
        r = len(blk)
        terms = []
        for s in itertools.permutations(range(1, r + 1)):
            terms.append((s, perm_sign(s)))
        pieces.append((blk, terms))
    out = {}
    for choice in itertools.product(*[t for _, t in pieces]):
        a = [0] * N
        sign = 1
        for (blk, _), (s, sg) in zip(pieces, choice):
            for k, pos in enumerate(blk):
                a[pos] = s[k]
            sign *= sg
        out[tuple(a)] = out.get(tuple(a), 0) + sign
    return out


def coeff(blocks, a):
    """Word coefficient read block by block (0 or +-1)."""
    sign = 1
    for blk in blocks:
        letters = tuple(a[p] for p in blk)
        if sorted(letters) != list(range(1, len(blk) + 1)):
            return 0
        sign *= perm_sign(letters)
    return sign


def act(g, a):
    """g e_a = e_{a o g^{-1}}: the letter at x moves to g(x)."""
    out = [None] * len(a)
    for x, gx in enumerate(g):
        out[gx] = a[x]
    return tuple(out)


def polytabloid_words(m):
    """Construct e_t by acting with the column group on tabloids of t."""
    B, idx, rows, cols, beta, b0, w, D = setup(m)
    N = len(B)
    results = {}
    # t_R: entry (i,j) in cell (j,i); t_C: entry (i,j) in cell (i,j).
    for name, cell in (("R", lambda i, j: (j, i)), ("C", lambda i, j: (i, j))):
        cell_of = {idx[(i, j)]: cell(i, j) for (i, j) in B}
        assert sorted(cell_of.values()) == sorted(positions(m))  # shape rho
        tcols = {}
        for e, (r, c) in cell_of.items():
            tcols.setdefault(c, []).append((r, e))
        tcols = [[e for r, e in sorted(v)] for c, v in sorted(tcols.items())]
        vec = {}
        for hs in itertools.product(*[list(itertools.permutations(col)) for col in tcols]):
            h = list(range(N))
            sign = 1
            for col, image in zip(tcols, hs):
                for y, hy in zip(col, image):
                    h[y] = hy
                sign *= perm_sign([col.index(z) for z in image])
            # Tabloid {ht}: entry h(y) sits in the cell of y.
            word = [None] * N
            for y in range(N):
                word[h[y]] = cell_of[y][0]
            word = tuple(word)
            vec[word] = vec.get(word, 0) + sign
        results[name] = (vec, tcols)
    return results


def q_pi_J(m, triple, data):
    """Literal J^{-1} pi_D q^B on one basis triple; returns g or None."""
    B, idx, rows, cols, beta, b0, w, D = data
    a, b, c = triple
    out = []
    for x in range(len(B)):
        if a[x] != c[x]:
            return None
        out.append((a[x] + b[x] - 1, a[x]))
    if sorted(out) != D:
        return None
    where = {letter: x for x, letter in enumerate(out)}
    # g e_w = e_u  iff  u(g(x)) = w(x).
    return tuple(where[w[x]] for x in range(len(B)))


def control_polytabloids(report):
    rec = []
    for m in range(1, 5):
        data = setup(m)
        B, idx, rows, cols = data[:4]
        vR = alt_vector(rows, len(B))
        vC = alt_vector(cols, len(B))
        pt = polytabloid_words(m)
        assert pt["R"][0] == vR and pt["C"][0] == vC
        assert pt["R"][1] == rows and pt["C"][1] == cols
        transpose = tuple(idx[(j, i)] for (i, j) in B)
        assert {act(transpose, a): s for a, s in vR.items()} == vC
        for a in vR:
            assert all(sum(1 for x in a if x == k) == m + 1 - k for k in range(1, m + 1))
        rec.append({"m": m, "terms": len(vR), "polytabloid_equals_alt": True,
                    "transpose_scalar": 1, "content_rho": True})
    report["C1_polytabloid_identification"] = rec


def control_projected_vector(report):
    rec = []
    for m in range(1, 6):
        data = setup(m)
        B, idx, rows, cols, beta, b0, w, D = data
        vR = alt_vector(rows, len(B))
        vC = alt_vector(cols, len(B))
        image = {}
        literal = m <= 3
        if literal:
            for (a, ca), (b, cb), (c, cc) in itertools.product(vR.items(), vR.items(), vC.items()):
                g = q_pi_J(m, (a, b, c), data)
                if g is not None:
                    image[g] = image.get(g, 0) + ca * cb * cc
        else:
            # q kills a != c, so restrict to a in supp(vR) cap supp(vC).
            common = [a for a in vR if a in vC]
            for a in common:
                for b, cb in vR.items():
                    g = q_pi_J(m, (a, b, a), data)
                    if g is not None:
                        image[g] = image.get(g, 0) + vR[a] * cb * vC[a]
        ident = tuple(range(len(B)))
        assert image == {ident: 1}, (m, image)
        rec.append({"m": m, "N": len(B), "row_words": len(vR),
                    "expansion": "all |vR|^2|vC| triples" if literal else "a=c filtered (q kills a!=c)",
                    "result": "pi_D q^B(z_m) = +1 e_w exactly"})
    report["C2_full_projected_vector"] = rec


def control_P_after_I(report):
    m = 3
    data = setup(m)
    B, idx, rows, cols, beta, b0, w, D = data
    N = len(B)
    vR = alt_vector(rows, N)
    vC = alt_vector(cols, N)
    G = list(itertools.permutations(range(N)))
    theta_orbit = {}
    for g in G:
        key = (act(g, beta), act(g, b0), act(g, beta))
        assert key not in theta_orbit
        theta_orbit[key] = g
    z = [((a, b, c), ca * cb * cc) for (a, ca) in vR.items() for (b, cb) in vR.items() for (c, cc) in vC.items()]
    for g in G:
        p1, p2 = {}, {}
        for (a, b, c), s in z:
            t = (act(g, a), act(g, b), act(g, c))
            h = q_pi_J(m, t, data)
            if h is not None:
                p1[h] = p1.get(h, 0) + s
            h2 = theta_orbit.get(t)
            if h2 is not None:
                p2[h2] = p2.get(h2, 0) + s
        assert p1 == {g: 1} and p2 == {g: 1}
    report["C3_full_matrix_P_I_m3"] = {"m": 3, "group_elements": len(G), "triples_per_translate": len(z),
                                       "P_I_equals_identity_both_formulas": True}


def theta_solve(m, t, data):
    """Evaluate sum_g theta*(g^{-1}t) delta_g on a basis triple by solving
    t = g theta directly: (beta, b0) determines the cell injectively."""
    B, idx, rows, cols, beta, b0, w, D = data
    a, b, c = t
    cell = {(beta[x], b0[x]): x for x in range(len(B))}
    ginv = []
    for y in range(len(B)):
        x = cell.get((a[y], b[y]))
        if x is None:
            return None
        ginv.append(x)
    if len(set(ginv)) != len(B):
        return None
    g = [None] * len(B)
    for y, x in enumerate(ginv):
        g[x] = y
    g = tuple(g)
    if (act(g, beta), act(g, b0), act(g, beta)) != t:
        return None
    return g


def control_formula_equivalence(report):
    rng = random.Random(20261015)
    rec = []
    for m in (2, 3, 4):
        data = setup(m)
        B, idx, rows, cols, beta, b0, w, D = data
        N = len(B)
        orbit = None
        if m <= 3:
            orbit = {}
            for g in itertools.permutations(range(N)):
                orbit[(act(g, beta), act(g, b0), act(g, beta))] = g
        count = nonzero = 0

        def check(t):
            nonlocal count, nonzero
            g1 = q_pi_J(m, t, data)
            g2 = orbit.get(t) if orbit is not None else theta_solve(m, t, data)
            assert g1 == g2, (m, t)
            if orbit is not None:
                assert theta_solve(m, t, data) == g2
            count += 1
            nonzero += g1 is not None

        mode = []
        if m == 2:
            words = list(itertools.product(range(1, m + 1), repeat=N))
            for t in itertools.product(words, repeat=3):
                check(t)
            mode.append("all 512 basis triples, orbit-table and solver evaluations")
        elif m == 3:
            words = list(itertools.product(range(1, m + 1), repeat=N))
            for a in words:
                for b in words:
                    check((a, b, a))
            mode.append("all 531441 triples with a=c")
            for _ in range(100000):
                check(tuple(tuple(rng.randint(1, m) for _ in range(N)) for _ in range(3)))
            mode.append("100000 uniform random triples")
        else:
            for _ in range(20000):
                g = list(range(N))
                rng.shuffle(g)
                g = tuple(g)
                t = (act(g, beta), act(g, b0), act(g, beta))
                assert q_pi_J(m, t, data) == g
                check(t)
            for _ in range(100000):
                a = tuple(rng.randint(1, m) for _ in range(N))
                b = tuple(rng.randint(1, m) for _ in range(N))
                check((a, b, a))
            for _ in range(20000):
                g = list(range(N))
                rng.shuffle(g)
                u = act(tuple(g), w)
                a = tuple(x[1] for x in u)
                b = tuple(x[0] + 1 - x[1] for x in u)
                check((a, b, a))
            mode.append("20000 random theta translates, 100000 random a=c triples, 20000 W_D preimages")
        rec.append({"m": m, "comparisons": count, "nonzero_outputs": nonzero, "mode": mode})
    report["C4_coordinate_formula_equivalence"] = rec


def control_palette_lemma(report):
    rec = []
    for m in range(1, 9):
        B, idx, rows, cols, beta, b0, w, D = setup(m)
        N = len(B)
        order = [idx[(i, j)] for i in range(1, m + 1) for j in range(1, m + 2 - i)]
        pos = B
        sols = []
        a = [0] * N
        usedr = [set() for _ in range(m + 1)]
        usedc = [set() for _ in range(m + 1)]

        def rec_fill(k):
            if k == N:
                sols.append(tuple(a))
                return
            i, j = pos[order[k]]
            for v in range(1, min(m + 1 - i, m + 1 - j) + 1):
                if v in usedr[i] or v in usedc[j]:
                    continue
                a[order[k]] = v
                usedr[i].add(v)
                usedc[j].add(v)
                rec_fill(k + 1)
                usedr[i].discard(v)
                usedc[j].discard(v)

        rec_fill(0)
        assert sols == [beta], (m, len(sols))
        rec.append({"m": m, "words_with_both_palettes": len(sols), "equals_beta": True})
    report["C5_palette_lemma_exhaustive"] = rec


def control_deficit(report):
    """Exhaustive deficit step: row-palette pairs (a,b) whose first output
    coordinates d=a+b-1 have content {r^r} must have d=r on the row of length r."""
    rec = []
    for m in range(1, 7):
        per_row = {}
        for r in range(1, m + 1):
            ms = set()
            for p in itertools.permutations(range(1, r + 1)):
                for q in itertools.permutations(range(1, r + 1)):
                    ms.add(tuple(sorted(x + y - 1 for x, y in zip(p, q))))
            per_row[r] = ms
        target = tuple(sorted(r for r in range(1, m + 1) for _ in range(r)))
        from collections import Counter
        hits = []

        def go(r, acc, chosen):
            if r > m:
                if tuple(sorted(acc.elements())) == target:
                    hits.append(tuple(chosen))
                return
            tgt = Counter(target)
            for ms in per_row[r]:
                new = acc + Counter(ms)
                if any(new[k] > tgt[k] for k in new):
                    continue
                go(r + 1, new, chosen + [ms])

        go(1, Counter(), [])
        expected = tuple(tuple([r] * r) for r in range(1, m + 1))
        assert hits == [expected], (m, len(hits))
        rec.append({"m": m, "row_multisets": {r: len(per_row[r]) for r in per_row},
                    "global_content_solutions": len(hits), "all_rows_constant": True})
    report["C6_square_deficit_exhaustive"] = rec


def control_hooks(report):
    def vp(n, p):
        k = 0
        while n % p == 0:
            n //= p
            k += 1
        return k
    rec = []
    for m in range(1, 16):
        N = m * (m + 1) // 2
        hooks = [2 * (m + 1 - i - j) + 1 for i in range(1, m + 1) for j in range(1, m + 2 - i)]
        # Direct arm+leg+1 hook computation.
        lam = list(range(m, 0, -1))
        conj = [sum(1 for part in lam if part >= c) for c in range(1, m + 1)]
        direct = [lam[i - 1] - j + conj[j - 1] - i + 1 for i in range(1, m + 1) for j in range(1, lam[i - 1] + 1)]
        assert sorted(hooks) == sorted(direct)
        dim = math.factorial(N) // math.prod(hooks)
        assert dim * math.prod(hooks) == math.factorial(N)
        primes = [p for p in range(2, N + 1) if all(p % d for d in range(2, int(p ** 0.5) + 1))]
        for p in primes:
            nonproj = vp(dim, p) < vp(math.factorial(N), p)
            if p == 2:
                assert not nonproj
            elif p <= 2 * m - 1:
                assert nonproj
            else:
                assert not nonproj
        rec.append({"m": m, "N": N, "dim": str(dim) if dim < 10 ** 30 else "len%d" % len(str(dim)),
                    "odd_primes_failing_divisibility": [p for p in primes if p > 2 and p <= 2 * m - 1]})
    report["C7_hook_and_projective_divisibility"] = rec


def control_complex_antecedent(report):
    """At m=1..3: G(v_R x v_R) has |G/H| distinct translates of full rank, and
    the pinned pair-letter map has scalar (-1)^H prod r!."""
    rec = []
    P = 1000000007
    for m in (1, 2, 3):
        data = setup(m)
        B, idx, rows, cols, beta, b0, w, D = data
        N = len(B)
        vR = alt_vector(rows, N)
        zz = {(a, b): ca * cb for a, ca in vR.items() for b, cb in vR.items()}
        tm = tuple(m + 1 - i for i, j in B)
        scalar = 0
        for (a, b), s in zz.items():
            out = tuple(x + y - 1 for x, y in zip(a, b))
            if sorted(out) == sorted(r for r in range(1, m + 1) for _ in range(r)):
                assert out == tm
                scalar += s
        H = sum(math.comb(r, 2) for r in range(1, m + 1))
        assert scalar == (-1) ** H * math.prod(math.factorial(r) for r in range(1, m + 1))
        translates = set()
        for g in itertools.permutations(range(N)):
            translates.add(frozenset(((act(g, a), act(g, b)), s) for (a, b), s in zz.items()))
        keys = sorted({k for v in translates for k, _ in v})
        col = {k: n for n, k in enumerate(keys)}
        rowsM = [{col[k]: s % P for k, s in v} for v in translates]
        rank = 0
        pivots = {}
        for r_ in rowsM:
            r_ = dict(r_)
            while r_:
                piv = min(r_)
                if piv in pivots:
                    prow = pivots[piv]
                    f = r_[piv]
                    for k2, v2 in prow.items():
                        r_[k2] = (r_.get(k2, 0) - f * v2) % P
                        if r_[k2] == 0:
                            del r_[k2]
                else:
                    inv = pow(r_[piv], P - 2, P)
                    pivots[piv] = {k2: v2 * inv % P for k2, v2 in r_.items()}
                    rank += 1
                    break
        index = math.factorial(N) // math.prod(math.factorial(r) for r in range(1, m + 1))
        assert len(translates) == index and rank == index
        rec.append({"m": m, "pair_letter_scalar": scalar, "distinct_translates": len(translates),
                    "rank_mod_1e9+7": rank, "dim_M_rho": index})
    report["C8_complex_antecedent_I21_OAI"] = rec


def control_mutations(report):
    """Mutations that the exact statement must exclude (m=2 and m=3)."""
    out = {}

    def image(m, data, x1, x2, x3, rule="exact"):
        res = {}
        for (a, ca), (b, cb), (c, cc) in itertools.product(x1.items(), x2.items(), x3.items()):
            if rule == "no_filter":
                # q'(a,b,c)=f_{a+b-1,a} for every c: evaluate with the third letter ignored.
                g = q_pi_J(m, (a, b, a), data)
            else:
                g = q_pi_J(m, (a, b, c), data)
            if g is not None:
                res[g] = res.get(g, 0) + ca * cb * cc
        return {g: v for g, v in res.items() if v}

    for m in (2, 3):
        data = setup(m)
        B, idx, rows, cols, beta, b0, w, D = data
        N = len(B)
        ident = tuple(range(N))
        vR = alt_vector(rows, N)
        vC = alt_vector(cols, N)
        assert image(m, data, vR, vR, vC) == {ident: 1}
        third_rows = image(m, data, vR, vR, vR)
        no_filter = image(m, data, vR, vR, vC, rule="no_filter")
        rows1 = [list(reversed(rows[0]))] + rows[1:]
        flipped = image(m, data, alt_vector(rows1, N), vR, vC)
        swapped = image(m, data, vC, vR, vR)
        out["m%d" % m] = {
            "third_factor_rows_vR_vR_vR": {"nonzero_words": len(third_rows),
                                           "coefficients": sorted(set(third_rows.values()))},
            "drop_a_eq_c_filter": {"nonzero_words": len(no_filter)},
            "reverse_top_row_order_first_layer": {"nonzero_words": len(flipped),
                                                  "identity_coefficient": flipped.get(ident, 0)},
            "column_first_layer_vC_vR_vR": {"nonzero_words": len(swapped),
                                            "coefficients": sorted(set(swapped.values())),
                                            "equals_unit_at_identity": swapped == {ident: 1}},
        }
        # Layers 1 and 3 enter only through a=c, so swapping them is a symmetry, not a mutation.
        assert swapped == {ident: 1}
        assert third_rows != {ident: 1} and no_filter != {ident: 1}
        assert flipped == {ident: (-1) ** (len(rows[0]) * (len(rows[0]) - 1) // 2)}
    report["C9_mutations"] = out


def main():
    if not __debug__:
        raise SystemExit("run without -O")
    report = {"python": sys.version.split()[0], "source": "frozen main.tex text only; no package code imported"}
    import time
    timing = {}
    for fn in (control_polytabloids, control_projected_vector, control_P_after_I,
               control_formula_equivalence, control_palette_lemma, control_deficit,
               control_hooks, control_complex_antecedent, control_mutations):
        start = time.perf_counter()
        fn(report)
        timing[fn.__name__] = "completed"
        print(fn.__name__, round(time.perf_counter() - start, 2), "s", file=sys.stderr)
    report["controls_completed"] = sorted(timing)
    report["status"] = "PASS"
    report["scope"] = "finite support only; not a proof of the all-m theorem"
    print(json.dumps(report, indent=1, sort_keys=True))


if __name__ == "__main__":
    main()
