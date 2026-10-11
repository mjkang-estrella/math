"""Fresh I173 research; all external data comes from authenticated memory."""
import json
from collections import Counter
from fractions import Fraction
from itertools import combinations
import toolkit as t

OLD = "frontier/experiments/i172_prescribed_square_switch/"
DATA = {}


def data(path):
    return json.loads(DATA[path])


def old(name):
    return data(OLD + name + "-attempt-01.json")


def as_graph(record):
    F = record["faces"]
    return dict(n=record["n"], faces=F,
                edges=sorted({t.edge(a, b) for f in F for a, b in zip(f, f[1:] + f[:1])}))


def compare_row(new, previous):
    for k in ("n", "arcs", "counts", "dg", "rankL", "rankU", "rankUV",
              "ell", "t", "eta", "delta_V", "delta_R", "epsilon"):
        if k in previous:
            assert new[k] == previous[k], (k, new[k], previous[k])


def compare_families(rec, previous):
    assert set(map(tuple, previous["cycles"])) == set(rec["cycles"])
    for k, vs in rec["families"].items():
        assert set(vs) == set(map(tuple, previous["families"][k])), k
    compare_row(rec["row"], previous["row"])


def mandatory():
    previous = old("mandatory")
    auditrows = data("frontier/experiments/i169_bridge_independence/audit-attempt-02.json")["rows"]
    graphbank = data("frontier/experiments/i166_affine_span_braces/bracegen-graphs.json")
    graphs = [as_graph(g) for group in graphbank.values() for g in group.values()]
    out = []
    for expected in previous["census"]:
        i = expected["index"]
        a = next(r for r in auditrows if r["index"] == i)
        E = tuple(map(tuple, a["parent_edges"]))
        g = next(g for g in graphs if t.edges_of(g) == E)
        rec = t.analyze(g, a["step"])
        compare_row(rec["row"], expected["row"])
        rec["certification"] = t.certify_graph(g)
        rec["index"] = i
        for k, vs in a["classes"].items():
            assert set(rec["families"][k]) == {t.vector(E, map(tuple, es)) for es in vs}
        fs = rec["families"]
        L = t.diff(sorted(fs["N10"] + fs["N01"] + fs["N11"]))
        U = sum((t.diff(fs[k]) for k in ("Pux", "Pvy", "D11")), [])
        offset = t.plus((1, rec["bridge"]), (-1, a["b"]))
        assert t.rank(L + U + [offset]) == t.rank(L + U)
        rec["ancestor_bridge_difference"] = offset
        out.append(rec)
    assert [r["index"] for r in out] == [0, 520, 522, 524, 527, 528, 530, 533, 534, 536, 539, 431]
    c = previous["C171"]
    rec = t.analyze(c["graph"], c["row"]["step"])
    compare_row(rec["row"], c["row"])
    rec["certification"] = t.certify_graph(c["graph"])
    rec["brace"] = t.brace_certificate(c["graph"])
    assert rec["brace"]["brace"] and len(rec["brace"]["extended_pairs"]) == 1032
    w = tuple(map(Fraction, c["w"]))
    dot = lambda v: sum(a * b for a, b in zip(w, v))
    fs = rec["families"]
    L = t.diff(sorted(fs["N10"] + fs["N01"] + fs["N11"]))
    assert all(dot(v) == 0 for v in L + t.diff(fs["N00"]))
    assert dot(t.plus((1, c["N"]), (-1, c["C0"]))) == 1
    assert dot(t.plus((1, c["F"]), (-1, c["C0"]))) == Fraction(1, 14)
    assert dot(t.plus((1, c["T"]), (-1, c["C0"]))) == Fraction(-1, 2)
    qa, qb, _ = t.boundary_q(c["graph"], c["row"]["step"])
    uvxy = rec["uvxy"]
    ef = t.vector(t.edges_of(c["graph"]), [t.edge(*uvxy[:2]), t.edge(*uvxy[2:])])
    assert t.plus((1, c["N"]), (1, ef), (-1, qa), (-1, qb)) == tuple(c["F"])
    assert c["T"] != c["F"]
    V = set(t.adjacency(t.edges_of(c["graph"])))
    for name in ("F", "T"):
        E2 = [e for e, val in zip(t.edges_of(c["graph"]), c[name]) if val]
        assert all(len(n) == 2 for n in t.adjacency(E2).values())
        assert len(t.components(V, E2)) == 2
    rec["weight_checks"] = dict(F="1/14", T="-1/2", w=c["w"], F_vector=c["F"], T_vector=c["T"], C0=c["C0"])
    high = []
    for a in old("cut-octagons")["records"]:
        if a["L"] in (6, 10):
            r = t.analyze(a["graph"], a["row"]["step"])
            compare_families(r, a)
            assert r["row"]["ell"] == a["L"] - 3
            r["m"] = a["L"]
            r["certification"] = t.certify_graph(a["graph"])
            high.append(r)
    return dict(status="PASS", first_order=previous["order"] + ["C171 [1,1,3]", "G6", "G10"],
                census=out, C171=rec, high_loss=high)


def ancestor_audit():
    # Called only after the mandatory payload has completed.
    octagons, remote, caps, residual, projection = [], [], [], [], []
    for a in old("cut-octagons")["records"]:
        g, m = a["graph"], a["L"]
        r = t.analyze(g, a["row"]["step"])
        compare_families(r, a)
        for name in ("graph", "base_graph", "intermediate_graph"):
            t.certify_graph(a[name])
        assert r["row"]["dg"] == m + 7 and r["row"]["rankL"] == 10
        assert r["row"]["rankL0"] == 8
        assert all(not d["good"] for d in r["residuals"].values())
        r["m"] = m
        r["cuts"] = t.cuts3(g)
        r["brace"] = t.brace_certificate(g)
        assert not r["brace"]["brace"]
        fs = r["families"]
        L = t.diff(sorted(fs["N10"] + fs["N01"] + fs["N11"]))
        U = sum((t.diff(fs[k]) for k in ("Pux", "Pvy", "D11")), [])
        sep = list(map(Fraction, a["bridge_separator"]))
        assert all(sum(x * y for x, y in zip(sep, v)) == 0 for v in L + U)
        assert sum(x * y for x, y in zip(sep, r["bridge"])) != 0
        # Stored offsets need not use our representatives, but must differ inside
        # the exact within-class spaces, not merely have the same rank.
        L0 = sum((t.diff(fs[k]) for k in ("N10", "N01", "N11")), [])
        for name, space in (("bridge", L + U), ("beta", L0 + U), ("c", L0 + t.diff(fs["N00"]))):
            d = t.plus((1, a[name]), (-1, r[name]))
            assert t.rank(space + [d]) == t.rank(space)
        octagons.append(r)
    for a in old("remote-splices")["rows"]:
        r = t.analyze(a["graph"], a["row"]["step"])
        compare_families(r, a)
        t.certify_graph(a["graph"])
        total = [Fraction(0)] * len(t.edges_of(a["graph"]))
        q, total_coeff = Fraction(0), Fraction(0)
        for term in a["coefficients"]:
            C, coeff = tuple(term["C"]), Fraction(term["coefficient"])
            assert C in r["cycles"]
            total = [x + coeff * y for x, y in zip(total, C)]
            total_coeff += coeff
            if C in r["families"]["N00"]:
                q += coeff
        assert total_coeff == 1 and total == a["F"]
        assert q == Fraction(a["N00_coefficient_total"]) == Fraction(1, a["L"] - 2)
        qa, qb, _ = t.boundary_q(a["graph"], a["row"]["step"])
        uvxy = r["uvxy"]
        ef = t.vector(t.edges_of(a["graph"]), [t.edge(*uvxy[:2]), t.edge(*uvxy[2:])])
        assert t.plus((1, a["N"]), (1, ef), (-1, qa), (-1, qb)) == tuple(a["F"])
        r["signed_certificate"] = a["coefficients"]
        r["prescribed_factor"] = a["F"]
        r["lost_total"] = str(q)
        remote.append(r)
    for a in old("cap-transport")["records"]:
        r = t.analyze(a["graph"], a["row"]["step"])
        compare_families(r, a)
        for gn, rn in (("base_graph", "base_row"), ("intermediate_graph", "intermediate_row"), ("graph", "row")):
            t.certify_graph(a[gn])
            compare_row(t.analyze(a[gn], a[rn]["step"])["row"], a[rn])
        r["m"] = a["L"]
        r["partners"] = [a["top_partner"], a["bottom_partner"]]
        caps.append(r)
    assert Counter((r["row"]["ell"], r["row"]["t"], r["row"]["eta"]) for r in caps) == {(0, 0, 0): 20, (1, 1, 0): 9}
    for a in old("residual-certificates")["records"]:
        r = next(r for r in octagons if r["m"] == a["L"])
        fs = r["families"]
        for N, P in zip(a["old_cycles"], a["residual_paths"]):
            assert tuple(N) in fs["N00"] and tuple(P) in fs["Pux"]
            assert t.plus((1, P), (-1, N)) == tuple(a["translation_offset"])
        L = t.diff(sorted(fs["N10"] + fs["N01"] + fs["N11"]))
        dirs = t.diff(a["residual_paths"])
        assert dirs == t.diff(a["old_cycles"])
        assert t.rank(L + dirs) - t.rank(L) == a["L"] - 4 == a["rank_mod_L"]
        residual.append(dict(m=a["L"], offset=a["translation_offset"], directions=dirs,
                             recovered=a["rank_mod_L"]))
    for a in old("cut-projection")["records"]:
        m = a["L"]
        r = next(r for r in octagons if r["m"] == m)
        E, baseE = t.edges_of(r["graph"]), t.edges_of(a["base_graph"])
        offA, offB = 2 * m, 2 * m + 8
        remap = {
            t.edge(1, offA + 1): t.edge(0, 1),
            t.edge(m - 1, offA + 4): t.edge(0, m - 1),
            t.edge(m, offA + 3): t.edge(0, m),
            t.edge(1, offB + 1): t.edge(1, m + 1),
            t.edge(m, offB + 4): t.edge(m, m + 1),
            t.edge(m + 2, offB + 3): t.edge(m + 1, m + 2),
        }
        def project(vec):
            ans = [0] * len(baseE)
            for e, val in zip(E, vec):
                if e in remap:
                    ans[baseE.index(remap[e])] += val
                elif e in baseE:
                    ans[baseE.index(e)] += val
            return tuple(ans)
        base = t.analyze(a["base_graph"], a["source_row"]["step"])
        projected = {}
        for name, vs in r["families"].items():
            counts = Counter(project(v) for v in vs)
            assert set(counts) == set(base["families"][name])
            assert set(counts.values()) == {4}
            assert set(counts) == set(map(tuple, a["projected_families"][name]["vectors"]))
            projected[name] = [dict(vector=v, fibre=n) for v, n in sorted(counts.items())]
        # Arbitrary inherited representative projection is verified coordinatewise.
        source = next(x for x in old("cut-octagons")["records"] if x["L"] == m)
        assert project(source["bridge"]) == tuple(a["projected_bridge"]) == tuple(a["source_bridge"])
        for k in ("bridge", "beta", "c"):
            space = t.diff(base["cycles"])
            assert t.rank(space + [t.plus((1, project(r[k])), (-1, base[k]))]) == t.rank(space)
        projection.append(dict(m=m, families=projected, projected_bridge=project(r["bridge"]),
                               projected_beta=project(r["beta"]), projected_c=project(r["c"]),
                               ambient_degree_dimension=len(E) - r["graph"]["n"] + 1))
    return dict(status="PASS ORIGINAL", octagons=octagons, remote=remote, caps=caps,
                residual=residual, projection=projection,
                scopes=dict(octagons=4, remote=12, caps=29, seven_class_projections=28))


def cross_steps(g, side, perimeter):
    """Lexicographic (face index, edge index, edge index), no isomorphism pruning."""
    side, perimeter = set(side), set(perimeter)
    ans = []
    for k, F in enumerate(g["faces"]):
        for i, j in combinations(range(len(F)), 2):
            if (j - i) % 2 or j - i < 2 or j - i > len(F) - 2:
                continue
            e = t.edge(F[i], F[(i + 1) % len(F)])
            f = t.edge(F[j], F[(j + 1) % len(F)])
            if e in perimeter or f in perimeter:
                continue
            if (set(e) <= side and not set(f) & side) or (set(f) <= side and not set(e) & side):
                ans.append([k, i, j])
    return ans


def surgery_plan():
    out = []
    for a in old("cut-octagons")["records"]:
        m = a["L"]
        if m not in (6, 8, 10):
            continue
        g = a["graph"]
        F = g["faces"][a["row"]["step"][0]]
        perimeter = [t.edge(x, y) for x, y in zip(F, F[1:] + F[:1])]
        A, B = list(range(2 * m + 1, 2 * m + 8)), list(range(2 * m + 9, 2 * m + 16))
        first = cross_steps(g, A, perimeter)
        children = []
        for step in first:
            child = t.expand(g, step)
            children.append(dict(first=step, second=cross_steps(child, B, perimeter)))
        out.append(dict(m=m, cutA=A, cutB=B, protected=F, first_count=len(first),
                        second_count=sum(len(c["second"]) for c in children), steps=children))
    return dict(order="m=6,8,10; all cross-A then all cross-B, lexicographic step triples",
                duplicates="No pruning of histories or labelled graphs", rows=out)


def transport(parent_graph, child, previous_pairs):
    """Keep all local extensions in the certificate; choose least vector to continue."""
    oldE, newE = t.edges_of(parent_graph), t.edges_of(child["graph"])
    common = sorted(set(oldE) & set(newE))
    old_indices, new_indices = [oldE.index(e) for e in common], [newE.index(e) for e in common]
    output, continuing = [], []
    for N, P in previous_pairs:
        entry = {}
        selected = []
        for name, vec in (("N00", N), ("Pux", P)):
            signature = tuple(vec[i] for i in old_indices)
            lifts = [v for v in child["families"][name] if tuple(v[i] for i in new_indices) == signature]
            entry[name] = dict(parent=vec, extensions=lifts)
            selected.append(lifts[0] if lifts else None)
        output.append(entry)
        if all(v is not None for v in selected):
            continuing.append(selected)
    fs = child["families"]
    L = t.diff(sorted(fs["N10"] + fs["N01"] + fs["N11"]))
    Ns = [x[0] for x in continuing]
    Ps = [x[1] for x in continuing]
    offsets = sorted(set(t.plus((1, p), (-1, n)) for n, p in continuing))
    cert = dict(records=output, paired_survivors=len(continuing), offsets=offsets,
                old_rank_mod_L=t.rank(L + t.diff(Ns)) - t.rank(L),
                path_rank_mod_L=t.rank(L + t.diff(Ps)) - t.rank(L),
                equal_differences=t.diff(Ns) == t.diff(Ps))
    return cert, continuing


def surgeries():
    plan = surgery_plan()
    rows = []
    for spec in plan["rows"]:
        m = spec["m"]
        original = next(a for a in old("cut-octagons")["records"] if a["L"] == m)
        fixed = next(a for a in old("residual-certificates")["records"] if a["L"] == m)
        g, F = original["graph"], spec["protected"]
        pairs = list(zip(fixed["old_cycles"], fixed["residual_paths"]))
        for first in spec["steps"]:
            step1 = first["first"]
            h = t.expand(g, step1)
            r1 = t.analyze(h, t.find_step(h, original["e"], original["f"], F))
            r1["certification"] = t.certify_graph(h)
            r1["brace"] = t.brace_certificate(h)
            r1["cuts"] = t.cuts3(h)
            r1["transport"], pairs1 = transport(g, r1, pairs)
            r1["m"], r1["history"] = m, [step1]
            rows.append(r1)
            for step2 in first["second"]:
                h2 = t.expand(h, step2)
                r2 = t.analyze(h2, t.find_step(h2, original["e"], original["f"], F))
                r2["certification"] = t.certify_graph(h2)
                r2["brace"] = t.brace_certificate(h2)
                r2["cuts"] = t.cuts3(h2)
                r2["transport"], _ = transport(h, r2, pairs1)
                r2["m"], r2["history"] = m, [step1, step2]
                rows.append(r2)
    histogram = Counter((r["m"], len(r["history"]), r["brace"]["brace"],
                         r["row"]["ell"], r["row"]["t"], r["row"]["eta"]) for r in rows)
    return dict(plan=plan, records=rows,
                histogram=[dict(key=k, count=n) for k, n in sorted(histogram.items())],
                high_loss_braces=[i for i, r in enumerate(rows) if r["brace"]["brace"] and r["row"]["ell"] >= 2],
                tested=len(rows))


def audit_refinements():
    """Explicit constructions, port totals, and annihilator checks."""
    a = old("mandatory")["index431"]
    r = t.analyze(a["graph"], a["row"]["step"])
    fs = r["families"]
    L = t.diff(sorted(fs["N10"] + fs["N01"] + fs["N11"]))
    U = sum((t.diff(fs[k]) for k in ("Pux", "Pvy", "D11")), [])
    w = tuple(map(Fraction, a["separator"]["w"]))
    dot = lambda v: sum(x * y for x, y in zip(w, v))
    assert all(dot(v) == 0 for v in L + U)
    assert dot(r["bridge"]) == 10 and dot(a["old_direction"]) == 8
    assert t.rank(U + t.diff(fs["N00"])) > t.rank(U)
    assert t.rank(L + U + t.diff(fs["N00"])) > t.rank(L + U)
    constructions = []
    cube = next(x["base_graph"] for x in old("cut-octagons")["records"] if x["L"] == 4)
    cubeE = t.edges_of(cube)
    for a in old("cut-octagons")["records"]:
        m = a["L"]
        base = {t.edge(i, (i + 1) % m) for i in range(m)}
        base |= {t.edge(m + i, m + (i + 1) % m) for i in range(m)}
        base |= {t.edge(i, m + i) for i in range(m)}
        assert base == set(t.edges_of(a["base_graph"]))
        A, B = 2 * m, 2 * m + 8
        expected = {e for e in base if 0 not in e and m + 1 not in e}
        for off in (A, B):
            expected |= {t.edge(off + x, off + y) for x, y in cubeE if x != 0 and y != 0}
        expected |= {t.edge(1, A + 1), t.edge(m - 1, A + 4), t.edge(m, A + 3),
                     t.edge(1, B + 1), t.edge(m, B + 4), t.edge(m + 2, B + 3)}
        assert expected == set(t.edges_of(a["graph"]))
        F = [1, A + 1, A + 2, A + 3, m, B + 4, B + 5, B + 1]
        assert F in a["graph"]["faces"]
        assert t.edge(A + 3, m) == tuple(a["e"]) and t.edge(1, B + 1) == tuple(a["f"])
        C = t.cycles(t.edges_of(a["graph"]))
        constructions.append(dict(m=m, formula_edges=True, exact_octagon=F,
                                  cycles=len(C), ambient_dimension=len(expected) - a["graph"]["n"] + 1))
    ports = []
    for a in old("remote-splices")["rows"]:
        E = t.edges_of(a["graph"])
        cut = [t.edge(*pair) for pair in a["port_mapping"]]
        positions = [E.index(e) for e in cut]
        totals = [Fraction(0)] * 3
        for term in a["coefficients"]:
            signature = [term["C"][i] for i in positions]
            assert sum(signature) == 2
            totals[signature.index(0)] += Fraction(term["coefficient"])
        target = [a["N"][i] for i in positions]
        assert totals == [Fraction(int(i == target.index(0))) for i in range(3)]
        assert [totals[1] + totals[2], totals[0] + totals[2], totals[0] + totals[1]] == target
        # Reconstruct remote splice graph from explicit port identification.
        coreE, attE = t.edges_of(a["base_graph"]), t.edges_of(a["attachment"])
        z, off = a["splice_vertex"], max(t.adjacency(coreE)) + 1
        expected = {e for e in coreE if z not in e}
        expected |= {t.edge(off + x, off + y) for x, y in attE if x != 0 and y != 0}
        expected |= set(cut)
        assert expected == set(E)
        ports.append(dict(m=a["L"], cut=cut, totals=list(map(str, totals)), target=target,
                          q=a["N00_coefficient_total"]))
    cap_reconstruction = []
    for a in old("cap-transport")["records"]:
        m, j, k = a["L"], a["top_partner"], a["bottom_partner"]
        s1 = t.find_step(a["base_graph"], t.edge(0, 1), t.edge(j, j + 1))
        first = t.expand(a["base_graph"], s1)
        assert t.edges_of(first) == t.edges_of(a["intermediate_graph"])
        s2 = t.find_step(first, t.edge(m, m + 1), t.edge(m + k, m + k + 1))
        second = t.expand(first, s2)
        assert t.edges_of(second) == t.edges_of(a["graph"])
        cap_reconstruction.append(dict(m=m, partners=[j, k], regenerated=True))
    return dict(status="PASS", separator431=dict(bridge=10, old=8, annihilates="L+U"),
                formula_constructions=constructions, port_total_checks=ports,
                cap_reconstruction=cap_reconstruction)


def independent_subset(rows):
    pivots, selected = {}, []
    for i, row in enumerate(rows):
        r = list(map(Fraction, row))
        for k in sorted(pivots):
            q = r[k]
            if q:
                r = [x - q * y for x, y in zip(r, pivots[k])]
        k = next((j for j, x in enumerate(r) if x), None)
        if k is not None:
            q = r[k]
            pivots[k] = [x / q for x in r]
            selected.append(i)
    return selected


def coordinates(basis, vectors):
    """Exact rational coordinates plus explicit remainder, never an approximate solve."""
    n = len(basis)
    pivots = {}
    for i, b in enumerate(basis):
        r = list(map(Fraction, b))
        weights = [Fraction(int(j == i)) for j in range(n)]
        for k in sorted(pivots):
            v, w = pivots[k]
            q = r[k]
            if q:
                r = [x - q * y for x, y in zip(r, v)]
                weights = [x - q * y for x, y in zip(weights, w)]
        k = next(j for j, x in enumerate(r) if x)
        q = r[k]
        pivots[k] = ([x / q for x in r], [x / q for x in weights])
    out = []
    for vector in vectors:
        r = list(map(Fraction, vector))
        weights = [Fraction(0)] * n
        for k in sorted(pivots):
            v, w = pivots[k]
            q = r[k]
            if q:
                r = [x - q * y for x, y in zip(r, v)]
                weights = [x + q * y for x, y in zip(weights, w)]
        assert all(Fraction(vector[j]) == r[j] + sum(weights[i] * basis[i][j] for i in range(n))
                   for j in range(len(vector)))
        out.append(dict(direction=vector, coefficients=list(map(str, weights)),
                        remainder=list(map(str, r)), absorbed=not any(r)))
    return out


def post_analysis():
    population = data("frontier/experiments/i173_brace_high_loss_octagons/surgeries-attempt-01.json")
    records = population["records"]
    certificates = []
    histogram = Counter()
    cut_histogram = Counter()
    deficit_histogram = Counter()
    transport_histogram = Counter()
    for i, a in enumerate(records):
        fs, g = a["families"], a["graph"]
        E = t.edges_of(g)
        S = sorted(fs["N10"] + fs["N01"] + fs["N11"])
        directions = t.diff(S)
        indices = independent_subset(directions)
        basis = [directions[j] for j in indices]
        assert t.rank(basis) == a["row"]["rankL"]
        ambient = len(E) - g["n"] + 1
        # Each displayed cycle is checked directly independently of the population's
        # membership assertion. The ambient bound needs no cycle exhaustion.
        chosen = [S[0]] + [S[j + 1] for j in indices]
        uvxy = t.interface(g, a["row"]["step"])
        deleted_positions = [E.index(t.edge(*uvxy[:2])), E.index(t.edge(*uvxy[2:]))]
        for C in chosen:
            assert all(val in (0, 1) for val in C)
            assert any(C[j] for j in deleted_positions)
            ce = [e for e, val in zip(E, C) if val]
            assert all(len(z) == 2 for z in t.adjacency(ce).values())
            assert len(t.adjacency(ce)) == g["n"]
            assert len(t.components(t.adjacency(E), ce)) == 1
        pairs = []
        for entry in a["transport"]["records"]:
            Ns, Ps = entry["N00"]["extensions"], entry["Pux"]["extensions"]
            if Ns and Ps:
                pairs.append((Ns[0], Ps[0]))
        old_dirs, path_dirs = t.diff([x[0] for x in pairs]), t.diff([x[1] for x in pairs])
        old_coordinates, path_coordinates = coordinates(basis, old_dirs), coordinates(basis, path_dirs)
        assert t.rank(basis + old_dirs) - len(basis) == a["transport"]["old_rank_mod_L"]
        assert t.rank(basis + path_dirs) - len(basis) == a["transport"]["path_rank_mod_L"]
        # Exhaustive cut enumeration now uses a bitset flood and independently
        # checks every found disconnection with the original set flood.
        assert json.loads(json.dumps(t.cuts3(g))) == a["cuts"]
        if len(a["history"]) == 1:
            untouched = list(range(2 * a["m"] + 9, 2 * a["m"] + 16))
            assert len(a["cuts"]) == 1 and untouched in a["cuts"][0]["sides"]
            cut_indices = sorted(E.index(tuple(e)) for e in a["cuts"][0]["edges"])
            assert a["brace"]["failed_pairs"] == [list(pair) for pair in combinations(cut_indices, 2)]
        else:
            assert not a["cuts"]
        r = a["row"]
        histogram[(a["m"], len(a["history"]), a["brace"]["brace"], r["ell"], r["t"], r["eta"])] += 1
        cut_histogram[(len(a["history"]), len(a["cuts"]))] += 1
        deficit_histogram[(len(a["history"]), r["delta_V"], r["delta_R"], r["epsilon"])] += 1
        transport_histogram[(len(a["history"]), a["transport"]["paired_survivors"],
                             a["transport"]["old_rank_mod_L"], a["transport"]["path_rank_mod_L"],
                             a["transport"]["equal_differences"])] += 1
        cert = dict(record=i, m=a["m"], history=a["history"], anchor=S[0],
                    survivor_basis_cycles=chosen[1:], survivor_rank=len(basis),
                    ambient_degree_kernel_dimension=ambient,
                    upper_bound_on_loss=ambient - len(basis),
                    old_direction_coordinates=old_coordinates, path_direction_coordinates=path_coordinates,
                    brace=a["brace"]["brace"], nontrivial_three_cuts=len(a["cuts"]))
        if a["brace"]["brace"] and r["ell"] >= 2:
            # Validate the actual protected expansion, not merely the interface algebra.
            child = t.expand(g, r["step"])
            cert["expanded_graph"] = child
            cert["expanded_certification"] = t.certify_graph(child)
            cert["expanded_cycles"] = t.cycles(t.edges_of(child))
            dh = t.rank(t.diff(cert["expanded_cycles"]))
            assert dh == 2 + r["rankL"] + r["t"] + r["eta"]
            cert["expanded_rank"] = dh
            cert["lower_bound_holds"] = r["delta_R"] >= r["delta_V"] + r["epsilon"] - 1
            cert["exchange_holds"] = r["delta_R"] + r["eta"] >= r["delta_V"] + r["epsilon"]
        certificates.append(cert)
    hist = lambda c: [dict(key=k, count=n) for k, n in sorted(c.items())]
    return dict(status="PASS", records=certificates, population=len(records),
                histogram=hist(histogram), cut_histogram=hist(cut_histogram),
                deficit_histogram=hist(deficit_histogram), transport_histogram=hist(transport_histogram),
                high_loss_braces=population["high_loss_braces"],
                all_loss_at_most_one=all(c["upper_bound_on_loss"] <= 1 for c in certificates),
                all_depth_two_loss_at_most_one=all(c["upper_bound_on_loss"] <= 1 for c in certificates if len(c["history"]) == 2))
