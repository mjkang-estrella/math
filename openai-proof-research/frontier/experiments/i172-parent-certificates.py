"""Parent-only DFS and exact-rank checks; no child Python is imported."""
import hashlib
import json
import runpy
from fractions import Fraction as Q
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BASE = ROOT / "frontier/experiments/i172_prescribed_square_switch"
PARENT_DFS = BASE.parent / "i171-parent-certificates.py"
DFS = runpy.run_path(str(PARENT_DFS))
edge, paths, cycles, terminals = (DFS[k] for k in ("edge", "paths", "cycles", "terminals"))


def read(name):
    return json.loads((BASE / name).read_text())


def vec(es, chosen):
    return tuple(int(e in chosen) for e in es)


def minus(a, b):
    return tuple(x-y for x, y in zip(a, b))


def differences(rows):
    return [minus(r, rows[0]) for r in rows[1:]] if rows else []


def rank(rows):
    basis = {}
    for row in rows:
        v = list(map(Q, row))
        for j, b in sorted(basis.items()):
            t = v[j]
            if t:
                v = [x-t*y for x, y in zip(v, b)]
        if any(v):
            j = next(j for j, x in enumerate(v) if x)
            basis[j] = [x/v[j] for x in v]
    return len(basis)


def families(graph, step):
    es = list(map(tuple, graph["edges"]))
    vs = {v for e in es for v in e}
    u, v, x, y = terminals(graph, step)
    e, f = edge(u, v), edge(x, y)
    hc = cycles(es, vs)
    result = {"N%d%d" % (a, b): [vec(es, h) for h in hc if (e in h, f in h) == (a, b)]
              for a in (0, 1) for b in (0, 1)}
    k = set(es) - {e, f}
    result["Pux"] = [vec(es, p) for p in paths(k, u, x, vs)]
    result["Pvy"] = [vec(es, p) for p in paths(k, v, y, vs)]
    covers = set()
    for p in paths(k, u, v, vs, spanning=False):
        used = {w for t in p for w in t}
        if x in used or y in used:
            continue
        for q in paths(k, x, y, vs-used):
            covers.add(p | q)
    result["D11"] = [vec(es, p) for p in covers]
    return es, result


def main():
    octagons = []
    for saved in read("cut-octagons-attempt-01.json")["records"]:
        m, graph, step = saved["L"], saved["graph"], saved["row"]["step"]
        es, fam = families(graph, step)
        for name, rows in fam.items():
            assert set(rows) == {tuple(z) for z in saved["families"][name]}, (m, name)
        survivor = fam["N10"] + fam["N01"] + fam["N11"]
        old = fam["N00"]
        L, V = differences(survivor), differences(old)
        L0 = sum((differences(fam[n]) for n in ("N10", "N01", "N11")), [])
        U = sum((differences(fam[n]) for n in ("Pux", "Pvy", "D11")), [])
        u, v, x, y = terminals(graph, step)
        ef = vec(es, {edge(u, v), edge(x, y)})
        b = tuple(p+q+d+2*h-3*s for p, q, d, h, s in
                  zip(fam["Pux"][0], fam["Pvy"][0], fam["D11"][0], ef, survivor[0]))
        c = tuple(n-a-b+c for n, a, b, c in zip(old[0], fam["N10"][0], fam["N01"][0], fam["N11"][0]))
        dg, dl, lu = rank(differences(survivor+old)), rank(L), rank(L+U)
        assert (dg, dl, rank(L0)) == (m+7, 10, 8)
        assert (dg-dl, lu-dl, rank(L+U+[b])-lu) == (m-3, m-4, 1)
        assert rank(L0+V) == rank(L0+U) == rank(L0+V+U) == m+4
        assert rank(L0+V+[c]) - rank(L0+V) == 1
        for name, info in saved["row"]["classes"].items():
            assert not [n for n in old if minus(n, info["q"]) in fam[name]]
        sep = list(map(Q, saved["bridge_separator"]))
        assert all(sum(x*y for x, y in zip(sep, r)) == 0 for r in L+U)
        assert sum(x*y for x, y in zip(sep, b)) == 1
        residual = next(z for z in read("residual-certificates-attempt-01.json")["records"] if z["L"] == m)
        olds = list(map(tuple, residual["old_cycles"]))
        ps = list(map(tuple, residual["residual_paths"]))
        assert len(olds) == len(ps) == m-3
        assert set(olds) <= set(old) and set(ps) <= set(fam["Pux"])
        assert {minus(p, n) for p, n in zip(ps, olds)} == {tuple(residual["translation_offset"])}
        assert rank(L+differences(ps)) - dl == m-4
        octagons.append({"m": m, "order": graph["n"], "cycles": len(survivor+old),
                         "ell_t_eta": [dg-dl, lu-dl, 1], "delta_V_delta_R_epsilon": [m-4, m-4, 1],
                         "compatible_old_families": "all empty", "residual_rank_mod_L": m-4})

    signed = []
    for saved in read("remote-splices-attempt-01.json")["rows"]:
        graph, step = saved["graph"], saved["row"]["step"]
        es = list(map(tuple, graph["edges"]))
        vs = {v for e in es for v in e}
        hc = {vec(es, c) for c in cycles(es, vs)}
        assert hc == {tuple(c) for c in saved["cycles"]}
        coeff = [(tuple(z["C"]), Q(z["coefficient"])) for z in saved["coefficients"]]
        assert all(c in hc for c, a in coeff)
        assert sum(a for c, a in coeff) == 1
        assert tuple(sum(a*c[j] for c, a in coeff) for j in range(len(es))) == tuple(saved["F"])
        u, v, x, y = terminals(graph, step)
        ei, fi = es.index(edge(u, v)), es.index(edge(x, y))
        total = sum(a for c, a in coeff if not c[ei] and not c[fi])
        assert total == Q(1, saved["L"]-2) == Q(saved["N00_coefficient_total"])
        signed.append({"core_m": saved["L"], "attachment_order": saved["attachment"]["n"],
                       "lost_class_total": str(total), "exact_signed_sum": "PASS"})
    result = {"status": "PASS", "octagons": octagons, "signed_splices": signed,
              "method": "Parent DFS path/cycle enumeration, full family equality, independent Fraction elimination and direct rational vector sums",
              "reused_parent_DFS": str(PARENT_DFS.relative_to(ROOT)),
              "reused_parent_DFS_sha256": hashlib.sha256(PARENT_DFS.read_bytes()).hexdigest(),
              "child_python_imported": False}
    with (BASE.parent / "i172-parent-certificates.json").open("x") as stream:
        json.dump(result, stream, indent=2, sort_keys=True)
        stream.write("\n")
    print(json.dumps({"status": "PASS", "octagons": octagons, "signed_splices": len(signed)}, indent=2))


if __name__ == "__main__":
    main()
