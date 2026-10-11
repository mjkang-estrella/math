"""Independent checks of full-scope path and dual-transfer obstructions."""
from fractions import Fraction
import itertools
import json
from pathlib import Path
import runpy

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
K = runpy.run_path(str(HERE / "kernel.py"))
globals().update({k: v for k, v in K.items() if not k.startswith("_")})


def fractional_rank(rows):
    rows = [[Fraction(x) for x in row] for row in rows]
    if not rows:
        return 0
    pivot = 0
    for col in range(len(rows[0])):
        i = next((i for i in range(pivot, len(rows)) if rows[i][col]), None)
        if i is None:
            continue
        rows[pivot], rows[i] = rows[i], rows[pivot]
        scale = rows[pivot][col]
        rows[pivot] = [x/scale for x in rows[pivot]]
        for i in range(pivot+1, len(rows)):
            scale = rows[i][col]
            rows[i] = [x-scale*y for x, y in zip(rows[i], rows[pivot])]
        pivot += 1
        if pivot == len(rows):
            break
    return pivot


def dual_shores(faces, es, hs):
    owner = {e: [] for e in es}
    for i, f in enumerate(faces):
        for a, b in zip(f, f[1:]+f[:1]):
            owner[edge(a, b)].append(i)
    dual = {e: edge(*pair) for e, pair in owner.items()}
    shores = []
    for h in hs:
        nonhc = [dual[e] for e in es if not (h >> es.index(e) & 1)]
        nb = adjacency(nonhc)
        rootpart = {0}
        todo = [0]
        for a in todo:
            for b in nb.get(a, ()):
                if b not in rootpart:
                    rootpart.add(b)
                    todo.append(b)
        other = set(range(len(faces)))-rootpart
        assert other and connected(nonhc, other)
        for part in (rootpart, other):
            induced = [e for e in dual.values() if set(e) <= part]
            assert connected(induced, part) and len(induced) == len(part)-1
        shores.append(frozenset(other))
    assert len(set(shores)) == len(hs)
    for a, b in itertools.combinations(shores, 2):
        assert not a < b and not b < a
    return shores


def generic_cycles(es):
    nb = adjacency(es)
    root = min(nb)
    ans = set()
    def walk(v, used, path):
        if len(used) == len(nb):
            if root in nb[v]:
                ans.add(frozenset(path+[edge(v, root)]))
            return
        for w in nb[v]-used:
            walk(w, used | {w}, path+[edge(v, w)])
    walk(root, {root}, [])
    return ans


def retract(es, deleted):
    u, v = deleted
    nb = adjacency(es)
    a, b = sorted(nb[u]-{v})
    c, d = sorted(nb[v]-{u})
    X, Y = {u, a, b}, {v, c, d}
    if X & Y:
        return None
    ren = {z: u if z in X else v if z in Y else z for z in nb}
    remain = [e for e in es if e != deleted and not set(e) <= X and not set(e) <= Y]
    res = [edge(ren[x], ren[y]) for x, y in remain]
    if len(set(res)) != len(res) or any(x == y for x, y in res):
        return None
    res = tuple(sorted(res))
    return res, ren, (a, b, c, d), dict(zip(remain, (edge(ren[x], ren[y]) for x, y in remain)))


def run():
    raw = json.loads((ROOT/"frontier/experiments/i166_affine_span_braces/bracegen-graphs.json").read_text())
    previous = json.loads((HERE/"diagnostic-attempt-01.json").read_text())
    census = list(raw["bfs"].values())
    rank_checks, antichain_checks, path_checks = [], [], []
    face_alternating = face_toggleable = face_count = 0
    for rec in census:
        faces = rec["faces"]
        es, hs = edges(faces), cycles(edges(faces))
        r = fractional_rank(differences(hs, len(es)))
        assert r == dimension(es)
        rank_checks.append({"n": rec["n"], "rank": r})
        sh = dual_shores(faces, es, hs)
        antichain_checks.append({"n": rec["n"], "h": len(hs),
                                "rooted_shores": [sorted(a) for a in sh]})
        for f in faces:
            face_count += 1
            fm = sum(1 << es.index(edge(a, b)) for a, b in zip(f, f[1:]+f[:1]))
            alt = toggle = False
            for h in hs:
                chosen = set(selected(es, h))
                if all(sum(edge(v, w) in chosen for w in (f[i-1], f[(i+1) % len(f)])) == 1
                       for i, v in enumerate(f)):
                    alt = True
                    if h ^ fm in hs:
                        toggle = True
            face_alternating += alt
            face_toggleable += toggle
        for st in steps(faces):
            child, labels = expand(faces, st)
            u, v, x, y, p, q, rr, s = labels
            reduced = tuple(e for e in es if e not in (edge(u, v), edge(x, y)))
            beta = len(reduced)-rec["n"]+1
            fixed_free = tuple(e for e in reduced if v not in e and y not in e)
            assert connected(fixed_free, set(adjacency(es))-{v, y})
            bound = beta-2+int(edge(v, y) in reduced)
            old = next(row for row in previous["expansions"]
                       if row["parent_history"] == rec["history"] and row["step"] == list(st))
            assert old["path_rank"] <= bound < beta
            # The survivor lift is affine and injective.
            ei, fi = es.index(edge(u, v)), es.index(edge(x, y))
            survivors = [h for h in hs if h >> ei & 1 or h >> fi & 1]
            ce = edges(child)
            lifted = []
            for h in survivors:
                E, F = (h >> ei) & 1, (h >> fi) & 1
                coeff = {z: int(h >> es.index(z) & 1) for z in reduced}
                for z in (edge(u, p), edge(v, q)):
                    coeff[z] = E
                for z in (edge(x, rr), edge(y, s)):
                    coeff[z] = F
                coeff[edge(p, q)], coeff[edge(rr, s)] = F, E
                coeff[edge(p, rr)] = coeff[edge(q, s)] = 2-E-F
                mask = sum(coeff[z] << i for i, z in enumerate(ce))
                assert mask in cycles(ce)
                lifted.append(mask)
            assert dimension(ce, lifted) == old["d_survival"]
            path_checks.append({"n": rec["n"], "step": list(st),
                                "beta": beta, "path_upper_bound": bound,
                                "actual_path_rank": old["path_rank"],
                                "transport_rank": old["d_survival"],
                                "required_new_rank": old["d_parent"]+2-old["d_survival"]})
    assert face_toggleable == 0
    # McCuaig-style index-two retract on the first small non-prism brace
    # admitting a simple brace retract. Explicitly test the typed HC interface.
    retract_witness = None
    for rec in census:
        es = edges(rec["faces"])
        if not brace(es):
            continue
        for deleted in es:
            ret = retract(es, deleted)
            if ret is None:
                continue
            re, ren, outer, emap = ret
            if not brace(re):
                continue
            u, v = deleted
            a, b, c, d = outer
            assert sorted(map(len, adjacency(re).values())).count(4) == 2
            rhs = generic_cycles(re)
            admissible = []
            for cycle in rhs:
                ok = True
                for oldvertex in (a, b, c, d):
                    corresponding = [image for e, image in emap.items() if oldvertex in e]
                    if sum(e in cycle for e in corresponding) != 1:
                        ok = False
                if ok:
                    admissible.append(cycle)
            avoiding = [set(selected(es, h)) for h in cycles(es)
                        if not (h >> es.index(deleted) & 1)]
            contracted = {frozenset(emap[e] for e in h if e in emap) for h in avoiding}
            assert contracted == set(admissible)
            retract_witness = {"n": rec["n"], "faces": rec["faces"], "deleted": deleted,
                               "retract_edges": re, "retract_degrees": sorted(map(len, adjacency(re).values())),
                               "all_retract_hc": len(rhs), "admissible_retract_hc": len(admissible),
                               "original_avoiding_hc": len(avoiding)}
            break
        if retract_witness:
            break
    assert retract_witness is not None
    return {"fractional_rank_checks": rank_checks, "dual_antichain": antichain_checks,
            "path_and_transport_checks": path_checks, "mccuaig_retract": retract_witness,
            "face_sweep": {"faces": face_count, "alternated_faces": face_alternating,
                           "toggleable_faces": face_toggleable},
            "summary": {"fractional_rank_crosschecks": len(rank_checks),
                        "dual_antichain_graphs": len(antichain_checks),
                        "path_obstruction_and_transport_checks": len(path_checks),
                        "maximum_required_extra_rank": max(r["required_new_rank"] for r in path_checks)}}


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
