"""Recompute all base traversal profiles for the infinite counterexample family."""
import json
import runpy
from pathlib import Path

g = runpy.run_path(str(Path(__file__).with_name("graphs.py")))


def run():
    faces = g["prism"](12)
    faces, _ = g["square"](faces, (0, 8, 10))
    faces, _ = g["square"](faces, (0, 2, 8))
    new, (u, v, x, y) = g["square"](faces, (8, 1, 5))
    es, nes = g["edges"](faces), g["edges"](new)
    e, f = g["edge"](u, v), g["edge"](x, y)
    factors = g["matching_factors"](es)
    k = [z for z in es if z not in (e, f)]
    families = {
        "h": {h for h, c in factors if len(c) == 1},
        "h_prime": g["pruned_paths"](nes, 0),
        "N00": {h for h, c in factors if len(c) == 1 and e not in h and f not in h},
        "Pux": g["pruned_paths"](k, u, x),
        "Pvy": g["pruned_paths"](k, v, y),
        "D11": {h for h, c in factors if len(c) == 2 and e in h and f in h
                and not any(u in cc and x in cc for cc in c)}
    }
    assert families["h"] == g["pruned_paths"](es, 0)
    profiles = {}
    for name, hs in families.items():
        ports = [sum(g["edge"](21, w) not in h for h in hs) for w in (9, 22, 28)]
        # 2*a0 + (m-2)*a1 + 2*a2.
        profiles[name] = {"ports": ports, "coefficient_m": ports[1],
                          "constant": 2*(ports[0]+ports[2]-ports[1])}
    assert profiles["N00"]["ports"] == [5, 16, 0]
    assert profiles["Pux"]["ports"] == [3, 4, 0]
    assert profiles["Pvy"]["ports"] == [1, 1, 21]
    assert profiles["D11"]["ports"] == [3, 3, 7]
    return {"base_terminals": [u, v, x, y], "base_vertex": 21,
            "base_neighbors": [9, 22, 28], "profiles": profiles,
            "family_scope": "Every even m >= 4; M fails for every even m >= 10",
            "n": "2*m+30", "n_prime": "2*m+34", "gain": "76-8*m"}


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
