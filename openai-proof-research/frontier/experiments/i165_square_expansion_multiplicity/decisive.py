"""Self-contained 50 -> 54 vertex counterexample, independent of search data."""
import json
import runpy
from pathlib import Path

g = runpy.run_path(str(Path(__file__).with_name("graphs.py")))


def encode(family):
    return sorted([sorted([list(e) for e in h]) for h in family])


def run():
    faces = g["prism"](12)
    faces, _ = g["square"](faces, (0, 8, 10))
    faces, _ = g["square"](faces, (0, 2, 8))
    base_new, terminals = g["square"](faces, (8, 1, 5))
    assert terminals == (29, 28, 24, 25)
    base_h = g["pruned_paths"](g["edges"](faces), 0)
    base_nh = g["pruned_paths"](g["edges"](base_new), 0)
    assert len(base_h) == 102 and len(base_nh) == 124
    neighbors = [9, 22, 28]
    aa = [sum(g["edge"](21, w) not in h for h in base_h) for w in neighbors]
    bb = [sum(g["edge"](21, w) not in h for h in base_nh) for w in neighbors]
    assert aa == [34, 62, 6] and bb == [36, 54, 34]
    big, relabel = g["splice"](faces, 21, g["prism"](10), 0,
                               {9: 1, 22: 10, 28: 9})
    chosen = []
    for step in g["steps"](big):
        _, t = g["square"](big, step)
        if {g["edge"](*t[:2]), g["edge"](*t[2:])} == {(28, 29), (24, 25)}:
            chosen.append(step)
    assert len(chosen) == 1
    step = chosen[0]
    new, t = g["square"](big, step)
    old_cert, new_cert = g["certificate"](big), g["certificate"](new)
    # Independent global traversal enumerator, not splice multiplication.
    old_cycles = g["pruned_paths"](g["edges"](big), 0)
    new_cycles = g["pruned_paths"](g["edges"](new), 0)
    assert len(old_cycles) == 576 and len(new_cycles) == 572
    result = g["boundary"](big, step, independent=(old_cycles, new_cycles))
    assert result["h"] == len(old_cycles) and result["h_prime"] == len(new_cycles)
    assert result["gain"] == -4
    # Full edge-set list is a recoverable exact certificate, not just totals.
    return {"construction": {"base_prism": 12, "base_squares": [[0, 8, 10], [0, 2, 8]],
                             "base_vertex": 21, "base_neighbors": neighbors,
                             "attached_prism": 10, "attached_vertex": 0,
                             "port_map": {"9": 1, "22": 10, "28": 9},
                             "relabel": {str(k): v for k, v in relabel.items()}},
            "base_certificate": g["certificate"](faces),
            "base_expanded_certificate": g["certificate"](base_new),
            "base_old_ports": aa, "base_new_ports": bb,
            "attachment_ports": [2, 8, 2],
            "certificate": old_cert, "expanded_certificate": new_cert,
            "step": list(step), **result,
            "arm_fibres": g["arm_fibres"](big, step, new_cycles),
            "old_cycles": encode(old_cycles), "new_cycles": encode(new_cycles)}


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
