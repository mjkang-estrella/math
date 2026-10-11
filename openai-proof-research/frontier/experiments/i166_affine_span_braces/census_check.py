"""Cross-check the generated census against the published enumeration.

OEIS A007083 (Holton-Manvel-McKay generation lineage; Brinkmann-McKay
plantri terms): unlabeled trivalent 3-connected bipartite planar graphs
on 2n nodes, orders 8..20: 1, 0, 1, 1, 2, 2, 8.  I166's BFS over square
and cube expansions with rotation-system canonical dedup must reproduce
exactly these counts.  The published terms are stored as owned bytes in
sources/i166_affine_span_braces/oeis-a007083.txt.
"""
import json
import runpy
from pathlib import Path

HERE = Path(__file__).resolve().parent
SOURCE = HERE.parents[1] / "sources" / "i166_affine_span_braces"
L = runpy.run_path(str(HERE / "lib166.py"))

PUBLISHED = {8: 1, 10: 0, 12: 1, 14: 1, 16: 2, 18: 2, 20: 8}


def run():
    graphs = json.loads((HERE / "bracegen-graphs.json").read_text())
    mine = {}
    for rec in graphs["bfs"].values():
        mine[rec["n"]] = mine.get(rec["n"], 0) + 1
    # every generated graph carries a full certificate rechecked here
    for rec in graphs["bfs"].values():
        L["certify"]([list(f) for f in rec["faces"]])
    assert all(mine.get(n, 0) == c for n, c in PUBLISHED.items()), \
        (mine, PUBLISHED)
    return {"orders_checked": sorted(PUBLISHED),
            "published_counts": PUBLISHED, "my_counts": mine,
            "graphs_recertified": len(graphs["bfs"]),
            "status": "PASS: matches OEIS A007083 through order 20"}


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
