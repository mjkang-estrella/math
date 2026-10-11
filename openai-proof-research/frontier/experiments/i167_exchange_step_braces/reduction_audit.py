"""Independent HMM reduction scope and rank-row certificates."""
import json
from pathlib import Path
import runpy

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
K = runpy.run_path(str(HERE / "kernel.py"))
globals().update({k: v for k, v in K.items() if not k.startswith("_")})


def run():
    raw = json.loads((ROOT / "frontier/experiments/i166_affine_span_braces/bracegen-graphs.json").read_text())
    census = list(raw["bfs"].values())
    tested = []
    for rec in census:
        es = edges(rec["faces"])
        if rec["n"] == 8 or not brace(es):
            continue
        for fi, face in enumerate(rec["faces"]):
            if len(face) != 4:
                continue
            ok = []
            for flip in (False, True):
                child = contract_square(es, face, flip)
                if child is not None:
                    target = [r for r in census if r["n"] == rec["n"]-4
                              and isomorphic(child, edges(r["faces"]))]
                    assert len(target) == 1
                    ok.append(flip)
            assert ok
            tested.append({"n": rec["n"], "history": rec["history"], "face": fi,
                           "class_valid_pairings": ok})
    return {"braces": len({r["history"] for r in tested}),
            "four_faces": len(tested), "applications": 2*len(tested),
            "cube_excluded_by_HMM_order_greater_than_eight": True, "rows": tested}


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
