"""Long-residual-path search, plus recoverable short-side injection checks."""
import json
import random
import runpy
from pathlib import Path

g = runpy.run_path(str(Path(__file__).with_name("graphs.py")))


def run(seeds=30, depth=5):
    records = []
    for seed in range(seeds):
        rng = random.Random(165500+seed)
        faces = g["prism"](8+2*(seed % 3))
        history = [{"prism": 8+2*(seed % 3)}]
        for level in range(depth):
            cert = g["certificate"](faces)
            fs = g["matching_factors"](g["edges"](faces))
            hs = [fac for fac, comp in fs if len(comp) == 1]
            choices, long = [], []
            for step in g["steps"](faces):
                fi, i, j = step
                _, (u, v, x, y) = g["square"](faces, step)
                e, f = g["edge"](u, v), g["edge"](x, y)
                n00 = sum(e not in h and f not in h for h in hs)
                choices.append((n00, step))
                if j-i >= 4 and len(faces[fi])-(j-i) >= 4:
                    long.append((n00, step))
            long.sort(reverse=True)
            selected = [z[1] for z in long[:3]]
            if long:
                selected.append(rng.choice(long)[1])
            for step in dict.fromkeys(selected):
                result = g["boundary"](faces, step)
                records.append({"seed": seed, "level": level, "history": history[:],
                                "certificate": cert, "step": list(step), **result})
            if level+1 < depth:
                if seed % 3 == 0 and level % 2 == 0:
                    v = rng.choice(sorted(g["adjacency"](g["edges"](faces))))
                    faces = g["cube_expand"](faces, v)
                    history.append({"cube": v})
                else:
                    # Preserve long faces often, but vary the construction.
                    step = rng.choice(choices)[1]
                    faces, _ = g["square"](faces, step)
                    history.append({"square": list(step)})
    return records


if __name__ == "__main__":
    import sys
    print(json.dumps(run(*(map(int, sys.argv[1:]))), indent=2))
