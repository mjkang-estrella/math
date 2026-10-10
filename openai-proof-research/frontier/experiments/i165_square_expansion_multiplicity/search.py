"""Seeded varied-history search. Executed only as owned diagnostic."""
import json
import random
import runpy
from pathlib import Path

g = runpy.run_path(str(Path(__file__).with_name("graphs.py")))


def run(seeds=16, depth=6):
    records = []
    for seed in range(seeds):
        rng = random.Random(165000+seed)
        faces = g["prism"](4 + 2*(seed % 3))
        history = [{"prism": 4+2*(seed % 3)}]
        for level in range(depth):
            cert = g["certificate"](faces)
            fs = g["matching_factors"](g["edges"](faces))
            hs = [fac for fac, comp in fs if len(comp) == 1]
            choices = []
            for step in g["steps"](faces):
                _, (u, v, x, y) = g["square"](faces, step)
                e, f = g["edge"](u, v), g["edge"](x, y)
                n00 = sum(e not in h and f not in h for h in hs)
                choices.append((n00, step))
            # Test a large-lost-family step and two independently selected steps.
            choices.sort(reverse=True)
            selected = [choices[0][1]] + [z[1] for z in rng.sample(choices, min(2, len(choices)))]
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
                    step = rng.choice(choices)[1]
                    faces, _ = g["square"](faces, step)
                    history.append({"square": list(step)})
    return records


if __name__ == "__main__":
    import sys
    records = run(*(map(int, sys.argv[1:])))
    print(json.dumps(records, indent=2))
