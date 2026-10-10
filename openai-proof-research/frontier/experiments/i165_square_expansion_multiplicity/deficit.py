"""Detect a local deficit and compute exact prism-splice amplification."""
import json
import runpy
from pathlib import Path

g = runpy.run_path(str(Path(__file__).with_name("graphs.py")))


def run(records):
    hits = []
    cache = {}
    for index, rec in enumerate(records):
        faces = rec["certificate"]["faces"]
        key = repr(faces)
        if key not in cache:
            cache[key] = [h for h, c in g["matching_factors"](g["edges"](faces))
                          if len(c) == 1]
        old_h = cache[key]
        new, terminals = g["square"](faces, rec["step"])
        new_h = [h for h, c in g["matching_factors"](g["edges"](new)) if len(c) == 1]
        for v, neighbors in g["adjacency"](g["edges"](faces)).items():
            if v in terminals:
                continue
            aa = [sum(g["edge"](v, w) not in h for h in old_h) for w in neighbors]
            bb = [sum(g["edge"](v, w) not in h for h in new_h) for w in neighbors]
            delta = [b-a for a, b in zip(aa, bb)]
            for port, d in enumerate(delta):
                if d < 0:
                    m = 4
                    while 2*rec["gain"] + (m-4)*d >= 2:
                        m += 2
                    hits.append({"index": index, "v": v, "neighbors": neighbors,
                                 "port": port, "old_ports": aa, "new_ports": bb,
                                 "delta": delta, "prism_m": m,
                                 "splice_n": rec["certificate"]["n"]+2*m-2,
                                 "splice_gain": 2*rec["gain"]+(m-4)*d})
    return sorted(hits, key=lambda x: (x["splice_n"], x["splice_gain"],
                                      x["index"], x["v"], x["port"]))


if __name__ == "__main__":
    print(json.dumps(run(json.loads(Path(__file__).with_name("targeted-01.json").read_text())),
                     indent=2))
