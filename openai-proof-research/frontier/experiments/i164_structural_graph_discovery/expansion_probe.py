"""Bounded C4-expansion search; exact counts, no writes."""
import importlib.util
import itertools
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
spec = importlib.util.spec_from_file_location("own_explore", HERE / "explore.py")
base = importlib.util.module_from_spec(spec)
spec.loader.exec_module(base)


def facial_cycles(n, chords, colors):
    mate = {}
    side = {}
    for (a, b), c in zip(chords, colors):
        mate[a] = b
        mate[b] = a
        side[a] = side[b] = c
    rot = {}
    for v in range(n):
        prev, nxt = (v - 1) % n, (v + 1) % n
        rot[v] = [nxt, mate[v], prev] if side[v] == 0 else [nxt, prev, mate[v]]
    return rotation_faces(rot)


def rotation_faces(rot):
    unused = {(u, v) for u, ns in rot.items() for v in ns}
    faces = []
    while unused:
        u, v = min(unused)
        face = []
        while (u, v) in unused:
            unused.remove((u, v))
            face.append(u)
            ns = rot[v]
            u, v = v, ns[(ns.index(u) + 1) % len(ns)]
        faces.append(face)
    return faces


def expanded(n, edges, u, v, x, y):
    p, q, r, s = range(n, n + 4)
    old = set(map(tuple, edges)) - {tuple(sorted((u, v))), tuple(sorted((x, y)))}
    new = [(u, p), (v, q), (x, r), (y, s), (p, q), (r, s), (p, r), (q, s)]
    return sorted(old | {tuple(sorted(e)) for e in new})


def main():
    data = json.loads((HERE / "discovery-01.json").read_text())
    output = []
    for item in data["results"]:
        if item["best"] is None or item["n"] > 20:
            continue
        g = item["best"]
        n = g["n"]
        faces = facial_cycles(n, g["chords"], g["colors"])
        assert len(faces) == n // 2 + 2
        h0 = g["h"]
        for face in faces:
            for i, j in itertools.combinations(range(len(face)), 2):
                if (j - i) % 2:
                    continue
                u, v = face[i], face[(i + 1) % len(face)]
                y, x = face[j], face[(j + 1) % len(face)]
                e = expanded(n, g["edges"], u, v, x, y)
                h1 = len(base.cycles(n + 4, e))
                output.append(dict(n=n, h_before=h0, h_after=h1, gain=h1-h0,
                                   terminals=[u, v, x, y], face=face,
                                   before=g["edges"], after=e))
    print(json.dumps(dict(tested=len(output), minimum_gain=min(x["gain"] for x in output),
                         decreases=[x for x in output if x["gain"] < 2],
                         first=output[0]), indent=2))


if __name__ == "__main__":
    main()
