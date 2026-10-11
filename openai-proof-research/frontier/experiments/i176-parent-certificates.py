"""Independent parent DFS/products and exact minors; no child code execution.

Uniform validity is the index-partition and parity proof in the disposition.
The finite checks below do not replace that proof.
"""
import hashlib
import json
import runpy
from fractions import Fraction
from itertools import product
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BASE = ROOT / "frontier/experiments/i176_uniform_five_port_rank"
HELPER = BASE.parent / "i175-parent-certificates.py"
H = runpy.run_path(str(HELPER))
edge, packings, cycles, rank, differences, minus = (
    H[k] for k in ("edge", "packings", "cycles", "rank", "differences", "minus"))


def det(rows):
    a = [list(map(Fraction, row)) for row in rows]
    value = Fraction(1)
    for j in range(len(a)):
        pivot = next((i for i in range(j, len(a)) if a[i][j]), None)
        if pivot is None:
            return Fraction(0)
        if pivot != j:
            a[pivot], a[j] = a[j], a[pivot]
            value = -value
        z = a[j][j]
        value *= z
        for i in range(j+1, len(a)):
            q = a[i][j]/z
            a[i] = [x-q*y for x, y in zip(a[i], a[j])]
    return value


def edges_of(words):
    return {edge(a, b) for word in words for a, b in zip(word, word[1:])}


def model(k):
    n, j = k-1, k-3
    T = lambda i: 12+i
    B = lambda i: 12+k+i
    s, t, p, q = range(12+2*k, 16+2*k)
    X = {T(i) for i in range(1, k)} | {B(i) for i in range(k)} | {p, q}
    Y = set(range(1, 12)) | {s, t}
    xe = sorted({edge(T(i), B(i)) for i in range(1, k)}
                | {edge(T(i), T(i+1)) for i in range(1, n) if i != j}
                | {edge(B(i), B((i+1) % k)) for i in range(k)}
                | {edge(T(j), p), edge(p, q), edge(q, T(n-1))})
    ye = [(1,7),(1,s),(2,3),(2,8),(2,t),(3,4),(3,9),(4,5),(4,10),
          (5,11),(6,7),(6,11),(7,8),(8,9),(9,10),(10,11),(s,t)]
    cut = [(1,T(1)),(5,T(n)),(6,B(0)),(s,p),(t,q)]
    return X, Y, xe, ye, cut, sorted(xe+ye+cut)


def exterior(k):
    s, t = 12+2*k, 13+2*k
    return [
        [[[1,s,t,2,3,4,5,11,10,9,8,7,6]]],
        [[[5,11,10,4,3,9,8,2,t,s,1,7,6]], [[5,4,3,2,t,s,1,7,8,9,10,11,6]]],
        [[[5,4,3,2,8,9,10,11,6,7,1,s,t]]],
        [[[6,11,5,4,10,9,3,2,8,7,1,s,t]]],
        [[[1,7,8,2,t,s],[5,4,3,9,10,11,6]],
         [[1,7,8,9,3,2,t,s],[5,4,10,11,6]],
         [[1,7,8,9,10,4,3,2,t,s],[5,11,6]]],
        [[[1,7,6],[5,11,10,4,3,9,8,2,t,s]]],
        [[[1,7,6,11,10,9,8,2,3,4,5],[s,t]]],
        [[[1,s],[6,7,8,9,10,11,5,4,3,2,t]]],
        [[[1,7,8,2,3,9,10,4,5,11,6],[s,t]]],
        [[[5,11,10,4,3,9,8,2,t],[6,7,1,s]]],
        [[[5,4,3,9,10,11,6],[s,1,7,8,2,t]]],
    ]


def vec(es, chosen):
    return tuple(int(e in chosen) for e in es)


def local_basis(k, xe):
    n, j = k-1, k-3
    h = lambda i: edge(12+i, 13+i)
    g = lambda i: edge(12+k+i, 12+k+(i+1) % k)
    r = lambda i: edge(12+i, 12+k+i)
    p, q = 14+2*k, 15+2*k
    z = (p, q)
    alpha, beta = edge(12+j, p), edge(12+n-1, q)
    missing = {}
    for a in list(range(1, j))+[n-1]:
        missing["6r"+str(a)] = {r(i) for i in range(1, n+1) if i not in (a, a+1)} | {h(a),g(a),z}
    missing.update({
        "1a": {h(i) for i in range(2, n, 2)} | {g(i) for i in range(1, j+1, 2)} | {g(n)},
        "1b": {r(i) for i in range(2, n+1)} | {g(0)},
        "4a": {h(i) for i in range(1, j, 2)} | {alpha,r(n-1),r(n),g(0)}
              | {g(i) for i in range(2, j, 2)},
        "4b": {r(i) for i in range(1, j)} | {alpha,h(n-1),g(n),g(j)},
        "7Z": {h(i) for i in range(1, j, 2)} | {alpha,beta,g(0)}
              | {g(i) for i in range(2, n, 2)},
        "7r1": {r(i) for i in range(3, n)} | {h(1),g(1),g(n),z},
    })
    rows = {name: vec(xe, set(xe)-es) for name, es in missing.items()}
    dirs = [minus(rows["6r"+str(a)], rows["6r"+str(n-1)]) for a in range(1, j)]
    dirs += [minus(rows[a], rows[b]) for a, b in (("1a","1b"),("4a","4b"),("7Z","7r1"))]
    cols = [h(i) for i in range(1, j)] + [h(n-1),z,g(0)]
    minor = [[row[xe.index(e)] for e in cols] for row in dirs]
    # Independently derive all entries by parity, not a rank-selected minor.
    expected = [[-int(i == a) for i in range(1, j)]+[1,0,0] for a in range(1, j)]
    expected += [
        [-int(i % 2 == 0) for i in range(1, j)]+[-1,0,1],
        [-int(i % 2 == 1) for i in range(1, j)]+[1,0,-1],
        [-int(i % 2 == 1 and i != 1) for i in range(1, j)]+[0,1,-1]]
    assert minor == expected
    assert det(minor) == 4-k and rank(dirs) == k-1
    return rows, minor


def main():
    finite = json.loads((BASE/"finite-attempt-01.json").read_bytes())["certificates"]
    uniform = json.loads((BASE/"uniform-attempt-02.json").read_bytes())["checks"]
    lookup = {c["k"]: c for c in finite}
    checks = []
    witness_count = 0
    fixed_minor = None
    for k in (4,6,8,10,12):
        X, Y, xe, ye, cut, es = model(k)
        c = lookup.get(k)
        u = next((a for a in uniform if a["k"] == k), None)
        states = c["states"] if c else u["states"]
        if c:
            assert c["graph"]["edges"] == [list(e) for e in es]
            assert c["xe"] == list(map(list, xe)) and c["ye"] == list(map(list, ye))
        genuine = {vec(es, a) for a in cycles(es, X | Y) if cut[2] in a or (1,7) in a}
        WX, WY, anchors, products = [], [], [], set()
        def lift(x, y, J):
            return vec(es, {e for e, a in zip(xe, x) if a}
                       | {e for e, a in zip(ye, y) if a} | {cut[i] for i in J})
        for state in states:
            local_pairs = tuple((cut[a][1],cut[b][1]) for a,b in state["px"])
            outside_pairs = tuple((cut[a][0],cut[b][0]) for a,b in state["py"])
            xx = sorted(packings(tuple(xe), tuple(sorted(X)), local_pairs))
            yy = sorted(y for y in packings(tuple(ye), tuple(sorted(Y)), outside_pairs)
                        if 2 in state["J"] or y[0])
            assert xx == list(map(tuple, state["X"])) and yy == list(map(tuple, state["Y"]))
            anchor = lift(xx[0], yy[0], state["J"])
            assert anchor == tuple(state["anchor"])
            anchors.append(anchor)
            WX.extend(minus(lift(x, yy[0], state["J"]), anchor) for x in xx[1:])
            WY.extend(minus(lift(xx[0], y, state["J"]), anchor) for y in yy[1:])
            products |= {lift(x, y, state["J"]) for x, y in product(xx, yy)}
        assert products == genuine
        A = differences(anchors)
        image_coords = [es.index(e) for e in ye+cut]
        image = rank([[r[i] for i in image_coords] for r in WY+A])
        local, full = rank(WX), rank(WX+WY+A)
        assert full == rank(differences(sorted(genuine))) == k+8 and image == 9
        assert local == (1 if k == 4 else k-1)
        details = dict(k=k, survivors=len(genuine), local=local, image=image,
                       total=full, extra_anchor_kernel=full-image-local)
        if u:
            rows, minor = local_basis(k, xe)
            assert minor == u["local_minor"]
            for w in u["local_witnesses"]:
                word = w["path_words"]
                flat = sum(word, [])
                assert len(flat) == len(set(flat)) and set(flat) == X
                chosen = edges_of(word)
                assert chosen <= set(xe) and set(xe)-chosen == set(map(tuple, w["missing"]))
                state = states[w["state"]]
                xp = [e[1] for e in cut]
                assert sorted(sorted((xp.index(a[0]),xp.index(a[-1]))) for a in word) == state["px"]
                row = vec(xe, chosen)
                assert list(row) in state["X"]
                if w["name"] in rows:
                    assert row == rows[w["name"]]
                assert lift(row, state["Y"][0], state["J"]) in genuine
                witness_count += 1
            y_rows = []
            for i, family in enumerate(exterior(k)):
                rr = []
                for words in family:
                    flat = sum(words, [])
                    assert len(flat) == len(set(flat)) and set(flat) == Y
                    chosen = edges_of(words)
                    assert chosen <= set(ye)
                    rr.append(vec(ye, chosen))
                # The proof lists sufficient partners, not every exterior packing.
                # Complete state families were independently checked above.
                assert rr == list(map(tuple, states[i]["Y"][:len(rr)]))
                y_rows.append(rr)
            projected = [tuple(ys[0])+tuple(int(j in states[i]["J"]) for j in range(5))
                         for i, ys in enumerate(y_rows)]
            dirs = [minus(y_rows[1][1],y_rows[1][0])+(0,)*5,
                    minus(y_rows[4][1],y_rows[4][0])+(0,)*5,
                    minus(y_rows[4][2],y_rows[4][0])+(0,)*5]
            dirs += [minus(projected[i], projected[0]) for i in (1,2,3,4,5,7)]
            assert dirs == list(map(tuple, u["image_directions"]))
            cols = [0,1,2,3,5,7,9,10,16]
            im = [[r[i] for i in cols] for r in dirs]
            assert det(im) == 1 and rank(dirs) == 9
            if fixed_minor is None:
                fixed_minor = im
            assert im == fixed_minor == u["image_minor"]
            for a in u["anchors"]:
                assert tuple(a["cycle"]) in genuine
                assert tuple(a["cycle"][es.index(e)] for e in ye+cut) == projected[a["state"]]
            details.update(local_minor_det=str(det(minor)), image_minor_det="1")
        checks.append(details)
    result = dict(status="PASS", finite_checks=checks, local_words_checked=witness_count,
                  fixed_image_minor=fixed_minor,
                  uniform_proof="Parent reviewed interval coverage, endpoint gluing, parity-derived Schur block and ambient upper bounds; see disposition.",
                  method="Parent-only DFS and exact Fraction ranks; exhaustive packing products; independently reconstructed graph and minors",
                  helper=str(HELPER.relative_to(ROOT)), helper_sha256=hashlib.sha256(HELPER.read_bytes()).hexdigest(),
                  limits="Only k=4,6,8,10,12 computed. Infinite claim follows the written proof, not finite tests. No brace or uniform counting claim.")
    with (BASE.parent/"i176-parent-certificates.json").open("x") as out:
        json.dump(result, out, indent=2, sort_keys=True)
        out.write("\n")
    print("PASS: five exhaustive parent products, actual path words, local and image minors", witness_count)


if __name__ == "__main__":
    main()
