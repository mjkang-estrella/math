#!/usr/bin/env python3
"""Independent finite diagnostics; no candidate modules or output files imported.

Original review code: copyright 2026 Myeongjin Kang, MIT license.
Finite results do not prove the quantified theorem. Run with assertions enabled.
"""
from collections import Counter
from itertools import permutations, product
import json


def sign(p):
    return (-1) ** sum(p[i] > p[j] for i in range(len(p)) for j in range(i + 1, len(p)))


def act(word, g):
    # g maps old position to new position. This implements word o g^{-1}.
    result = [None] * len(word)
    for old, new in enumerate(g):
        result[new] = word[old]
    return tuple(result)


def compose(g, h):
    return tuple(g[h[i]] for i in range(len(g)))


def setup(m):
    cells = [(i, j) for i in range(1, m + 1) for j in range(1, m + 2 - i)]
    rows = [[k for k, (i, j) in enumerate(cells) if i == r] for r in range(1, m + 1)]
    cols = [[k for k, (i, j) in enumerate(cells) if j == c] for c in range(1, m + 1)]
    return cells, rows, cols


def polytabloid(cells, columns, row_word):
    # Actual column-position permutations of a tableau's row tabloid.
    result = Counter()
    for choices in product(*(list(permutations(col)) for col in columns)):
        g = list(range(len(cells)))
        for col, perm in zip(columns, choices):
            for old, new in zip(col, perm):
                g[old] = new
        result[act(row_word, g)] += sign(g)
    return +result if all(v > 0 for v in result.values()) else dict(result)


def alternating_blocks(n, blocks):
    result = {}
    for choices in product(*(list(permutations(range(1, len(b) + 1))) for b in blocks)):
        word = [None] * n
        s = 1
        for block, labels in zip(blocks, choices):
            s *= sign(labels)
            for position, label in zip(block, labels):
                word[position] = label
        result[tuple(word)] = s
    return result


def image(a, b, c, m, equality=True, shift=-1):
    if equality and a != c:
        return None
    word = tuple((x + y + shift, x) for x, y in zip(a, b))
    desired = {(r, x) for r in range(1, m + 1) for x in range(1, r + 1)}
    return word if len(set(word)) == len(word) and set(word) == desired else None


def project(layers, m, g=None, equality=True, shift=-1):
    if g is not None:
        layers = [{act(w, g): s for w, s in layer.items()} for layer in layers]
    output = Counter()
    survivors = 0
    for a, sa in layers[0].items():
        for b, sb in layers[1].items():
            for c, sc in layers[2].items():
                out = image(a, b, c, m, equality, shift)
                if out is not None:
                    survivors += 1
                    output[out] += sa * sb * sc
    return {w: s for w, s in output.items() if s}, survivors


def main():
    result = {"independent_of_candidate_scripts": True, "finite_only": True, "orbit_cases": []}
    for m in (1, 2, 3):
        cells, rows, cols = setup(m)
        vr = polytabloid(cells, rows, tuple(j for i, j in cells))
        vc = polytabloid(cells, cols, tuple(i for i, j in cells))
        assert vr == alternating_blocks(len(cells), rows)
        assert vc == alternating_blocks(len(cells), cols)
        transpose = tuple(cells.index((j, i)) for i, j in cells)
        assert {act(w, transpose): s for w, s in vr.items()} == vc
        w = tuple((m + 1 - i, m + 2 - i - j) for i, j in cells)
        cases = 0
        for g in permutations(range(len(cells))):
            out, survivors = project((vr, vr, vc), m, g)
            assert out == {act(w, g): 1}
            assert survivors == 1
            # Recover the actual group label from its output word.
            u = act(w, g)
            recovered = tuple(u.index(w[x]) for x in range(len(cells)))
            assert recovered == g
            cases += 1
        result["orbit_cases"].append({"m": m, "permutations": cases,
            "literal_triples_per_permutation": len(vr) ** 2 * len(vc),
            "one_retained_term_coefficient": 1,
            "tableau_and_block_expansions_equal": True,
            "transpose_scalar": 1})

    cells, rows, cols = setup(2)
    vr = alternating_blocks(len(cells), rows)
    vc = alternating_blocks(len(cells), cols)
    mutations = {}
    for name, layers, opts in [
        ("drop_equality", (vr, vr, vc), {"equality": False}),
        ("wrong_sum_shift", (vr, vr, vc), {"shift": 0}),
        ("third_layer_rows", (vr, vr, vr), {}),
        ("reverse_one_block_order", ({w: -s for w, s in vr.items()}, vr, vc), {}),
    ]:
        out, survivors = project(layers, 2, **opts)
        mutations[name] = {"retained_terms": survivors,
            "nonzero_words": len(out), "coefficients": sorted(out.values())}
    assert mutations["drop_equality"]["nonzero_words"] == 0
    assert mutations["wrong_sum_shift"]["nonzero_words"] == 0
    assert mutations["third_layer_rows"]["nonzero_words"] == 2
    assert mutations["reverse_one_block_order"]["coefficients"] == [-1]
    result["mutations"] = mutations

    tested = 0
    words = list(product(range(1, 3), repeat=3))
    for a, b, c in product(words, repeat=3):
        out = image(a, b, c, 2)
        for g in permutations(range(3)):
            translated = image(act(a, g), act(b, g), act(c, g), 2)
            assert translated == (None if out is None else act(out, g))
            tested += 1
    result["composite_map_equivariance_arbitrary_basis_cases"] = tested

    # Unfiltered content-projection equivariance, including repeated/outside letters.
    alphabet = [(r, a) for r in range(1, 4) for a in range(1, 3)]
    D = {(1, 1), (2, 1), (2, 2)}
    tested = 0
    for word in product(alphabet, repeat=3):
        kept = len(set(word)) == 3 and set(word) == D
        for g in permutations(range(3)):
            shifted = act(word, g)
            assert (len(set(shifted)) == 3 and set(shifted) == D) == kept
            tested += 1
    result["content_projection_equivariance_cases"] = tested
    result["status"] = "PASS"
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
