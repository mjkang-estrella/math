#!/usr/bin/env python3
"""Read-only provenance and exact-diagnostic checks; not an H2 decision procedure."""
from fractions import Fraction
from hashlib import sha1, sha256
from itertools import permutations, product
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parent
PIN = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"
INTERFACE = "b2f6064d2710b3a994a38525a8a4a54a5297bd44c20c5dfb053bfea75bfe2809"


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def check_provenance():
    manifest = json.loads((ROOT / "manifest.json").read_text())
    actual = {p.name for p in ROOT.iterdir() if p.is_file() and p.name != "manifest.json"}
    assert actual == set(manifest["files"])
    for name, expected in manifest["files"].items():
        assert digest(ROOT / name) == expected, name
    receipts = json.loads((ROOT / "source-receipts.json").read_text())
    assert receipts["pin"] == PIN
    tree = json.loads((ROOT / "private/context/sources/preprints-tree.json").read_text())
    assert tree["truncated"] is False
    blobs = {entry["path"]: entry["sha"] for entry in tree["tree"] if entry["type"] == "blob"}
    for entry in receipts["context"] + receipts["sources"]:
        data = (ROOT / entry["path"]).read_bytes()
        assert len(data) == entry["bytes"]
        assert sha256(data).hexdigest() == entry["sha256"], entry["path"]
        if "git_blob" in entry:
            blob = sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
            assert blob == entry["git_blob"] == blobs[entry["upstream_path"]]
            assert entry["url"] == f"https://raw.githubusercontent.com/openai/math/{PIN}/{entry['upstream_path']}"
            assert entry["read_scope"] == "complete text"
            assert len(data.splitlines()) == entry["lines"]
    assert digest(ROOT / "private/context/hyperstar-interface.md") == INTERFACE


def add(a, b):
    return [x + y for x, y in zip(a, b)]


def mul(a, b):
    out = [0] * 10
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            if x and y:
                assert i + j < 10
                out[i + j] += x * y
    return out


def check_spectral_diagnostics():
    # Coefficients in increasing powers, so this is a polynomial identity check.
    pm1 = [-1, 1] + [0] * 8
    omin_m1 = [-1, 1, 0, 1, 0, 0, 0, 0, 1, 0]
    qp1 = [1, 0, 0, 0, 1] + [0] * 5
    gap = add(mul(pm1, omin_m1), [-x for x in mul(qp1, qp1)])
    assert gap == [0, -2, 1, -1, -1, 0, 0, 0, -2, 1]
    assert sum(c * 3**i for i, c in enumerate(gap)) == 6456
    assert Fraction(2 * (3**8 + 3**3 + 3 - 1), (3**4 + 1)**2) == Fraction(3295, 1681)
    # Exact small matrices check all three eigenspaces, with no floating point.
    for p in (3, 5, 7):
        for blocks in (1, 2, 3):
            n = p * blocks
            K = [[p - 1 - int(a // p == c // p and a != c) for c in range(n)] for a in range(n)]
            apply = lambda x: [sum(a * b for a, b in zip(row, x)) for row in K]
            assert apply([1] * n) == [(p - 1) * (n - 1)] * n
            for block in range(blocks):
                for j in range(1, p):
                    x = [0] * n
                    x[block * p], x[block * p + j] = 1, -1
                    assert apply(x) == x
            for block in range(1, blocks):
                x = [int(i // p == 0) - int(i // p == block) for i in range(n)]
                assert apply(x) == [-(p - 1) * v for v in x]
    for p in range(3, 102):
        # The proof applies to every integer p>=3; primality is not needed here.
        numerator = (p - 1) * (p**8 + p**3 + p - 1)
        denominator = (p**4 + 1)**2
        assert numerator > 2 * p**8 > denominator


def check_star_diagnostics():
    for n in (2, 3):
        perms = list(permutations(range(n)))
        outcomes = list(product(perms, repeat=3))
        for endpoints in ((0, 0, 0), (0, 1, 0)):
            pair = full = completed = 0
            for maps in outcomes:
                z0 = maps[0][endpoints[0]]
                if z0 == maps[1][endpoints[1]]:
                    pair += 1
                    completed += sum(maps[2][x] == z0 for x in range(n))
                    full += int(maps[2][endpoints[2]] == z0)
            assert Fraction(pair, len(outcomes)) == Fraction(1, n)
            assert Fraction(full, len(outcomes)) == Fraction(1, n**2)
            assert completed == pair  # Unspecified arm adds no probability cost.


if __name__ == "__main__":
    check_provenance()
    check_spectral_diagnostics()
    check_star_diagnostics()
    print("PASS: provenance, exact spectral diagnostics, and star probabilities")
    print("H2 remains unresolved; no matching existence claim is verified.")
    print("manifest_sha256=" + digest(ROOT / "manifest.json"))
