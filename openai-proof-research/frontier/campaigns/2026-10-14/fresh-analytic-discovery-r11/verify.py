#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Myeongjin Kang
"""Read-only verifier for fresh-analytic-discovery-r11.

Writes nothing. Checks:
  1. size and SHA-256 of every file in inputs-manifest.json and
     outputs-manifest.json, and of the files named in seal.json;
  2. frozen-scope hash;
  3. Git blob SHA-1 of the private source copies against the recorded values;
  4. exact algebra for beta_6 (irreducible trace cubic, root intervals);
  5. Corollary S' constants for beta_6 (q, Q, R, C_sep, C_{beta,Q}(1/2), kappa);
  6. deterministic re-run of the greedy product chain (evidence) against
     evidence/greedy_chain_raw.json.
Usage: python3 -B verify.py [--with-search]  (--with-search also re-runs the
seeded local search, about 25 s).
"""
import hashlib
import io
import json
import math
import os
import sys
from contextlib import redirect_stdout, redirect_stderr
from fractions import Fraction

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
SCOPE_SHA256 = "143778fc32d5eb1f668b4b941ad1bd184b19c71b1bfb2792bee78b1effdd2bdd"
BLOBS = {
    "README.md": "fd1abc787eea89c1aa3a469c5a05cf1c7e939f34",
    "build/main.tex": "1fce7aad27ddf5f83680fb28a43f393d51756a55",
    "build/salem.tex": "68552edd50043c1bde3e54a891d3ef65a41c9b6e",
    "build/nonpisot.tex": "859f16285b1c270cfcc31336842044c48bd7ded5",
    "build/classification.tex": "3abdd297813b3a2fd67c305468c0bc0e12fa59b6",
    "build/certificate.tex": "8630d0578a57a2e2a3900e5ed6d4aa45221caa10",
    "build/references.bib": "7222408828aec34147ab55ed77c7bb079e8581db",
    "verification/verify_degree31.py": "8663aeacac2d9eadf2d0fe74f0bf125e27f50a68",
}

failures = []


def check(cond, msg):
    print(("ok   " if cond else "FAIL ") + msg)
    if not cond:
        failures.append(msg)


def sha256(path):
    with open(path, "rb") as fh:
        return hashlib.sha256(fh.read()).hexdigest()


def manifests():
    for name in ("inputs-manifest.json", "outputs-manifest.json"):
        path = os.path.join(HERE, name)
        if not os.path.exists(path):
            check(False, f"{name} present")
            continue
        entries = json.load(open(path))["files"]
        for e in entries:
            p = os.path.join(HERE, e["path"])
            ok = os.path.exists(p) and os.path.getsize(p) == e["size"] \
                and sha256(p) == e["sha256"]
            check(ok, f"{name}: {e['path']}")
    seal = os.path.join(HERE, "seal.json")
    if os.path.exists(seal):
        s = json.load(open(seal))
        for key in ("inputs", "outputs", "receipt"):
            e = s[key]
            p = os.path.join(HERE, e["path"])
            check(os.path.exists(p) and os.path.getsize(p) == e["size"]
                  and sha256(p) == e["sha256"], f"seal.json {key}: {e['path']}")


def scope():
    check(sha256(os.path.join(HERE, "original-scope.md")) == SCOPE_SHA256,
          "frozen scope hash")


def blobs():
    base = os.path.join(HERE, "inputs", "private", "source-153")
    for rel, want in BLOBS.items():
        p = os.path.join(base, rel)
        if not os.path.exists(p):
            check(False, f"source blob {rel} present")
            continue
        data = open(p, "rb").read()
        got = hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()
        check(got == want, f"source blob {rel}")


def algebra():
    def T(y):
        return y ** 3 - 4 * y - 1
    signs = [(Fraction(x), T(Fraction(x))) for x in (-2, -1, 0, 2, 3)]
    check(all(T(Fraction(r)) != 0 for r in (1, -1)), "y^3-4y-1 has no rational root")
    check(signs[0][1] < 0 < signs[1][1] and signs[2][1] < 0 and signs[3][1] < 0 < signs[4][1],
          "trace cubic roots in (-2,-1), (-1,0), (2,3)")
    # P6(x) = x^3 T(x + 1/x) as an exact polynomial identity at 7 points.
    ok = True
    for x in range(2, 9):
        x = Fraction(x)
        ok &= x ** 6 - x ** 4 - x ** 3 - x ** 2 + 1 == x ** 3 * T(x + 1 / x)
    check(ok, "P6(x) = x^3 T(x + 1/x)")


def constants():
    sys.path.insert(0, os.path.join(HERE, "scripts"))
    from salem_numerics import Salem
    S = Salem([1, 0, -4, -1], "P6")
    b = S.beta
    check(abs(b - 1.40126836794) < 1e-10, f"beta_6 = {b:.12f}")
    q = 1
    while b ** q <= 2:
        q += 1
    Q = b ** q
    R = b / (b - 1)
    Csep = 1 + (1 + 2 * R) / (2 * (b - 1))
    a = 0.5
    cQ = (Q - 2) / (Q - 1)
    D = 2 * a / (math.pi * cQ * (1 - (1 + a) / Q))
    B = a * Q / ((1 - a) * (Q - 1))
    C = math.log((2 * R + 2 + D) * Csep) + B
    print(f"     q={q} Q={Q:.4f} R={R:.4f} C_sep={Csep:.3f} D={D:.3f} B={B:.3f} C={C:.3f}")
    check(q == 3 and abs(C - 6.33) < 0.01, "C_{beta_6,Q}(1/2) about 6.33 with q = 3")
    angs = [s * t for t in S.thetas for s in (1, -1)]
    diffs = [x - y for x in angs for y in angs if x != y]
    kappa = max(1 / abs(math.sin(d / 2)) for d in diffs)
    print(f"     kappa = {kappa:.4f}")
    check(math.isfinite(kappa), "kappa finite (distinct circle conjugates)")


def greedy():
    from salem_numerics import Salem, greedy_chain
    stored = json.load(open(os.path.join(HERE, "evidence", "greedy_chain_raw.json")))
    for key, poly in (("quartic_P1", [1, -1, -3]), ("sextic_P6", [1, 0, -4, -1])):
        S = Salem(poly, key)
        chain = greedy_chain(S, 6, 400)
        old = stored[key]["chain"]
        same = len(chain) == len(old) and all(
            c["ks"] == o["ks"] and abs(c["Lambda"] - o["Lambda"]) < 1e-6 * max(1, o["Lambda"])
            for c, o in zip(chain, old))
        check(same, f"greedy chain evidence reproduces ({key})")


def search():
    import seed_search
    buf, err = io.StringIO(), io.StringIO()
    with redirect_stdout(buf), redirect_stderr(err):
        seed_search.main()
    new = json.loads(buf.getvalue())
    old = json.load(open(os.path.join(HERE, "evidence", "seed_search_raw.json")))
    same = [abs(n["L_minus_Lambda"] - o["L_minus_Lambda"]) < 1e-9 for n, o in zip(new, old)]
    check(len(new) == len(old) and all(same), "seeded search evidence reproduces")
    check(max(o["L_minus_Lambda"] for o in old) < 0, "no searched seed has L > Lambda")


def main():
    manifests()
    scope()
    blobs()
    algebra()
    constants()
    greedy()
    if "--with-search" in sys.argv:
        search()
    print("RESULT:", "ALL CHECKS PASSED" if not failures else f"{len(failures)} FAILURE(S)")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
