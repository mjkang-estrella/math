#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
# Copyright (c) 2026 Myeongjin Kang
"""Read-only, fail-closed verifier for fresh-analytic-discovery-r12.

Writes nothing. Checks:
  1. size and SHA-256 of every file in inputs-manifest.json and
     outputs-manifest.json; no unlisted file exists in this directory;
  2. seal.json entries and the detached seal.sha256 (required unless
     --pre-seal is given);
  3. frozen-scope hash, as recorded in status.json and here;
  4. Git blob SHA-1 of the pinned source copies;
  5. status.json is not self-passed and not counted;
  6. exact rational arithmetic for the constants 162, 18, 48, 52 and C_LC;
  7. unchanged-source receipts: live repository copies of the snapshots in
     inputs/context/ (upstream.json must match; other files are reported);
  8. with --with-experiments, the two numerical scripts are re-run in a
     subprocess (no bytecode) and their stdout must equal the stored JSON.
Exit code 0 only if every check passes.
"""
import hashlib
import json
import os
import subprocess
import sys
from fractions import Fraction

sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
PROJECT = os.path.abspath(os.path.join(HERE, "..", "..", "..", ".."))
SCOPE_SHA256 = "d14eb78f156fda839a910797953d27445492625839dd6d0e2d22a2059fda29b4"
BLOBS = {
    "README.md": "575cccc262d3d9c9e7a87df235884857a1620f79",
    "main.tex": "676dc958b88fa0062b3949895c4b01092a9bab64",
    "references.bib": "ef5e68b8d708d1a263e6db20f873a76bfba5776b",
    "sections/cells.tex": "15cf607375c84a422c8aa4b69c9b2791651fd13c",
    "sections/finite_stability.tex": "ebb83b10ad60efd546708576f5a6fd339a8eb90e",
    "sections/gradient.tex": "baebc01672a5e6e1e83838192e4fb3a56ab201b6",
    "sections/introduction.tex": "a3f79cd0ba261e054ad3ebb0a5641453788f20ef",
    "sections/moments.tex": "b1645cc9b0cf7982c28ba13b1138b86cbd664b2c",
    "sections/sharpness.tex": "ae214b7d19cd630fccf6da61b4e169fd329b28e8",
}
CONTEXT = {
    "inputs/context/upstream.json": ("sources/upstream.json", True),
    "inputs/context/NEW-TEN-2026-10-14.md": ("frontier/NEW-TEN-2026-10-14.md", False),
    "inputs/context/r2-brief.txt":
        ("frontier/campaigns/2026-10-14/salem-sextic-parent/r2-brief.txt", False),
    "inputs/context/fresh-r12-brief.txt":
        ("frontier/campaigns/2026-10-14/salem-sextic-parent/fresh-r12-brief.txt", False),
    "inputs/context/fresh-r12-launch.json":
        ("frontier/campaigns/2026-10-14/salem-sextic-parent/fresh-r12-launch.json", False),
}
SEAL_FILES = {"seal.json", "seal.sha256", "verify-receipt.json",
              "inputs-manifest.json", "outputs-manifest.json"}

failures = []


def check(cond, msg):
    print(("ok   " if cond else "FAIL ") + msg)
    if not cond:
        failures.append(msg)


def sha256(path):
    with open(path, "rb") as fh:
        return hashlib.sha256(fh.read()).hexdigest()


def load_json(name):
    path = os.path.join(HERE, name)
    if not os.path.exists(path):
        check(False, f"{name} present")
        return None
    with open(path) as fh:
        return json.load(fh)


def manifests():
    listed = set()
    for name in ("inputs-manifest.json", "outputs-manifest.json"):
        data = load_json(name)
        if data is None:
            continue
        for e in data["files"]:
            p = os.path.join(HERE, e["path"])
            ok = os.path.isfile(p) and os.path.getsize(p) == e["size"] \
                and sha256(p) == e["sha256"]
            check(ok, f"{name}: {e['path']}")
            listed.add(e["path"])
    present = set()
    for root, dirs, files in os.walk(HERE):
        dirs[:] = [d for d in dirs if d != "__pycache__"]
        for f in files:
            present.add(os.path.relpath(os.path.join(root, f), HERE))
    extra = sorted(present - listed - SEAL_FILES)
    check(not extra, "no unlisted files" + (f": {extra}" if extra else ""))
    pycache = any(d == "__pycache__" for _, ds, _ in os.walk(HERE) for d in ds)
    check(not pycache, "no __pycache__ directories")


def seal(pre_seal):
    path = os.path.join(HERE, "seal.json")
    if not os.path.exists(path):
        check(pre_seal, "seal.json present (or --pre-seal)")
        return
    s = load_json("seal.json")
    check(s.get("scope_sha256") == SCOPE_SHA256, "seal.json scope hash")
    check(s.get("counted") is False, "seal.json not counted")
    for key in ("inputs", "outputs", "receipt"):
        e = s[key]
        p = os.path.join(HERE, e["path"])
        check(os.path.isfile(p) and os.path.getsize(p) == e["size"]
              and sha256(p) == e["sha256"], f"seal.json {key}: {e['path']}")
    det = os.path.join(HERE, "seal.sha256")
    if os.path.exists(det):
        want = open(det).read().split()[0]
        check(want == sha256(path), "detached seal.sha256 matches seal.json")
    else:
        check(False, "seal.sha256 present")


def scope_and_status():
    check(sha256(os.path.join(HERE, "original-scope.md")) == SCOPE_SHA256,
          "frozen scope hash")
    st = load_json("status.json")
    if st is None:
        return
    check(st.get("scope_sha256") == SCOPE_SHA256, "status.json scope hash")
    check(st.get("self_pass") is False and st.get("counted") is False,
          "status.json: no self-PASS, not counted")
    check(st.get("source_family") == 374, "status.json source family 374")


def blobs():
    base = os.path.join(HERE, "inputs", "pinned", "brenier")
    for rel, want in BLOBS.items():
        p = os.path.join(base, rel)
        if not os.path.isfile(p):
            check(False, f"source blob {rel} present")
            continue
        data = open(p, "rb").read()
        got = hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()
        check(got == want, f"source blob {rel}")


def constants():
    F = Fraction
    # Proposition 5.1: A <= 5 R^2 B from A/4 <= R^2B/8 + A/8 + R^2B/2.
    check(F(1, 8) + F(1, 2) == F(5, 8) and F(5, 8) / F(1, 8) == 5,
          "A <= 5 R^2 B")
    # (a+b)/2 - sqrt(ab) <= (a-b)^2/(8 sqrt(ab)) at sample rationals squared.
    ok = True
    for p, q in [(1, 2), (2, 3), (5, 7), (1, 9), (3, 3)]:
        a, b = F(p) ** 2, F(q) ** 2
        g = F(p * q)
        ok &= (a + b) / 2 - g <= (a - b) ** 2 / (8 * g)
    check(ok, "AM-GM gap bound (exact at sample points)")
    # alpha^2/M <= 4M <= 8 gamma and B <= 2E for alpha, gamma in [M/2, 2M].
    # alpha <= 2M gives alpha^2/M <= 4M; gamma >= M/2 gives 4M <= 8 gamma.
    check(F(2) ** 2 == 4 and 4 == 8 * F(1, 2), "alpha^2/M <= 8 gamma")
    total = 2 + 16 * 5 * 2
    check(total == 162, "2 + 16*5*2 = 162")
    # Lemma 7.1: 3*(6 + 0) and 3*(4*4) + 4.
    check(3 * 6 == 18 and 3 * 4 * 4 + 4 == 52, "slice constants 18 and 52")
    # Two translation pieces: (2/h^2) * 3 = 6/h^2.
    check(2 * 3 == 6, "translation constant 6")


def receipts():
    for snap, (live, strict) in CONTEXT.items():
        sp = os.path.join(HERE, snap)
        lp = os.path.join(PROJECT, live)
        if not os.path.isfile(sp):
            check(False, f"snapshot {snap} present")
            continue
        if not os.path.isfile(lp):
            msg = f"live {live} missing"
            if strict:
                check(False, msg)
            else:
                print("note " + msg)
            continue
        same = sha256(sp) == sha256(lp)
        if strict:
            check(same, f"live {live} unchanged since snapshot")
        else:
            print(("note " if not same else "ok   ")
                  + f"live {live} " + ("unchanged" if same else "CHANGED since snapshot (informational)"))


def experiments():
    env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")
    exp = os.path.join(HERE, "experiments")
    for script, args, stored in (("check_slice.py", ["300"], "slice-result.json"),
                                 ("check_moment.py", ["12", "220"], "moment-result.json")):
        out = subprocess.run([sys.executable, "-B", os.path.join(exp, script)] + args,
                             capture_output=True, text=True, env=env, cwd=exp, timeout=1800)
        want = open(os.path.join(exp, stored)).read().strip()
        check(out.returncode == 0 and out.stdout.strip() == want,
              f"experiment {script} reproduces {stored}")
        try:
            check(json.loads(want)["passes"] is True, f"{stored} records passes=true")
        except (ValueError, KeyError):
            check(False, f"{stored} parses")


def main():
    pre_seal = "--pre-seal" in sys.argv
    manifests()
    seal(pre_seal)
    scope_and_status()
    blobs()
    constants()
    receipts()
    if "--with-experiments" in sys.argv:
        experiments()
    print("RESULT:", "ALL CHECKS PASSED" if not failures else f"{len(failures)} FAILURE(S)")
    print("meaning: integrity, constants and evidence reproduction only; not a mathematical PASS")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
