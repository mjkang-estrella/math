#!/usr/bin/env python3
"""Disposable-copy integrity controls for the T096N126 contribution review r1.

All mutations happen only in disposable copies under <root>/.controls-scratch,
which is removed afterwards. Originals (review directory and recorded inputs)
are hashed before and after and must be unchanged. Results go to stdout.
Artifact checks only; never a mathematical or contribution gate. Run with python -B.
"""
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys

SCRATCH = ".controls-scratch"
OUTSIDE_RESULTS = {"controls-result.json", "controls-result.sha256"}


def sha(path):
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for block in iter(lambda: fh.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


def tree_hash(root, skip_top=()):
    out = {}
    for dirpath, dirnames, filenames in os.walk(root):
        rel_dir = os.path.relpath(dirpath, root)
        if rel_dir == ".":
            dirnames[:] = [d for d in dirnames if d not in skip_top]
            filenames = [f for f in filenames if f not in skip_top]
        for fn in filenames:
            p = os.path.join(dirpath, fn)
            out[os.path.relpath(p, root).replace(os.sep, "/")] = sha(p)
    return out


def run_verify(verifier, root, project, final, report, skip_inputs=False):
    cmd = [sys.executable, "-B", verifier, "--root", root, "--project", project,
           "--expected-final", final, "--expected-report", report]
    if skip_inputs:
        cmd.append("--skip-inputs")
    r = subprocess.run(cmd, capture_output=True, text=True)
    try:
        status = json.loads(r.stdout)["status"]
    except Exception:
        status = "ERROR"
    return status, r.returncode


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=os.path.dirname(os.path.dirname(here)))
    ap.add_argument("--project", default=None)
    ap.add_argument("--expected-final", required=True)
    ap.add_argument("--expected-report", required=True)
    a = ap.parse_args()
    root = os.path.abspath(a.root)
    project = os.path.abspath(a.project) if a.project else os.path.abspath(
        os.path.join(root, "..", "..", "..", ".."))
    verifier = os.path.join(root, "packet", "public", "verify.py")
    with open(os.path.join(root, "packet", "public", "inputs.json"), encoding="utf-8") as fh:
        inputs = json.load(fh)["files"]
    skip = {SCRATCH} | OUTSIDE_RESULTS
    before_root = tree_hash(root, skip)
    before_inputs = {r: sha(os.path.join(project, r)) for r in inputs}
    scratch = os.path.join(root, SCRATCH)
    if os.path.exists(scratch):
        print(json.dumps({"status": "ERROR", "error": "scratch exists"}))
        return 2
    os.mkdir(scratch)
    results = []
    F, R = a.expected_final, a.expected_report

    def fresh(name):
        dst = os.path.join(scratch, name)
        shutil.copytree(root, dst, ignore=shutil.ignore_patterns(SCRATCH, *OUTSIDE_RESULTS))
        return dst

    def record(name, expect, status):
        results.append({"control": name, "expected": expect, "observed": status,
                        "ok": status == expect})

    try:
        record("baseline-original", "PASS", run_verify(verifier, root, project, F, R)[0])
        c = fresh("c01")
        record("baseline-copy", "PASS", run_verify(verifier, c, project, F, R)[0])
        c = fresh("c02")
        with open(os.path.join(c, "packet/public/review.md"), "ab") as fh:
            fh.write(b" ")
        record("tamper-review-byte", "FAIL", run_verify(verifier, c, project, F, R)[0])
        c = fresh("c03")
        os.remove(os.path.join(c, "packet/public/reading-limits.md"))
        record("delete-packet-file", "FAIL", run_verify(verifier, c, project, F, R)[0])
        c = fresh("c04")
        with open(os.path.join(c, "packet/public/extra.md"), "w") as fh:
            fh.write("x")
        record("add-unlisted-file", "FAIL", run_verify(verifier, c, project, F, R)[0])
        c = fresh("c05")
        os.rename(os.path.join(c, "packet/public/review.md"), os.path.join(c, "packet/public/Review.md"))
        record("rename-packet-file", "FAIL", run_verify(verifier, c, project, F, R)[0])
        c = fresh("c06")
        with open(os.path.join(c, "packet/MANIFEST.json"), "ab") as fh:
            fh.write(b"\n")
        record("tamper-manifest", "FAIL", run_verify(verifier, c, project, F, R)[0])
        c = fresh("c07")
        record("wrong-expected-final", "FAIL", run_verify(verifier, c, project, "0" * 64, R)[0])
        record("wrong-expected-report", "FAIL", run_verify(verifier, c, project, F, "0" * 64)[0])
        c = fresh("c08")
        with open(os.path.join(c, "REPORT.md"), "ab") as fh:
            fh.write(b" ")
        record("tamper-outside-report", "FAIL", run_verify(verifier, c, project, F, R)[0])
        c = fresh("c09")
        with open(os.path.join(c, "FINAL"), "w") as fh:
            fh.write("0" * 64 + "\n")
        record("tamper-detached-final", "FAIL", run_verify(verifier, c, project, F, R)[0])
        # Input mirrors: disposable copies of every recorded input.
        mirror = os.path.join(scratch, "mirror")
        for rel in inputs:
            dst = os.path.join(mirror, rel)
            os.makedirs(os.path.dirname(dst), exist_ok=True)
            shutil.copyfile(os.path.join(project, rel), dst)
        record("mirror-inputs-unchanged", "PASS", run_verify(verifier, root, mirror, F, R)[0])
        proof_rel = "frontier/campaigns/2026-10-14/fresh-analytic-discovery-r126/packet/public/proof.md"
        with open(os.path.join(mirror, proof_rel), "ab") as fh:
            fh.write(b" ")
        record("mirror-tamper-author-proof", "FAIL", run_verify(verifier, root, mirror, F, R)[0])
        shutil.copyfile(os.path.join(project, proof_rel), os.path.join(mirror, proof_rel))
        i38_rel = "frontier/iterations/i38-inequality-stability-discovery.md"
        os.remove(os.path.join(mirror, i38_rel))
        record("mirror-missing-inherited-input", "FAIL", run_verify(verifier, root, mirror, F, R)[0])
    finally:
        shutil.rmtree(scratch)
    after_root = tree_hash(root, skip)
    after_inputs = {r: sha(os.path.join(project, r)) for r in inputs}
    originals_ok = before_root == after_root and before_inputs == after_inputs
    all_ok = all(r["ok"] for r in results) and originals_ok
    print(json.dumps({
        "status": "PASS" if all_ok else "FAIL",
        "controls": results,
        "originals_unchanged": originals_ok,
        "review_files_hashed": len(before_root),
        "inputs_hashed": len(before_inputs),
        "scratch_removed": not os.path.exists(scratch),
        "note": "artifact integrity controls only; not a mathematical or contribution gate",
    }, indent=1))
    return 0 if all_ok else 1


if __name__ == "__main__":
    sys.exit(main())
