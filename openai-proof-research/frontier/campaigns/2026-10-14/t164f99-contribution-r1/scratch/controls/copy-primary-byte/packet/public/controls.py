#!/usr/bin/env python3
"""Copied-controls for the T164F99 contribution-r1 verifier.

Builds scratch/controls/copy-clean (a full copy of packet/, FINAL.json,
FINAL.sha256, REPORT.md, REPORT.sha256) inside this review root, verifies the
clean copy (expect accept), then for each mutation case builds a fresh copy,
flips exactly one byte or adds one file, and verifies (expect reject). The
verifier's read-only behaviour on each copy is checked by hashing the copy
tree before and after each run. Writes artifact-controls.json at the root.
"""
import hashlib, json, os, shutil, subprocess, sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(os.path.dirname(HERE))
CTRL = os.path.join(ROOT, "scratch", "controls")
TOP = ["FINAL.json", "FINAL.sha256", "REPORT.md", "REPORT.sha256"]

def tree_hash(path):
    h = hashlib.sha256()
    for dirpath, dirnames, filenames in os.walk(path):
        dirnames[:] = sorted(d for d in dirnames if d != "__pycache__")
        for fn in sorted(filenames):
            full = os.path.join(dirpath, fn)
            rel = os.path.relpath(full, path)
            h.update(rel.encode())
            with open(full, "rb") as f:
                h.update(f.read())
    return h.hexdigest()

def make_copy(name):
    dst = os.path.join(CTRL, name)
    if os.path.exists(dst):
        shutil.rmtree(dst)
    os.makedirs(dst)
    shutil.copytree(os.path.join(ROOT, "packet"), os.path.join(dst, "packet"))
    for f in TOP:
        shutil.copy2(os.path.join(ROOT, f), os.path.join(dst, f))
    return dst

def flip_byte(path):
    with open(path, "r+b") as f:
        b = bytearray(f.read(1))
        b[0] ^= 0x01
        f.seek(0)
        f.write(bytes(b))

def run_verify(target):
    return subprocess.run([sys.executable, os.path.join(HERE, "verify.py"), "--root", target],
                          capture_output=True, text=True)

CASES = {
    "clean": None,
    "review-byte": "packet/public/review.md",
    "final-byte": "FINAL.json",
    "manifest-byte": "packet/MANIFEST.json",
    "report-byte": "REPORT.md",
    "author-copy-byte": "packet/private/author/proof.md",
    "primary-byte": "packet/private/primary/2307.08901v6.txt",
}

def main():
    os.makedirs(CTRL, exist_ok=True)
    results = {}
    for name, mutation in CASES.items():
        dst = make_copy("copy-" + name)
        if mutation == "extra-packet-file":
            pass
        elif mutation:
            flip_byte(os.path.join(dst, mutation))
        before = tree_hash(dst)
        proc = run_verify(dst)
        after = tree_hash(dst)
        expect = 0 if name == "clean" else 1
        results[name] = {
            "expected_accept": name == "clean",
            "returncode": proc.returncode,
            "as_expected": proc.returncode == expect,
            "copy_unchanged_by_verifier": before == after,
            "stdout_head": proc.stdout.strip().splitlines()[:2],
        }
    # extra-file case
    dst = make_copy("copy-extra-packet-file")
    with open(os.path.join(dst, "packet", "public", "extra.txt"), "w") as f:
        f.write("extra\n")
    before = tree_hash(dst)
    proc = run_verify(dst)
    results["extra-packet-file"] = {
        "expected_accept": False,
        "returncode": proc.returncode,
        "as_expected": proc.returncode == 1,
        "copy_unchanged_by_verifier": before == tree_hash(dst),
        "stdout_head": proc.stdout.strip().splitlines()[:2],
    }
    out = {
        "all_as_expected": all(r["as_expected"] and r["copy_unchanged_by_verifier"] for r in results.values()),
        "cases": results,
    }
    with open(os.path.join(ROOT, "artifact-controls.json"), "w") as f:
        json.dump(out, f, indent=1, sort_keys=True)
    print("CONTROLS", "PASS" if out["all_as_expected"] else "FAIL")
    return 0 if out["all_as_expected"] else 1

if __name__ == "__main__":
    sys.exit(main())
