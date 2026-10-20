#!/usr/bin/env python3
# MIT License. Author: Myeongjin Kang. Copied integrity controls for the r133 root.
# Each case copies the root (without the temporary directory) into <root>/.controls-tmp/<case>, applies one
# mutation, runs verify.py against the original detached anchors, and compares the outcome with the expectation.
# The temporary directory is removed at the end. Artifact checks only; not a mathematical gate.
import argparse
import json
import os
import shutil
import subprocess
import sys

sys.dont_write_bytecode = True
TMP = ".controls-tmp"


def copy_root(root, dst):
    shutil.copytree(root, dst, symlinks=True, ignore=shutil.ignore_patterns(TMP))


def flip(path):
    with open(path, "rb") as f:
        data = bytearray(f.read())
    data[len(data) // 2] ^= 1
    os.chmod(path, 0o644)
    with open(path, "wb") as f:
        f.write(bytes(data))


CASES = [
    ("intact", True, None),
    ("intact-math", True, "math"),
    ("flip-proof", False, ("flip", "packet/public/proof.md")),
    ("flip-frozen-theorem", False, ("flip", "packet/public/FROZEN-THEOREM.md")),
    ("flip-certificate", False, ("flip", "packet/public/certificate.py")),
    ("flip-private-upstream", False, ("flip", "packet/private/upstream/preprints/A-product-counterexample-to-the-simplex-maximum-for-projection-body-volume-September-24-2026/build/main.tex")),
    ("flip-notes", False, ("flip", "work/notes.md")),
    ("flip-manifest", False, ("flip", "packet/MANIFEST.json")),
    ("flip-final", False, ("flip", "FINAL.json")),
    ("flip-report", False, ("flip", "REPORT.md")),
    ("extra-file", False, ("extra", "packet/public/extra.txt")),
    ("extra-dir", False, ("mkdir", "packet/public/newdir")),
    ("delete-file", False, ("delete", "scratch/bs.py")),
    ("symlink", False, ("symlink", "packet/public/link")),
]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", required=True)
    ap.add_argument("--manifest-sha256", required=True)
    ap.add_argument("--final-sha256", required=True)
    ap.add_argument("--report-sha256", required=True)
    ap.add_argument("--out", required=True)
    a = ap.parse_args()
    root = os.path.abspath(a.root)
    tmp = os.path.join(root, TMP)
    if os.path.exists(tmp):
        print("temporary directory already exists; refusing")
        return 2
    os.mkdir(tmp)
    verifier = os.path.join(root, "packet/public/verify.py")
    results = []
    try:
        for name, expect_pass, op in CASES:
            dst = os.path.join(tmp, name)
            copy_root(root, dst)
            extra_args = []
            if op == "math":
                extra_args = ["--math"]
            elif op is not None:
                kind, rel = op
                p = os.path.join(dst, rel)
                if kind == "flip":
                    flip(p)
                elif kind == "extra":
                    with open(p, "w") as f:
                        f.write("x\n")
                elif kind == "mkdir":
                    os.mkdir(p)
                elif kind == "delete":
                    os.chmod(os.path.dirname(p), 0o755)
                    os.remove(p)
                elif kind == "symlink":
                    os.symlink("proof.md", p)
            r = subprocess.run([sys.executable, "-B", verifier, "--root", dst,
                                "--manifest-sha256", a.manifest_sha256, "--final-sha256", a.final_sha256,
                                "--report-sha256", a.report_sha256] + extra_args,
                               capture_output=True, text=True)
            passed = r.returncode == 0
            first = (r.stdout.strip().splitlines() or [""])[0]
            results.append({"case": name, "expect_pass": expect_pass, "exit": r.returncode,
                            "first_line": first, "as_expected": passed == expect_pass})
            shutil.rmtree(dst, onerror=lambda f, p, e: (os.chmod(p, 0o755), f(p)))
    finally:
        for d, ds, fs in os.walk(tmp):
            os.chmod(d, 0o755)
            for fn in fs:
                fp = os.path.join(d, fn)
                if not os.path.islink(fp):
                    os.chmod(fp, 0o644)
        shutil.rmtree(tmp)
    out = {"cases": len(results), "all_as_expected": all(r["as_expected"] for r in results), "results": results}
    with open(a.out, "w") as f:
        json.dump(out, f, indent=1)
        f.write("\n")
    print("CONTROLS", "ALL AS EXPECTED" if out["all_as_expected"] else "UNEXPECTED", len(results))
    return 0 if out["all_as_expected"] else 1


if __name__ == "__main__":
    sys.exit(main())
