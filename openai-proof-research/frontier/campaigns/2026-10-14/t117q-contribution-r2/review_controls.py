#!/usr/bin/env python3
"""Positive, wrong-anchor and copied mutation controls for the r2 review package.

Run: review_controls.py --anchor <external SHA256 of MANIFEST.json> [--source DIR]
All mutations happen on copies under /var/tmp; the source directory is only read and
is first authenticated against the anchor. Identity controls only.
"""
import argparse
import hashlib
import json
import os
import shutil
import subprocess
import sys
import tempfile

HERE = os.path.dirname(os.path.abspath(__file__))


def run(verifier, root, anchor):
    r = subprocess.run([sys.executable, "-B", verifier, "verify", root, "--anchor", anchor],
                       capture_output=True, text=True)
    return r.returncode, r.stdout + r.stderr


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--anchor", required=True)
    ap.add_argument("--source", default=HERE)
    a = ap.parse_args()
    src = os.path.abspath(a.source)
    rc, out = run(os.path.join(src, "verify_review.py"), src, a.anchor)
    if rc != 0:
        raise SystemExit(f"source does not authenticate: {out}")
    cases = [
        ("positive", "PASS_IDENTITY_ONLY"),
        ("wrong-anchor", "external manifest anchor mismatch"),
        ("malformed-anchor", "external anchor missing or malformed"),
        ("changed-review", "payload mismatch: review.md"),
        ("changed-private", "payload mismatch: private/"),
        ("missing-limits", "exact file inventory mismatch"),
        ("extra-file", "exact file inventory mismatch"),
        ("extra-directory", "exact directory inventory mismatch"),
        ("payload-symlink", "symlink or nonregular node: review.md"),
        ("payload-hardlink", "hardlinked regular file: review.md"),
        ("fifo", "symlink or nonregular node: review.md"),
        ("nested-manifest", "nested manifest: private/MANIFEST.json"),
        ("root-symlink", "symlink root or ancestor"),
        ("ancestor-symlink", "symlink root or ancestor"),
        ("self-reseal", "external manifest anchor mismatch"),
        ("manifest-removed", "manifest missing"),
    ]
    results = []
    with tempfile.TemporaryDirectory(prefix="t117q-contrib-r2-controls-", dir="/var/tmp") as tmp:
        for case, reason in cases:
            base = os.path.join(tmp, case)
            os.mkdir(base)
            dest = os.path.join(base, "pkg")
            shutil.copytree(src, dest, symlinks=True)
            verifier = os.path.join(dest, "verify_review.py")
            vcopy = os.path.join(base, "verify_review.py")
            shutil.copy2(verifier, vcopy)
            anchor = a.anchor
            target = dest
            review = os.path.join(dest, "review.md")
            if case == "wrong-anchor":
                anchor = "f" * 64
            elif case == "malformed-anchor":
                anchor = "not-a-hash"
            elif case == "changed-review":
                with open(review, "ab") as f:
                    f.write(b"\nmutation\n")
            elif case == "changed-private":
                p = os.path.join(dest, "private")
                name = sorted(os.listdir(p))[0]
                with open(os.path.join(p, name), "ab") as f:
                    f.write(b"x")
            elif case == "missing-limits":
                os.unlink(os.path.join(dest, "reading-and-search-limits.md"))
            elif case == "extra-file":
                with open(os.path.join(dest, "extra.txt"), "w") as f:
                    f.write("extra")
            elif case == "extra-directory":
                os.mkdir(os.path.join(dest, "extra-dir"))
            elif case == "payload-symlink":
                os.unlink(review)
                os.symlink("reading-and-search-limits.md", review)
            elif case == "payload-hardlink":
                os.link(review, os.path.join(base, "review-link"))
            elif case == "fifo":
                os.unlink(review)
                os.mkfifo(review)
            elif case == "nested-manifest":
                with open(os.path.join(dest, "private", "MANIFEST.json"), "w") as f:
                    f.write("{}")
            elif case == "root-symlink":
                target = os.path.join(base, "alias")
                os.symlink(dest, target, target_is_directory=True)
            elif case == "ancestor-symlink":
                os.symlink(base, os.path.join(tmp, case + "-alias"), target_is_directory=True)
                target = os.path.join(tmp, case + "-alias", "pkg")
            elif case == "self-reseal":
                with open(review, "ab") as f:
                    f.write(b"\nmutation\n")
                subprocess.run([sys.executable, "-B", vcopy, "seal", dest],
                               check=True, capture_output=True)
            elif case == "manifest-removed":
                os.unlink(os.path.join(dest, "MANIFEST.json"))
            # Use the out-of-tree verifier copy so payload mutations cannot alter the checker.
            rc, out = run(vcopy, target, anchor)
            accepted = rc == 0
            if accepted != (case == "positive") or reason not in out:
                raise SystemExit(f"control failed: {case} rc={rc} out={out!r}")
            results.append({"case": case, "accepted": accepted, "returncode": rc,
                            "reason_checked": reason})
    print(json.dumps({"identity_only": True,
                      "anchor": a.anchor,
                      "verifier_sha256": hashlib.sha256(open(os.path.join(src, "verify_review.py"), "rb").read()).hexdigest(),
                      "scratch": "/var/tmp (deleted after run)",
                      "results": results}, indent=2))


if __name__ == "__main__":
    main()
