#!/usr/bin/env python3
"""Copied positive and reason-checked negative controls for verify.py.

Copies this review directory and the frozen author packet into a fresh
/var/tmp work directory, mutates only the copies, and writes one transcript
per case into ./controls/ (exempt from the manifest by exact name).
Usage: run-controls.py --manifest-sha256 H (author anchors are read from
input-binding.json; they are the externally supplied parent anchors).
"""
import argparse
import json
import os
import shutil
import subprocess
import sys
import tempfile
from pathlib import Path

HERE = Path(__file__).absolute().parent
AUTHOR_NAME = "fresh-analytic-discovery-r74"
ZERO = "0" * 64


def run(script, args):
    p = subprocess.run([sys.executable, str(script)] + args, capture_output=True, text=True)
    return p.returncode, p.stdout, p.stderr


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--manifest-sha256", required=True)
    m = ap.parse_args().manifest_sha256
    anchors = json.loads((HERE / "input-binding.json").read_text())["external_anchors_supplied_by_parent"]
    base = ["--manifest-sha256", m,
            "--author-manifest-sha256", anchors["manifest.json"],
            "--author-proof-sha256", anchors["candidate-proof.md"],
            "--author-scope-sha256", anchors["scope-status.json"],
            "--author-completion-sha256", anchors["author-completion.json"]]

    def swap(flag, value):
        out = list(base)
        out[out.index(flag) + 1] = value
        return out

    cases = [
        ("positive", None, base, None),
        ("wrong-review-manifest", None, swap("--manifest-sha256", ZERO), "external review manifest anchor mismatch"),
        ("wrong-author-manifest", None, swap("--author-manifest-sha256", ZERO), "author manifest anchor differs"),
        ("wrong-author-proof", None, swap("--author-proof-sha256", ZERO), "author proof anchor differs"),
        ("changed-review-file", lambda r, a: (r / "review.md").write_text((r / "review.md").read_text() + "x"), base, "review byte mismatch"),
        ("missing-review-file", lambda r, a: (r / "reading-limits.md").unlink(), base, "review file membership mismatch"),
        ("extra-review-file", lambda r, a: (r / "extra.txt").write_text("x"), base, "review file membership mismatch"),
        ("extra-review-directory", lambda r, a: (r / "extra-dir").mkdir(), base, "review directory membership mismatch"),
        ("symlink-entry", lambda r, a: (r / "link.md").symlink_to("review.md"), base, "symlink entry"),
        ("hardlink-entry", lambda r, a: os.link(r / "review.md", r / "hard.md"), base, "hardlink entry"),
        ("fifo-entry", lambda r, a: os.mkfifo(r / "pipe"), base, "nonregular entry"),
        ("changed-author-file", lambda r, a: (a / "dependency-map.md").write_text((a / "dependency-map.md").read_text() + "x"), base, "author byte mismatch"),
        ("root-symlink", "ROOTLINK", base, "symlink root ancestry"),
    ]
    work = Path(tempfile.mkdtemp(prefix="t212m-contrib-controls-", dir="/var/tmp"))
    outdir = HERE / "controls"
    outdir.mkdir(exist_ok=True)
    summary = []
    for name, mutate, args, reason in cases:
        case = work / name
        case.mkdir()
        r = case / HERE.name
        a = case / AUTHOR_NAME
        shutil.copytree(HERE, r, symlinks=True,
                        ignore=lambda d, names: names if Path(d) == outdir else [])
        shutil.copytree(HERE.parent / AUTHOR_NAME, a, symlinks=True)
        script = r / "verify.py"
        if mutate == "ROOTLINK":
            link = case / "linked-review"
            link.symlink_to(r, target_is_directory=True)
            script = link / "verify.py"
        elif mutate is not None:
            mutate(r, a)
        code, out, err = run(script, args)
        if reason is None:
            ok = code == 0 and "IDENTITY_PASS_ONLY" in out
        else:
            ok = code != 0 and reason in err
        summary.append({"case": name, "accepted": code == 0, "expected_reason": reason, "control_ok": ok})
        (outdir / (name + ".txt")).write_text(json.dumps(
            {"case": name, "returncode": code, "stdout": out, "stderr": err,
             "expected_reason": reason, "control_ok": ok}, indent=1) + "\n")
    print(json.dumps({"work_directory": str(work), "all_ok": all(s["control_ok"] for s in summary),
                      "results": summary}, indent=1))
    sys.exit(0 if all(s["control_ok"] for s in summary) else 1)


if __name__ == "__main__":
    main()
