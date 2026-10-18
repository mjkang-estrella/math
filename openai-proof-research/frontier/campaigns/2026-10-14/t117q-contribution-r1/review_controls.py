#!/usr/bin/env python3
"""Positive and mutation controls for verify_review.py, run only on copies.

  review_controls.py PACKAGE --anchor H --scratch DIR

PACKAGE must already be sealed with external anchor H. DIR must be an empty or new
directory outside PACKAGE; every case works on its own copy (private/ is not copied).
Prints a JSON result. Exit 0 only if every case gives its expected outcome.
"""
import argparse
import json
import os
import shutil
import subprocess
import sys

VERIFIER = "verify_review.py"


def copy_package(src, dst):
    shutil.copytree(src, dst, symlinks=True, ignore=shutil.ignore_patterns("private", "__pycache__"))


def run(tool, root, anchor):
    args = [sys.executable, tool, "verify", root]
    if anchor is not None:
        args += ["--anchor", anchor]
    p = subprocess.run(args, capture_output=True, text=True)
    return p.returncode, p.stdout.strip() or p.stderr.strip()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("package")
    ap.add_argument("--anchor", required=True)
    ap.add_argument("--scratch", required=True)
    a = ap.parse_args()
    pkg = os.path.realpath(a.package)
    scratch = os.path.realpath(a.scratch)
    if scratch == pkg or scratch.startswith(pkg + os.sep):
        sys.exit("refusing: scratch must be outside the package")
    os.makedirs(scratch, exist_ok=True)
    if os.listdir(scratch):
        sys.exit("refusing: scratch must be empty")

    tooldir = os.path.join(scratch, "tool")
    os.mkdir(tooldir)
    tool = os.path.join(tooldir, VERIFIER)
    shutil.copy2(os.path.join(pkg, VERIFIER), tool)

    wrong = "0" * 64
    anchor = a.anchor

    def edit(path, old, new):
        with open(path, encoding="utf-8") as f:
            s = f.read()
        if old not in s:
            raise SystemExit(f"control setup failed: {old!r} not in {path}")
        with open(path, "w", encoding="utf-8") as f:
            f.write(s.replace(old, new, 1))

    def reseal(root):
        out = subprocess.run([sys.executable, tool, "seal", root], capture_output=True, text=True, check=True)
        return out.stdout.strip()

    cases = []

    def case(name, expect, mutate=None, use_anchor=None, root_override=None):
        root = os.path.join(scratch, name)
        copy_package(pkg, root)
        target = root
        info = mutate(root) if mutate else None
        if root_override:
            target = root_override(root)
        anc = anchor if use_anchor is None else use_anchor
        if anc == "INFO":
            anc = info
        rc, msg = run(tool, target, None if anc == "NONE" else anc)
        ok = (rc == 0) if expect == "accept" else (rc != 0 and expect in msg)
        cases.append({"case": name, "expected": expect, "rc": rc, "actual": msg, "ok": ok})

    case("positive_copy", "accept")
    case("wrong_anchor", "external manifest anchor mismatch", use_anchor=wrong)
    case("missing_anchor", "external anchor missing or malformed", use_anchor="NONE")
    case("changed_payload", "payload mismatch: review.md",
         lambda r: edit(os.path.join(r, "review.md"), "Role:", "Role (edited):"))
    case("changed_verdict", "payload mismatch: review.md",
         lambda r: edit(os.path.join(r, "review.md"), "**SUBSTANTIAL**", "**TECHNICAL**"))
    case("missing_payload", "exact file inventory mismatch",
         lambda r: os.remove(os.path.join(r, "replay-record.json")))
    case("extra_file", "exact file inventory mismatch",
         lambda r: open(os.path.join(r, "extra.txt"), "w").close())
    case("extra_empty_directory", "exact directory inventory mismatch",
         lambda r: os.mkdir(os.path.join(r, "extra-dir")))

    def root_symlink(r):
        link = r + "-link"
        os.symlink(r, link)
        return link
    case("root_symlink", "symlink or nonregular node: .", root_override=root_symlink)

    def payload_symlink(r):
        p = os.path.join(r, "review.md")
        real = os.path.join(scratch, "payload-symlink-target.md")
        shutil.move(p, real)
        os.symlink(real, p)
    case("payload_symlink", "symlink or nonregular node: review.md", payload_symlink)

    case("payload_hardlink", "hardlinked regular file: review.md",
         lambda r: os.link(os.path.join(r, "review.md"), os.path.join(scratch, "hardlink-outside.md")))
    case("fifo", "symlink or nonregular node: fifo", lambda r: os.mkfifo(os.path.join(r, "fifo")))

    def nested(r):
        os.mkdir(os.path.join(r, "sub"))
        shutil.copy2(os.path.join(r, "MANIFEST.json"), os.path.join(r, "sub", "MANIFEST.json"))
    case("nested_manifest", "nested manifest: sub/MANIFEST.json", nested)

    def private_symlink(r):
        os.symlink(scratch, os.path.join(r, "private"))
    case("private_symlink", "symlink or nonregular node: private", private_symlink)

    def resealed(r):
        edit(os.path.join(r, "review.md"), "**SUBSTANTIAL**", "**TECHNICAL**")
        return reseal(r)
    case("self_resealed_wrong_external_anchor", "external manifest anchor mismatch", resealed)
    # Documents that only the external anchor defeats a consistent reseal.
    case("self_resealed_own_anchor_accepts", "accept", resealed, use_anchor="INFO")

    status = "PASS" if all(c["ok"] for c in cases) else "FAIL"
    print(json.dumps({
        "status": status,
        "package_manifest_sha256": anchor,
        "python": sys.version.split()[0],
        "cases": cases,
        "scope": "Membership/integrity controls on copies only. No mathematical claims.",
    }, indent=2))
    return 0 if status == "PASS" else 1


if __name__ == "__main__":
    sys.exit(main())
