#!/usr/bin/env python3
# MIT License. Author: Myeongjin Kang. Read-only integrity verifier for the r133 root.
# Byte/inventory checks against detached anchors; optional reruns of the exact certificate and the float control.
# These are artifact checks, not mathematical gates.
import argparse
import hashlib
import json
import os
import subprocess
import sys

sys.dont_write_bytecode = True
UNSEALED = {"packet/MANIFEST.json", "FINAL.json", "REPORT.md", "CONTROL-RESULTS.json"}


def sha256(path):
    h = hashlib.sha256()
    with open(path, "rb") as f:
        for chunk in iter(lambda: f.read(1 << 16), b""):
            h.update(chunk)
    return h.hexdigest()


def inventory(root):
    files, dirs, links = set(), set(), []
    for d, ds, fs in os.walk(root, followlinks=False):
        rel = os.path.relpath(d, root).replace(os.sep, "/")
        if rel != ".":
            dirs.add(rel)
        for name in ds + fs:
            p = os.path.join(d, name)
            if os.path.islink(p):
                links.append(os.path.relpath(p, root))
        for name in fs:
            p = os.path.join(d, name)
            if os.path.isfile(p) and not os.path.islink(p):
                files.add(os.path.relpath(p, root).replace(os.sep, "/"))
    return files, dirs, links


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", required=True)
    ap.add_argument("--manifest-sha256", required=True)
    ap.add_argument("--final-sha256", required=True)
    ap.add_argument("--report-sha256", required=True)
    ap.add_argument("--project-root", help="also check that recorded external inputs are unchanged")
    ap.add_argument("--math", action="store_true", help="rerun certificate.py and geometry_control.py")
    a = ap.parse_args()
    root = os.path.abspath(a.root)
    errors = []
    anchors = (("packet/MANIFEST.json", a.manifest_sha256, "MANIFEST"),
               ("FINAL.json", a.final_sha256, "FINAL"),
               ("REPORT.md", a.report_sha256, "REPORT"))
    for rel, want, name in anchors:
        p = os.path.join(root, rel)
        if not os.path.isfile(p) or os.path.islink(p):
            errors.append(f"{name} missing")
        elif sha256(p) != want:
            errors.append(f"{name} sha256 mismatch")
    if errors:
        print("FAIL", errors)
        return 1
    manifest = json.load(open(os.path.join(root, "packet/MANIFEST.json")))
    final = json.load(open(os.path.join(root, "FINAL.json")))
    if final.get("manifest_sha256") != a.manifest_sha256:
        errors.append("FINAL does not bind MANIFEST")
    files, dirs, links = inventory(root)
    if links:
        errors.append(f"symlinks present: {links}")
    listed = set(manifest["files"])
    extra = sorted((files - UNSEALED) - listed)
    missing = sorted(listed - files)
    if extra:
        errors.append(f"unlisted files: {extra}")
    if missing:
        errors.append(f"missing files: {missing}")
    for rel in sorted(listed & files):
        rec = manifest["files"][rel]
        p = os.path.join(root, rel)
        if os.path.getsize(p) != rec["bytes"] or sha256(p) != rec["sha256"]:
            errors.append(f"content mismatch: {rel}")
    if set(manifest.get("directories", [])) != dirs:
        errors.append("directory set mismatch")
    frozen = os.path.join(root, "packet/public/FROZEN-THEOREM.md")
    if os.path.isfile(frozen) and sha256(frozen) != final.get("frozen_theorem_sha256"):
        errors.append("frozen theorem bytes differ from FINAL record")
    if a.project_root:
        for rel, want in final.get("external_inputs_sha256", {}).items():
            p = os.path.join(a.project_root, rel)
            if not os.path.isfile(p) or sha256(p) != want:
                errors.append(f"external input changed: {rel}")
    if a.math and not errors:
        env = dict(os.environ, PYTHONDONTWRITEBYTECODE="1")
        for script, token in (("certificate.py", "CERTIFICATE PASS"), ("geometry_control.py", "GEOMETRY CONTROL PASS")):
            r = subprocess.run([sys.executable, "-B", os.path.join(root, "packet/public", script)],
                               capture_output=True, text=True, env=env, cwd=os.path.join(root, "packet/public"))
            if r.returncode != 0 or token not in r.stdout:
                errors.append(f"{script} did not pass")
    if errors:
        print("FAIL")
        for e in errors:
            print(" -", e)
        return 1
    print(f"PASS files={len(listed)} directories={len(dirs)}" + (" math=PASS" if a.math else ""))
    return 0


if __name__ == "__main__":
    sys.exit(main())
