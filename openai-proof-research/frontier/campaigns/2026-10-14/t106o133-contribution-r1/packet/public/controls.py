#!/usr/bin/env python3
"""Copied controls for verify.py.

Usage:
  python -B controls.py --root REVIEW_ROOT --project PROJECT \
      --finalhash DETACHED_FINAL_SHA256 --author-finalhash DETACHED_AUTHOR_FINAL_SHA256

Every mutation is applied to copies under REVIEW_ROOT/.controls-tmp/, which is
removed afterwards. Originals (this review's packet, the author root and parent
inputs) are only read. The receipt REVIEW_ROOT/artifact-controls.json lies
outside the packet and is not bound by FINAL.
"""
import argparse
import hashlib
import importlib.util
import json
import os
import shutil
import subprocess
import sys
import time

sys.dont_write_bytecode = True

CAMPAIGN = "frontier/campaigns/2026-10-14"
HERE = os.path.dirname(os.path.abspath(__file__))


def snapshot(root, skip=()):
    out = {}
    for r, dirs, files in os.walk(root):
        dirs[:] = sorted(d for d in dirs if os.path.join(r, d) not in skip)
        for f in sorted(files):
            p = os.path.join(r, f)
            if p in skip:
                continue
            st = os.stat(p)
            with open(p, "rb") as fh:
                out[os.path.relpath(p, root)] = (st.st_size, st.st_mtime_ns,
                                                 hashlib.sha256(fh.read()).hexdigest())
    return out


def flip_byte(path):
    with open(path, "rb") as fh:
        b = bytearray(fh.read())
    b[len(b) // 2] ^= 0x01
    with open(path, "wb") as fh:
        fh.write(bytes(b))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", required=True)
    ap.add_argument("--project", required=True)
    ap.add_argument("--finalhash", required=True)
    ap.add_argument("--author-finalhash", required=True)
    a = ap.parse_args()
    root = os.path.abspath(a.root)
    project = os.path.abspath(a.project)
    author_root = os.path.join(project, CAMPAIGN, "fresh-structural-discovery-r133")
    parent_dir = os.path.join(project, CAMPAIGN, "discovery-structural-r133-parent")
    verify = os.path.join(HERE, "verify.py")
    tmp = os.path.join(root, ".controls-tmp")
    receipt_path = os.path.join(root, "artifact-controls.json")
    if os.path.exists(tmp):
        raise SystemExit(f"{tmp} already exists; refusing to reuse it")

    spec = importlib.util.spec_from_file_location("seal", os.path.join(HERE, "seal.py"))
    seal = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(seal)

    def run(rroot, finalhash, author_hash, aroot=None, pdir=None, extra=None):
        cmd = [sys.executable, "-B", verify, "--root", rroot, "--project", project]
        if finalhash is not None:
            cmd += ["--finalhash", finalhash]
        if author_hash is not None:
            cmd += ["--author-finalhash", author_hash]
        if aroot:
            cmd += ["--author-root", aroot]
        if pdir:
            cmd += ["--parent-dir", pdir]
        cmd += extra or []
        p = subprocess.run(cmd, capture_output=True, text=True)
        fails = [ln for ln in p.stdout.splitlines() if ln.startswith("FAIL ")]
        return p.returncode, fails, p.stderr.strip().splitlines()[-1:] if p.returncode == 2 else []

    results = []

    def record(name, expect_pass, rc, fails, err):
        ok = (rc == 0) if expect_pass else (rc != 0)
        results.append({"control": name, "expect": "PASS" if expect_pass else "FAIL",
                        "exit_code": rc, "failed_checks": [f[5:] for f in fails][:6],
                        "error": err, "ok": ok})

    protected = {"review_root": (root, {receipt_path, tmp}), "author_root": (author_root, set())}
    before = {k: snapshot(p, s) for k, (p, s) in protected.items()}
    parent_inputs = ["review-context-r1.txt", "contribution-r1-brief.txt"]
    parent_before = {f: hashlib.sha256(open(os.path.join(parent_dir, f), "rb").read()).hexdigest()
                     for f in parent_inputs}

    record("C00 originals, detached anchors", True, *run(root, a.finalhash, a.author_finalhash))

    def fresh():
        if os.path.exists(tmp):
            shutil.rmtree(tmp)
        os.makedirs(tmp)
        rv = os.path.join(tmp, "review")
        os.makedirs(rv)
        shutil.copytree(os.path.join(root, "packet"), os.path.join(rv, "packet"))
        for f in ("REPORT.md", "FINAL.json"):
            shutil.copy2(os.path.join(root, f), os.path.join(rv, f))
        au = os.path.join(tmp, "author")
        shutil.copytree(author_root, au)
        pa = os.path.join(tmp, "parent")
        os.makedirs(pa)
        for f in parent_inputs:
            shutil.copy2(os.path.join(parent_dir, f), os.path.join(pa, f))
        return rv, au, pa

    try:
        rv, au, pa = fresh()
        record("C01 copies, unmodified", True, *run(rv, a.finalhash, a.author_finalhash, au, pa))
        record("C02 wrong detached FINAL hash", False, *run(rv, "0" * 64, a.author_finalhash, au, pa))
        record("C03 missing --finalhash", False, *run(rv, None, a.author_finalhash, au, pa))
        record("C04 wrong detached author FINAL hash", False, *run(rv, a.finalhash, "0" * 64, au, pa))

        flip_byte(os.path.join(rv, "packet/public/review.md"))
        record("C05 review.md byte flip", False, *run(rv, a.finalhash, a.author_finalhash, au, pa))
        rv, au, pa = fresh()
        with open(os.path.join(rv, "packet/public/extra.txt"), "w") as fh:
            fh.write("x\n")
        record("C06 unlisted file in packet", False, *run(rv, a.finalhash, a.author_finalhash, au, pa))
        rv, au, pa = fresh()
        os.remove(os.path.join(rv, "packet/public/rights.md"))
        record("C07 listed file deleted", False, *run(rv, a.finalhash, a.author_finalhash, au, pa))
        rv, au, pa = fresh()
        with open(os.path.join(rv, "REPORT.md"), "a") as fh:
            fh.write("\nedit\n")
        record("C08 outside REPORT edited", False, *run(rv, a.finalhash, a.author_finalhash, au, pa))
        rv, au, pa = fresh()
        vpath = os.path.join(rv, "packet/public/verdict.json")
        v = json.load(open(vpath))
        v["verdict"] = "SUBSTANTIAL"
        json.dump(v, open(vpath, "w"), indent=1)
        seal.write_manifest(rv)
        new_final = seal.write_final(rv, a.author_finalhash)
        record("C09 verdict changed and fully resealed (new anchor supplied)", False,
               *run(rv, new_final, a.author_finalhash, au, pa))
        rv, au, pa = fresh()
        src = os.path.join(rv, "packet/private/source/preprints/Hardness-of-finding-large-independent-sets-in-three-colorable-graphs-September-24-2026/build/source/sections/lists.tex")
        flip_byte(src)
        seal.write_manifest(rv)
        new_final = seal.write_final(rv, a.author_finalhash)
        record("C10 pinned source byte flip, resealed (blob check only)", False,
               *run(rv, new_final, a.author_finalhash, au, pa))
        rv, au, pa = fresh()
        flip_byte(os.path.join(au, "packet/public/proof.md"))
        record("C11 author proof.md byte flip (copy)", False, *run(rv, a.finalhash, a.author_finalhash, au, pa))
        rv, au, pa = fresh()
        with open(os.path.join(au, "scratch/added.txt"), "w") as fh:
            fh.write("x\n")
        record("C12 file added to author root (copy)", False, *run(rv, a.finalhash, a.author_finalhash, au, pa))
        rv, au, pa = fresh()
        with open(os.path.join(pa, "contribution-r1-brief.txt"), "a") as fh:
            fh.write(" ")
        record("C13 parent brief edited (copy)", False, *run(rv, a.finalhash, a.author_finalhash, au, pa))
        rv, au, pa = fresh()
        record("C14 copies, unmodified (repeat)", True, *run(rv, a.finalhash, a.author_finalhash, au, pa))
    finally:
        if os.path.exists(tmp):
            shutil.rmtree(tmp)

    after = {k: snapshot(p, s) for k, (p, s) in protected.items()}
    parent_after = {f: hashlib.sha256(open(os.path.join(parent_dir, f), "rb").read()).hexdigest()
                    for f in parent_inputs}
    preservation = {
        "review_root_unchanged_by_controls": before["review_root"] == after["review_root"],
        "author_root_unchanged_by_controls": before["author_root"] == after["author_root"],
        "parent_inputs_unchanged_by_controls": parent_before == parent_after,
        "tmp_removed": not os.path.exists(tmp),
    }
    all_ok = all(r["ok"] for r in results) and all(preservation.values())
    receipt = {
        "run_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
        "finalhash": a.finalhash,
        "author_finalhash": a.author_finalhash,
        "controls": results,
        "preservation": preservation,
        "all_ok": all_ok,
        "note": "Artifact controls only; not a correctness or contribution judgment. Not bound by FINAL.",
    }
    with open(receipt_path, "w") as fh:
        json.dump(receipt, fh, indent=1)
        fh.write("\n")
    for r in results:
        print(("ok   " if r["ok"] else "BAD  ") + r["control"] + f"  (exit {r['exit_code']})")
    for k, val in preservation.items():
        print(("ok   " if val else "BAD  ") + k)
    print("CONTROLS " + ("PASS" if all_ok else "FAIL"))
    sys.exit(0 if all_ok else 1)


if __name__ == "__main__":
    main()
