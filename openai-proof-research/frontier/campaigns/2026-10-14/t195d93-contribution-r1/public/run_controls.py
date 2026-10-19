#!/usr/bin/env python3
"""Disposable-copy integrity controls for verify.py. Artifact checks only, never mathematical gates.

All copies live under scratch/ inside this review directory and are removed afterwards.
The original review payloads and every external file named in public/reading.json are
snapshotted (path, bytes, sha256, mode, link count) before and after; CONTROLS.json records
the outcome outside the sealed manifest.

Usage: run_controls.py --final-sha256 HEX
"""
import argparse
import hashlib
import json
import os
import shutil
import stat
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
REPO = os.path.abspath(os.path.join(ROOT, "..", "..", "..", ".."))
SKIP = {"scratch", "CONTROLS.json"}


def sha256(path):
    with open(path, "rb") as f:
        return hashlib.sha256(f.read()).hexdigest()


def snap_entry(p):
    st = os.lstat(p)
    return [st.st_size, sha256(p), stat.S_IMODE(st.st_mode), st.st_nlink]


def externals():
    with open(os.path.join(ROOT, "public", "reading.json")) as f:
        r = json.load(f)
    paths = set(r["detached_author_anchors"]) | {b["path"] for b in r["bodies"]}
    paths |= {r["preprints_tree"]["path"], r["pinned_source"]["path"]}
    return sorted(paths)


def snapshot():
    snap = {}
    for dirpath, dirnames, filenames in os.walk(ROOT):
        if os.path.relpath(dirpath, ROOT) == ".":
            dirnames[:] = [d for d in dirnames if d not in SKIP]
            filenames = [n for n in filenames if n not in SKIP]
        for n in filenames:
            p = os.path.join(dirpath, n)
            snap["review/" + os.path.relpath(p, ROOT)] = snap_entry(p)
    for rel in externals():
        snap["repo/" + rel] = snap_entry(os.path.join(REPO, rel))
    return snap


def copy_review(dst):
    shutil.copytree(ROOT, dst, symlinks=True, ignore=lambda d, names: [n for n in names if d == ROOT and n in SKIP])


def copy_repo_subset(dst):
    for rel in externals():
        target = os.path.join(dst, rel)
        os.makedirs(os.path.dirname(target), exist_ok=True)
        shutil.copy2(os.path.join(REPO, rel), target)


def flip(path):
    with open(path, "r+b") as f:
        b = f.read(1)
        f.seek(0)
        f.write(bytes([b[0] ^ 1]))


def run(copy_root, final, repo):
    cmd = [sys.executable, "-I", "-B", os.path.join(copy_root, "public", "verify.py"),
           "--final-sha256", final, "--root", copy_root, "--repo", repo]
    p = subprocess.run(cmd, capture_output=True, text=True)
    return p.returncode, p.stdout.strip()


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--final-sha256", required=True)
    final = ap.parse_args().final_sha256
    before = snapshot()
    base = os.path.join(ROOT, "scratch", "controls")
    if os.path.exists(base):
        raise SystemExit("scratch/controls already exists; refusing to reuse it")
    os.makedirs(base)
    wrong = "0" * 64

    def m_review(c): flip(os.path.join(c, "REVIEW.md"))
    def m_private(c): flip(os.path.join(c, "private", "primary", "miyazaki.txt"))
    def m_extra(c): open(os.path.join(c, "public", "extra.txt"), "w").write("x")
    def m_missing(c): os.remove(os.path.join(c, "private", "primary", "miyazaki.txt"))
    def m_symlink(c): os.symlink("reading.json", os.path.join(c, "public", "link.json"))
    def m_mode(c):
        p = os.path.join(c, "public", "reading.json")
        os.chmod(p, stat.S_IMODE(os.lstat(p).st_mode) ^ 0o040)
    def m_hardlink(c): os.link(os.path.join(c, "REVIEW.md"), os.path.join(os.path.dirname(c), "hardlink-REVIEW.md"))
    def m_manifest(c):
        p = os.path.join(c, "MANIFEST.json")
        d = json.load(open(p))
        d["files"].pop("private/primary/miyazaki.txt")
        open(p, "w").write(json.dumps(d))

    cases = [
        ("baseline", None, final, False, True),
        ("wrong-detached-final", None, wrong, False, False),
        ("review-byte-flip", m_review, final, False, False),
        ("private-body-byte-flip", m_private, final, False, False),
        ("extra-payload", m_extra, final, False, False),
        ("missing-payload", m_missing, final, False, False),
        ("symlink-payload", m_symlink, final, False, False),
        ("mode-change", m_mode, final, False, False),
        ("extra-hard-link", m_hardlink, final, False, False),
        ("manifest-edit", m_manifest, final, False, False),
        ("external-subset-baseline", None, final, "clean", True),
        ("external-author-proof-flip", None, final, "proof", False),
        ("external-pinned-source-flip", None, final, "source", False),
    ]
    results = []
    for i, (name, mut, fin, ext, expect_ok) in enumerate(cases):
        case_dir = os.path.join(base, "%02d" % i)
        copy_root = os.path.join(case_dir, "review")
        os.makedirs(case_dir)
        copy_review(copy_root)
        repo = REPO
        if ext:
            repo = os.path.join(case_dir, "repo")
            copy_repo_subset(repo)
            if ext == "proof":
                flip(os.path.join(repo, "frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r93/packet/public/proof.md"))
            if ext == "source":
                with open(os.path.join(ROOT, "public", "reading.json")) as f:
                    flip(os.path.join(repo, json.load(f)["pinned_source"]["path"]))
        if mut:
            mut(copy_root)
        rc, out = run(copy_root, fin, repo)
        ok = rc == 0
        results.append({"case": name, "expected_ok": expect_ok, "observed_ok": ok,
                        "as_expected": ok == expect_ok, "returncode": rc, "output": out})
    shutil.rmtree(os.path.join(ROOT, "scratch"))
    after = snapshot()
    receipt = {
        "schema": "t195d93-contribution-r1-controls-v1",
        "mathematical_gate": False,
        "final_sha256_tested": final,
        "all_as_expected": all(r["as_expected"] for r in results),
        "originals_unchanged": before == after,
        "snapshot_entries": len(before),
        "cases": results,
        "limits": "Copies are disposable; the verifier audit hook is not proven against hostile runtimes and no explicit denial probes are included.",
    }
    with open(os.path.join(ROOT, "CONTROLS.json"), "w") as f:
        json.dump(receipt, f, indent=1, sort_keys=True)
        f.write("\n")
    print(json.dumps({k: receipt[k] for k in ("all_as_expected", "originals_unchanged", "snapshot_entries")}))
    sys.exit(0 if receipt["all_as_expected"] and receipt["originals_unchanged"] else 1)


if __name__ == "__main__":
    main()
