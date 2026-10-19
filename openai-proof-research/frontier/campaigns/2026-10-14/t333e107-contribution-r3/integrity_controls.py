#!/usr/bin/env python3
"""Positive and negative integrity controls for this review's verify.py.

Every mutation happens in a fresh scratch directory, `_scratch_controls/`,
created inside this review directory and removed when the run finishes. The
script never modifies the real bundle or any repository file. It reads the
real files, copies them into the scratch area, mutates only the copies, and
runs verify.py in a subprocess against those copies. It prints one JSON
receipt. The receipt tests the verifier's behaviour; it does not test
mathematics.

Usage: python3 -B integrity_controls.py --expected-manifest <SHA256> --repo-root <REPO>
"""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import subprocess
import sys

HERE = Path(__file__).resolve().parent
SCRATCH = HERE / "_scratch_controls"


def run(bundle, repo, digest):
    p = subprocess.run([sys.executable, "-B", str(HERE / "verify.py"),
                        "--expected-manifest", digest, "--repo-root", str(repo),
                        "--bundle-root", str(bundle)],
                       capture_output=True, text=True, timeout=300)
    msg = (p.stdout if p.returncode == 0 else p.stderr).strip()
    return p.returncode, msg


def copy_bundle(dst):
    # Copy exactly the sealed members, so files written after sealing (such as
    # this script's own receipt) cannot cause a spurious or masking rejection.
    dst.mkdir(parents=True)
    m = json.loads((HERE / "manifest.json").read_bytes())
    for name in [r["path"] for r in m["payloads"]] + m["envelope_exclusions"]:
        (dst / name).parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(HERE / name, dst / name)
    return dst


def mirror_repo(repo, dst):
    m = json.loads((HERE / "manifest.json").read_bytes())
    for a in m["external_anchors"]:
        t = dst / a["path"]
        t.parent.mkdir(parents=True, exist_ok=True)
        shutil.copy2(repo / a["path"], t)
    return dst


def reseal(bundle, mutate):
    m = json.loads((bundle / "manifest.json").read_bytes())
    mutate(m)
    mb = (json.dumps(m, indent=1, sort_keys=True) + "\n").encode()
    (bundle / "manifest.json").write_bytes(mb)
    h = hashlib.sha256(mb).hexdigest()
    (bundle / "seal.sha256").write_text(h + "  manifest.json\n")
    return h


def flip_byte(path):
    b = bytearray(path.read_bytes())
    b[len(b) // 2] ^= 0x01
    path.write_bytes(bytes(b))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--expected-manifest", required=True)
    ap.add_argument("--repo-root", type=Path, required=True)
    a = ap.parse_args()
    repo, d = a.repo_root.resolve(strict=True), a.expected_manifest
    if SCRATCH.exists():
        raise SystemExit("refusing to run: scratch directory already exists")
    SCRATCH.mkdir()
    results = []

    def control(name, expect_pass, bundle, repo_root, digest):
        rc, msg = run(bundle, repo_root, digest)
        results.append({"control": name, "expected": "pass" if expect_pass else "reject",
                        "observed": "pass" if rc == 0 else "reject",
                        "as_expected": (rc == 0) == expect_pass, "message": msg[:200]})

    try:
        n = 0

        def fresh():
            nonlocal n
            n += 1
            return copy_bundle(SCRATCH / ("b%02d" % n))

        control("intact copied bundle, real repository", True, fresh(), repo, d)
        mir = mirror_repo(repo, SCRATCH / "repo-mirror")
        control("intact copied bundle, intact repository mirror", True, fresh(), mir, d)
        control("wrong external digest", False, fresh(), repo,
                ("0" if d[0] != "0" else "1") + d[1:])
        control("malformed external digest", False, fresh(), repo, d.upper())
        b = fresh(); flip_byte(b / "review.md")
        control("modified review.md", False, b, repo, d)
        b = fresh(); (b / "extra.txt").write_text("x\n")
        control("extra payload file", False, b, repo, d)
        b = fresh(); (b / "checks.json").unlink()
        control("missing payload file", False, b, repo, d)
        b = fresh(); (b / "subdir").mkdir()
        control("unexpected directory", False, b, repo, d)
        b = fresh(); real = SCRATCH / "review-target.md"
        shutil.copy2(b / "review.md", real); (b / "review.md").unlink()
        (b / "review.md").symlink_to(real)
        control("symlink substitution with identical bytes", False, b, repo, d)
        b = fresh(); (b / "seal.sha256").write_text("0" * 64 + "  manifest.json\n")
        control("altered seal copy", False, b, repo, d)
        b = fresh(); flip_byte(b / "manifest.json")
        control("modified manifest, old digest", False, b, repo, d)
        b = fresh(); h = reseal(b, lambda m: m.__setitem__("count_credit", 1))
        control("resealed manifest claiming count credit", False, b, repo, h)
        b = fresh()
        st = json.loads((b / "status.json").read_bytes()); st["count_credit"] = 1
        (b / "status.json").write_text(json.dumps(st, indent=2) + "\n")
        sb = (b / "status.json").read_bytes()

        def fix_status(m):
            for r in m["payloads"]:
                if r["path"] == "status.json":
                    r["bytes"], r["sha256"] = len(sb), hashlib.sha256(sb).hexdigest()
        h = reseal(b, fix_status)
        control("resealed bundle with altered status.json", False, b, repo, h)
        # external drift in a mirror of the repository
        mir2 = mirror_repo(repo, SCRATCH / "repo-drift")
        flip_byte(mir2 / "frontier/campaigns/2026-10-14/fresh-analytic-discovery-r107/proof.md")
        control("author proof.md drift", False, fresh(), mir2, d)
        mir3 = mirror_repo(repo, SCRATCH / "repo-extra")
        (mir3 / "frontier/campaigns/2026-10-14/fresh-analytic-discovery-r107/new.md").write_text("x\n")
        control("extra file in author directory", False, fresh(), mir3, d)
        mir4 = mirror_repo(repo, SCRATCH / "repo-r1")
        flip_byte(mir4 / "frontier/campaigns/2026-10-14/t333e107-contribution-r1/review.md")
        control("r1 draft drift", False, fresh(), mir4, d)
        # pinned blob mismatch even when the anchor hash is resealed to match
        mir5 = mirror_repo(repo, SCRATCH / "repo-blob")
        rel = ("frontier/campaigns/2026-10-14/fresh-analytic-discovery-r107/"
               "private/upstream/velocity-loop.tex")
        flip_byte(mir5 / rel)
        vb = (mir5 / rel).read_bytes()
        b = fresh()

        def fix_anchor(m):
            for r in m["external_anchors"]:
                if r["path"] == rel:
                    r["bytes"], r["sha256"] = len(vb), hashlib.sha256(vb).hexdigest()
        h = reseal(b, fix_anchor)
        control("source blob altered, anchor resealed", False, b, mir5, h)
        mir6 = mirror_repo(repo, SCRATCH / "repo-tree")
        t = json.loads((mir6 / "sources/preprints-tree.json").read_bytes())
        t["truncated"] = True
        tb = json.dumps(t).encode()
        (mir6 / "sources/preprints-tree.json").write_bytes(tb)
        b = fresh()

        def fix_tree(m):
            for r in m["external_anchors"]:
                if r["path"] == "sources/preprints-tree.json":
                    r["bytes"], r["sha256"] = len(tb), hashlib.sha256(tb).hexdigest()
        h = reseal(b, fix_tree)
        control("truncated tree, anchor resealed", False, b, mir6, h)
    finally:
        shutil.rmtree(SCRATCH)
    out = {"manifest_under_test": d, "controls": results,
           "all_as_expected": all(r["as_expected"] for r in results),
           "scratch_removed": not SCRATCH.exists(),
           "certifies_mathematics_or_contribution": False}
    print(json.dumps(out, indent=1, sort_keys=True))
    return 0 if out["all_as_expected"] else 1


if __name__ == "__main__":
    sys.exit(main())
