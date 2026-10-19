#!/usr/bin/env python3
"""Positive and negative integrity controls for verify.py (integrity only).

All mutations are applied to copies in a fresh temporary directory: a copy of
this bundle and a copy of exactly the anchored external files.  The
repository itself is only read.  Writes the receipt to --out (default: print).
Run with: python3 -I integrity_controls.py --repo-root <ROOT> --expected <SHA256> [--out FILE]
"""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent


def run(bundle, repo, digest):
    p = subprocess.run([sys.executable, "-I", str(HERE / "verify.py"), "--expected-manifest", digest,
                        "--repo-root", str(repo), "--bundle-root", str(bundle)],
                       capture_output=True, text=True)
    return p.returncode, (p.stdout.strip() or p.stderr.strip())


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo-root", type=Path, required=True)
    ap.add_argument("--expected", required=True)
    ap.add_argument("--out", type=Path)
    a = ap.parse_args()
    repo = a.repo_root.resolve(strict=True)
    digest = a.expected
    manifest = json.loads((HERE / "manifest.json").read_bytes())
    results = []

    def record(name, expected_exit, got):
        results.append({"control": name, "expected_exit": expected_exit,
                        "actual_exit": got[0], "output": got[1],
                        "as_expected": got[0] == expected_exit})

    record("intact bundle against real repository", 0, run(HERE, repo, digest))
    record("wrong detached digest", 1, run(HERE, repo, "0" * 64))
    record("malformed detached digest", 1, run(HERE, repo, digest.upper()))

    with tempfile.TemporaryDirectory(prefix="t333e107r2-controls-") as tmp:
        tmp = Path(tmp)

        def fresh():
            b, r = tmp / "bundle", tmp / "root"
            for d in (b, r):
                if d.exists():
                    shutil.rmtree(d)
            shutil.copytree(HERE, b, symlinks=True,
                            ignore=shutil.ignore_patterns("__pycache__"))
            for e in manifest["external_anchors"]:
                dst = r / e["path"]
                dst.parent.mkdir(parents=True, exist_ok=True)
                shutil.copyfile(repo / e["path"], dst)
            return b, r

        b, r = fresh()
        record("intact copied bundle and copied anchor root", 0, run(b, r, digest))

        b, r = fresh()
        p = b / "review.md"
        p.write_bytes(p.read_bytes().replace(b"TECHNICAL", b"TECHNICAX", 1))
        record("same-size edit of review.md", 1, run(b, r, digest))

        b, r = fresh()
        (b / "extra.md").write_text("x\n")
        record("unexpected extra payload", 1, run(b, r, digest))

        b, r = fresh()
        (b / "checks.json").unlink()
        record("missing payload", 1, run(b, r, digest))

        b, r = fresh()
        (b / "README.md").unlink()
        os.symlink(b / "review.md", b / "README.md")
        record("symlink substitution", 1, run(b, r, digest))

        b, r = fresh()
        (b / "scratch").mkdir()
        record("unexpected empty directory", 1, run(b, r, digest))

        b, r = fresh()
        (b / "seal.sha256").write_text("f" * 64 + "  manifest.json\n")
        record("seal copy disagrees with detached digest", 1, run(b, r, digest))

        b, r = fresh()
        mp = b / "manifest.json"
        mp.write_bytes(mp.read_bytes().replace(b'"count_credit": 0', b'"count_credit": 1', 1))
        record("modified manifest (count credit) under original digest", 1, run(b, r, digest))

        b, r = fresh()
        ap_ = r / "frontier/campaigns/2026-10-14/fresh-analytic-discovery-r107/proof.md"
        ap_.write_bytes(ap_.read_bytes() + b"\n")
        record("author proof.md drift in copied root", 1, run(b, r, digest))

        b, r = fresh()
        tp = r / "sources/preprints-tree.json"
        tp.write_bytes(tp.read_bytes().replace(b'"truncated": false', b'"truncated": true', 1))
        record("tree drift (truncated flag) in copied root", 1, run(b, r, digest))

        b, r = fresh()
        (r / "frontier/campaigns/2026-10-14/t333e107-contribution-r1/review.md").unlink()
        record("missing r1 draft anchor in copied root", 1, run(b, r, digest))
        tmp_listing = sorted(str(q.relative_to(tmp)) for q in tmp.iterdir())

    receipt = {
        "purpose": "Integrity controls only; not proof, contribution or priority evidence.",
        "tested_manifest_sha256": digest,
        "verifier_sha256": hashlib.sha256((HERE / "verify.py").read_bytes()).hexdigest(),
        "scratch": "Python tempfile directory under the system temp root, removed on exit; "
                   "repository files were only read.",
        "scratch_top_level_before_removal": tmp_listing,
        "all_as_expected": all(x["as_expected"] for x in results),
        "controls": results,
    }
    text = json.dumps(receipt, indent=1, sort_keys=True) + "\n"
    if a.out:
        a.out.write_text(text)
    else:
        sys.stdout.write(text)
    return 0 if receipt["all_as_expected"] else 2


if __name__ == "__main__":
    sys.exit(main())
