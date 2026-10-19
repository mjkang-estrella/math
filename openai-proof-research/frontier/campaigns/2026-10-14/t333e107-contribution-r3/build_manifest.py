#!/usr/bin/env python3
"""Write manifest.json and seal.sha256 for this review directory.

It writes only those two envelope files in this directory and reads
everything else. Run it only to reseal after an intentional payload change.
The printed digest must be handed off out of band; the seal file is only a
convenience copy.

Usage: python3 -B build_manifest.py --repo-root <REPO>
"""
import argparse
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
PIN = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"
CAMP = "frontier/campaigns/2026-10-14/"
AUTHOR = CAMP + "fresh-analytic-discovery-r107/"
S333 = ("preprints/Smooth-isometric-immersions-of-closed-surfaces-into-"
        "Euclidean-four-space-September-23-2026/build/")
S334_MAIN = ("preprints/A-Smooth-Metric-with-No-Local-Isometric-Immersion-into-"
             "Three-Space-September-24-2026/build/main.tex")


def rec(base, rel, **kw):
    d = (base / rel).read_bytes()
    r = {"path": rel, "bytes": len(d), "sha256": hashlib.sha256(d).hexdigest()}
    r.update(kw)
    return r


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo-root", type=Path, required=True)
    repo = ap.parse_args().repo_root.resolve(strict=True)
    payloads = [rec(HERE, p.relative_to(HERE).as_posix(), classification="original")
                for p in sorted(HERE.rglob("*"))
                if p.is_file() and p.name not in ("manifest.json", "seal.sha256")]
    anchors = [rec(repo, p, role="context") for p in
               ("AGENTS.md", "sources/upstream.json", "sources/preprints-tree.json")]
    anchors += [rec(repo, p.relative_to(repo).as_posix(), role="author-baseline")
                for p in sorted((repo / AUTHOR).rglob("*")) if p.is_file()]
    anchors += [rec(repo, CAMP + p, role="family333-body") for p in
                ("fresh-parent-discovery-r5/screen.md",
                 "fresh-analytic-discovery-r17/source-reading.md",
                 "fresh-structural-discovery-r92/screening.md")]
    anchors += [rec(repo, CAMP + "t333e107-contribution-r1/" + p, role="r1-unsealed-draft")
                for p in ("README.md", "author-baseline.json", "paid-unpaid-comparison.md",
                          "reading-limits.md", "review.md", "verify.py")]
    tree = json.loads((repo / "sources/preprints-tree.json").read_bytes())
    entries = {e["path"]: e for e in tree["tree"]}
    blobs = []
    for p in sorted((repo / AUTHOR / "private/upstream").iterdir()):
        d = p.read_bytes()
        g = hashlib.sha1(b"blob %d\0" % len(d) + d).hexdigest()
        up = S334_MAIN if p.name == "companion334-main.tex" else S333 + p.name
        if entries[up]["sha"] != g:
            raise SystemExit("pinned blob mismatch: " + up)
        blobs.append({"path": p.relative_to(repo).as_posix(), "upstream_path": up,
                      "git_blob": g})
    m = {"schema": "t333e107-contribution-r3-integrity-v1", "upstream_revision": PIN,
         "classification": "TECHNICAL_CONDITIONAL_ON_CORRECTNESS",
         "count_credit": 0, "acceptance_entered": False,
         "certifies_mathematics_or_contribution": False,
         "envelope_exclusions": ["manifest.json", "seal.sha256"],
         "payloads": payloads, "external_anchors": anchors, "pinned_blobs": blobs}
    mb = (json.dumps(m, indent=1, sort_keys=True) + "\n").encode()
    (HERE / "manifest.json").write_bytes(mb)
    h = hashlib.sha256(mb).hexdigest()
    (HERE / "seal.sha256").write_text(h + "  manifest.json\n")
    print(json.dumps({"manifest_sha256": h, "payloads": len(payloads),
                      "external_anchors": len(anchors), "pinned_blobs": len(blobs)}))


if __name__ == "__main__":
    main()
