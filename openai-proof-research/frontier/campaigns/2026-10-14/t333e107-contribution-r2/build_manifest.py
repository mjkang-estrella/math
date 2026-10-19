#!/usr/bin/env python3
"""Write manifest.json and seal.sha256 for this r2 bundle (owned directory only).

Hashes every non-envelope file in the bundle (all original), a fixed list of
external read-only anchors under the repository root, and the author's 13
retained upstream copies' Git blob identities.  Reads external files; writes
only manifest.json and seal.sha256 in this directory.
Run with: python3 -I build_manifest.py --repo-root <ROOT>
"""
import argparse
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
CAMP = "frontier/campaigns/2026-10-14/"
AUTHOR = CAMP + "fresh-analytic-discovery-r107/"
R1 = CAMP + "t333e107-contribution-r1/"
CONTEXT = [
    "AGENTS.md", "sources/upstream.json", "sources/preprints-tree.json", "sources/CONTENTS.md",
    CAMP + "fresh-parent-discovery-r5/screen.md",
    CAMP + "fresh-analytic-discovery-r17/source-reading.md",
    CAMP + "fresh-analytic-discovery-r17/candidate.md",
    CAMP + "fresh-structural-discovery-r92/screening.md",
] + [R1 + n for n in ("README.md", "review.md", "paid-unpaid-comparison.md",
                      "reading-limits.md", "author-baseline.json", "verify.py")]


def rec(base, rel, **extra):
    data = (base / rel).read_bytes()
    d = {"path": rel, "bytes": len(data), "sha256": hashlib.sha256(data).hexdigest()}
    d.update(extra)
    return d


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--repo-root", type=Path, required=True)
    repo = ap.parse_args().repo_root.resolve(strict=True)
    author_dir = repo / AUTHOR
    author_files = sorted(p.relative_to(repo).as_posix() for p in author_dir.rglob("*")
                          if p.is_file() and not p.is_symlink())
    anchors = [rec(repo, r) for r in CONTEXT + author_files]
    prov = json.loads((author_dir / "upstream-provenance.json").read_bytes())
    pinned = [{"anchor": AUTHOR + f["path"], "upstream_path": f["upstream_path"],
               "git_blob": f["git_blob"]} for f in prov["files"]]
    payloads = [rec(HERE, p.relative_to(HERE).as_posix(), classification="original")
                for p in sorted(HERE.rglob("*"))
                if p.is_file() and p.name not in ("manifest.json", "seal.sha256")]
    manifest = {
        "schema": "t333e107-contribution-r2-integrity-v1",
        "upstream_revision": "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb",
        "target": "T333E107",
        "contribution_verdict": "TECHNICAL (conditional on correctness)",
        "count_credit": 0,
        "acceptance_entered": False,
        "envelopes": ["manifest.json", "seal.sha256"],
        "author_detached_manifest_sha256": "e3b992016df3fadbe6fc223e9f1dfb9565f435b9afe9ed81705a495453ffdb6f",
        "limits": [
            "Integrity binds bytes only; it certifies no mathematics, contribution or priority.",
            "External anchors detect drift of the author packet, context and prior drafts; they do not endorse them.",
            "Third-party evidence is not copied into this bundle; only hashes of author-retained copies are bound.",
        ],
        "payloads": payloads,
        "external_anchors": anchors,
        "pinned_blobs": pinned,
    }
    data = (json.dumps(manifest, indent=1, sort_keys=True) + "\n").encode()
    (HERE / "manifest.json").write_bytes(data)
    digest = hashlib.sha256(data).hexdigest()
    (HERE / "seal.sha256").write_text(digest + "  manifest.json\n")
    print(digest, len(payloads), len(anchors), len(pinned))


if __name__ == "__main__":
    main()
