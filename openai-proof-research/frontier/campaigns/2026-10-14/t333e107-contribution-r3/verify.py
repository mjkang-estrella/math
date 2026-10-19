#!/usr/bin/env python3
"""Read-only, offline integrity verifier for the T333E107 r3 contribution review.

It authenticates bytes only. It does not certify mathematics, priority, or
contribution. The expected manifest digest must come from the detached
parent-facing handoff, not from the neighboring seal copy. The program performs
no writes, no network access, and executes no payload.
"""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import stat
import sys

PIN = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"
SCHEMA = "t333e107-contribution-r3-integrity-v1"
ENVELOPES = ("manifest.json", "seal.sha256")
TREE = "sources/preprints-tree.json"
AUTHOR_DIR = "frontier/campaigns/2026-10-14/fresh-analytic-discovery-r107/"
AUTHOR_FILE_COUNT = 36


def require(cond, msg):
    if not cond:
        raise ValueError(msg)


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def safe_file(base, rel):
    require(isinstance(rel, str) and rel, "empty or non-string path")
    p = PurePosixPath(rel)
    require(not p.is_absolute() and ".." not in p.parts and "\\" not in rel
            and p.as_posix() == rel, "unsafe path: " + rel)
    target = base
    for part in p.parts:
        target = target / part
        require(not target.is_symlink(), "symlink: " + rel)
    require(target.exists() and stat.S_ISREG(target.stat().st_mode),
            "missing or non-regular file: " + rel)
    return target


def check_record(base, rec):
    data = safe_file(base, rec["path"]).read_bytes()
    require(len(data) == rec["bytes"], "size mismatch: " + rec["path"])
    require(sha256(data) == rec["sha256"], "SHA256 mismatch: " + rec["path"])
    return data


def verify(bundle, repo, expected):
    require(re.fullmatch(r"[0-9a-f]{64}", expected or "") is not None,
            "expected manifest digest must be 64 lowercase hex characters")
    mbytes = safe_file(bundle, "manifest.json").read_bytes()
    require(sha256(mbytes) == expected, "detached manifest anchor mismatch")
    m = json.loads(mbytes)
    require(m.get("schema") == SCHEMA, "unexpected schema")
    require(m.get("upstream_revision") == PIN, "wrong upstream revision")
    require(m.get("envelope_exclusions") == sorted(ENVELOPES), "envelope list changed")
    require(m.get("count_credit") == 0 and m.get("acceptance_entered") is False,
            "status boundary changed")
    seal = safe_file(bundle, "seal.sha256").read_text()
    require(seal == expected + "  manifest.json\n", "seal copy mismatch")

    # exact bundle membership
    names = [r["path"] for r in m["payloads"]]
    require(len(names) == len(set(names)), "duplicate payload")
    require(not set(names) & set(ENVELOPES), "envelope listed as payload")
    dirs = {q.as_posix() for n in names for q in PurePosixPath(n).parents
            if q.as_posix() != "."}
    seen = set()
    for p in bundle.rglob("*"):
        rel = p.relative_to(bundle).as_posix()
        require(not p.is_symlink(), "symlink in bundle: " + rel)
        if p.is_dir():
            require(rel in dirs, "unexpected directory: " + rel)
        else:
            require(stat.S_ISREG(p.stat().st_mode), "special file: " + rel)
            if rel not in ENVELOPES:
                seen.add(rel)
    require(seen == set(names), "payload membership mismatch")
    for rec in m["payloads"]:
        require(rec.get("classification") == "original",
                "unexpected payload classification: " + rec["path"])
        check_record(bundle, rec)

    status = json.loads(safe_file(bundle, "status.json").read_bytes())
    require(status["contribution_classification"]
            == "TECHNICAL_CONDITIONAL_ON_CORRECTNESS"
            and status["count_credit"] == 0
            and status["acceptance_entered"] is False
            and status["substantial_contribution_pass"] is False,
            "status.json boundary changed")

    # detached external anchors in the repository
    anchors = m["external_anchors"]
    apaths = [a["path"] for a in anchors]
    require(len(apaths) == len(set(apaths)), "duplicate external anchor")
    for a in anchors:
        check_record(repo, a)
    author = [p for p in apaths if p.startswith(AUTHOR_DIR)]
    require(len(author) == AUTHOR_FILE_COUNT, "author baseline is not 36 files")
    actual_author = {p.relative_to(repo).as_posix()
                     for p in (repo / AUTHOR_DIR).rglob("*") if p.is_file()}
    require(actual_author == set(author), "author directory membership changed")
    require(TREE in apaths, "complete tree not anchored")

    # pinned upstream blobs against the complete tree
    tree = json.loads(safe_file(repo, TREE).read_bytes())
    require(tree.get("truncated") is False and len(tree["tree"]) == 13223,
            "tree is not the complete 13223-entry listing")
    entries = {e["path"]: e for e in tree["tree"]}
    require(len(entries) == 13223, "duplicate tree path")
    blobs = m["pinned_blobs"]
    require(len(blobs) == 13, "expected 13 pinned blobs")
    for b in blobs:
        data = safe_file(repo, b["path"]).read_bytes()
        require(b["path"] in apaths, "pinned blob copy not anchored: " + b["path"])
        g = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        e = entries.get(b["upstream_path"])
        require(e is not None and e["type"] == "blob", "absent upstream path")
        require(g == b["git_blob"] == e["sha"], "Git blob mismatch: " + b["upstream_path"])
    return {"integrity": "verified", "manifest_sha256": expected,
            "payloads": len(names), "external_anchors": len(apaths),
            "author_files": len(author), "pinned_blobs": len(blobs),
            "mathematics_or_contribution_certified": False}


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--expected-manifest", required=True)
    ap.add_argument("--repo-root", type=Path, required=True)
    ap.add_argument("--bundle-root", type=Path, default=Path(__file__).parent)
    args = ap.parse_args()
    try:
        out = verify(args.bundle_root.resolve(strict=True),
                     args.repo_root.resolve(strict=True), args.expected_manifest)
    except (ValueError, KeyError, TypeError, OSError, json.JSONDecodeError) as exc:
        print("INTEGRITY FAILURE: " + str(exc), file=sys.stderr)
        return 1
    print(json.dumps(out, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
