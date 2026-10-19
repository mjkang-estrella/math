#!/usr/bin/env python3
"""Read-only offline integrity verifier for the T333E107 contribution r2 bundle.

Integrity only: it does not certify mathematics, contribution or priority.
The expected manifest SHA256 must come from the detached parent-facing
handoff; the neighbouring seal.sha256 is only a convenience copy and is
checked against the detached value, never trusted in its place.

It performs no writes and no network access, and executes no payload.
Run with: python3 -I verify.py --expected-manifest <SHA256> --repo-root <ROOT>
"""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import stat
import sys

SCHEMA = "t333e107-contribution-r2-integrity-v1"
PIN = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"
ENVELOPES = ("manifest.json", "seal.sha256")
TREE = "sources/preprints-tree.json"
TREE_ENTRIES = 13223


class Failure(Exception):
    pass


def need(cond, msg):
    if not cond:
        raise Failure(msg)


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def resolve_regular(base, rel):
    need(isinstance(rel, str) and rel, "bad path entry")
    p = PurePosixPath(rel)
    need(not p.is_absolute() and ".." not in p.parts and "\\" not in rel
         and p.as_posix() == rel, "unsafe path: " + rel)
    cur = base
    for part in p.parts:
        cur = cur / part
        need(not cur.is_symlink(), "symlink on path: " + rel)
    need(cur.exists() and stat.S_ISREG(cur.lstat().st_mode),
         "missing or non-regular file: " + rel)
    return cur


def check_bytes(base, rec):
    data = resolve_regular(base, rec["path"]).read_bytes()
    need(len(data) == rec["bytes"], "size mismatch: " + rec["path"])
    need(sha256(data) == rec["sha256"], "SHA256 mismatch: " + rec["path"])
    return data


def verify(bundle, repo, expected):
    need(re.fullmatch(r"[0-9a-f]{64}", expected or "") is not None,
         "expected manifest digest must be 64 lowercase hex characters")
    mbytes = resolve_regular(bundle, "manifest.json").read_bytes()
    need(sha256(mbytes) == expected, "detached manifest anchor mismatch")
    seal = resolve_regular(bundle, "seal.sha256").read_text()
    need(seal == expected + "  manifest.json\n", "seal copy disagrees with detached anchor")
    m = json.loads(mbytes)
    need(m.get("schema") == SCHEMA, "unexpected schema")
    need(m.get("upstream_revision") == PIN, "wrong upstream revision")
    need(m.get("envelopes") == list(ENVELOPES), "unexpected envelope list")
    need(m.get("count_credit") == 0 and m.get("acceptance_entered") is False,
         "status boundary altered in manifest")

    # exact payload membership, no symlinks, no unexpected directories
    names = [r["path"] for r in m["payloads"]]
    need(len(names) == len(set(names)), "duplicate payload")
    need(not set(names) & set(ENVELOPES), "envelope listed as payload")
    dirs = {q.as_posix() for n in names for q in PurePosixPath(n).parents
            if q.as_posix() != "."}
    seen = set()
    for p in bundle.rglob("*"):
        rel = p.relative_to(bundle).as_posix()
        need(not p.is_symlink(), "symlink in bundle: " + rel)
        if p.is_dir():
            need(rel in dirs, "unexpected directory: " + rel)
            continue
        need(stat.S_ISREG(p.lstat().st_mode), "special file: " + rel)
        if rel not in ENVELOPES:
            seen.add(rel)
    need(seen == set(names), "payload membership mismatch")
    for rec in m["payloads"]:
        need(rec.get("classification") == "original", "non-original payload in public bundle")
        check_bytes(bundle, rec)

    # status file must agree with the no-count boundary
    status = json.loads(resolve_regular(bundle, "status.json").read_bytes())
    need(status.get("contribution_verdict") == "TECHNICAL"
         and status.get("count_credit") == 0
         and status.get("acceptance_entered") is False
         and status.get("substantial_contribution_pass") is False,
         "status.json boundary mismatch")

    # external anchors (author packet, context, prior drafts, companions)
    anchors = [r["path"] for r in m["external_anchors"]]
    need(len(anchors) == len(set(anchors)), "duplicate external anchor")
    for rec in m["external_anchors"]:
        check_bytes(repo, rec)
    need(TREE in anchors, "complete tree not anchored")
    tree = json.loads(resolve_regular(repo, TREE).read_bytes())
    need(tree.get("truncated") is False and len(tree.get("tree", [])) == TREE_ENTRIES,
         "tree is not the complete nontruncated 13223-entry tree")
    entries = {e["path"]: e for e in tree["tree"]}
    need(len(entries) == TREE_ENTRIES, "duplicate tree paths")

    # pinned Git blobs of the author's retained upstream copies
    for rec in m["pinned_blobs"]:
        need(rec["anchor"] in anchors, "pinned blob copy not anchored: " + rec["anchor"])
        data = resolve_regular(repo, rec["anchor"]).read_bytes()
        blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        e = entries.get(rec["upstream_path"])
        need(e is not None and e.get("type") == "blob", "upstream path absent: " + rec["upstream_path"])
        need(blob == rec["git_blob"] == e["sha"], "pinned Git blob mismatch: " + rec["upstream_path"])
    return {
        "integrity": "verified",
        "manifest_sha256": expected,
        "payloads": len(names),
        "external_anchors": len(anchors),
        "pinned_blobs": len(m["pinned_blobs"]),
        "contribution_verdict_recorded": status["contribution_verdict"],
        "count_credit": 0,
        "mathematics_or_contribution_certified": False,
    }


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--expected-manifest", required=True)
    ap.add_argument("--repo-root", type=Path, required=True)
    ap.add_argument("--bundle-root", type=Path, default=Path(__file__).resolve().parent)
    a = ap.parse_args()
    try:
        out = verify(a.bundle_root.resolve(strict=True), a.repo_root.resolve(strict=True),
                     a.expected_manifest)
    except (Failure, KeyError, TypeError, ValueError, OSError) as exc:
        print("INTEGRITY FAILURE: %s" % exc, file=sys.stderr)
        return 1
    print(json.dumps(out, sort_keys=True))
    return 0


if __name__ == "__main__":
    sys.exit(main())
