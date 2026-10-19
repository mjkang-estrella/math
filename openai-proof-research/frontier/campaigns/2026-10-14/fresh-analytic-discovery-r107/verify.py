#!/usr/bin/env python3
"""Read-only, offline integrity verification. Not mathematical certification.

Supply --expected-manifest from the detached parent-facing handoff, never merely
from the mutable seal file beside this program. No payload code is executed.
"""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import stat
import sys

PIN = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"
ENVELOPES = {"manifest.json", "seal.sha256"}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def safe_file(base, relative):
    require(isinstance(relative, str), "non-string path")
    p = PurePosixPath(relative)
    require(relative and not p.is_absolute() and ".." not in p.parts
            and p.as_posix() == relative and "\\" not in relative,
            "unsafe path: " + relative)
    target = base
    for part in p.parts:
        target = target / part
        require(not target.is_symlink(), "symlink: " + relative)
    require(target.exists() and stat.S_ISREG(target.stat().st_mode),
            "missing/nonregular file: " + relative)
    return target


def check_record(base, record):
    data = safe_file(base, record["path"]).read_bytes()
    require(len(data) == record["bytes"], "size mismatch: " + record["path"])
    require(sha(data) == record["sha256"], "SHA256 mismatch: " + record["path"])
    return data


def verify(root, repo, expected):
    require(re.fullmatch(r"[0-9a-f]{64}", expected) is not None,
            "expected digest must be 64 lowercase hex digits")
    manifest_bytes = safe_file(root, "manifest.json").read_bytes()
    require(sha(manifest_bytes) == expected, "external manifest anchor mismatch")
    manifest = json.loads(manifest_bytes)
    require(manifest["schema"] == "r107-integrity-v1", "unexpected schema")
    require(manifest["upstream_revision"] == PIN, "wrong upstream revision")
    require(manifest["envelope_exclusions"] == sorted(ENVELOPES),
            "unexpected envelope exclusions")
    seal = safe_file(root, "seal.sha256").read_text()
    require(seal == expected + "  manifest.json\n", "detached seal copy mismatch")

    records = manifest["payloads"]
    names = [r["path"] for r in records]
    require(len(set(names)) == len(names), "duplicate payload")
    require(not set(names) & ENVELOPES, "envelope is not payload")
    expected_dirs = set()
    for name in names:
        for p in PurePosixPath(name).parents:
            if p.as_posix() != ".":
                expected_dirs.add(p.as_posix())
    seen = set()
    for p in root.rglob("*"):
        relative = p.relative_to(root).as_posix()
        require(not p.is_symlink(), "symlink in bundle: " + relative)
        if p.is_dir():
            require(relative in expected_dirs, "unexpected directory: " + relative)
        else:
            require(stat.S_ISREG(p.stat().st_mode), "special file: " + relative)
            if relative not in ENVELOPES:
                seen.add(relative)
    require(seen == set(names), "payload membership mismatch")
    for record in records:
        require(record["classification"] in {"original", "private-third-party"},
                "invalid payload classification")
        require((record["classification"] == "private-third-party")
                == record["path"].startswith("private/"),
                "private boundary mismatch")
        check_record(root, record)

    anchor_names = [r["path"] for r in manifest["external_anchors"]]
    require(len(anchor_names) == len(set(anchor_names)), "duplicate external anchor")
    for record in manifest["external_anchors"]:
        check_record(repo, record)
    require("sources/preprints-tree.json" in anchor_names, "tree is not anchored")
    tree = json.loads(safe_file(repo, "sources/preprints-tree.json").read_bytes())
    require(tree["truncated"] is False and len(tree["tree"]) == 13223,
            "tree is not complete 13223-entry tree")
    entries = {e["path"]: e for e in tree["tree"]}
    require(len(entries) == 13223, "duplicate canonical tree path")
    provenance = json.loads(safe_file(root, "upstream-provenance.json").read_bytes())
    require(provenance["revision"] == PIN and provenance["tree_entries"] == 13223
            and provenance["truncated"] is False, "wrong upstream provenance")
    upstream_names = set()
    for record in provenance["files"]:
        require(record["path"] in seen, "upstream file not in manifest")
        require(record["path"] not in upstream_names, "duplicate upstream file")
        upstream_names.add(record["path"])
        data = check_record(root, record)
        canonical = record["upstream_path"]
        require(canonical in entries and entries[canonical]["type"] == "blob",
                "upstream path absent/nonblob")
        blob = hashlib.sha1(b"blob " + str(len(data)).encode("ascii")
                            + b"\0" + data).hexdigest()
        require(blob == record["git_blob"] == entries[canonical]["sha"],
                "pinned Git blob mismatch: " + canonical)
        require(record["raw_url"] == "https://raw.githubusercontent.com/openai/math/"
                + PIN + "/" + canonical, "nonpinned raw URL")
    primary = json.loads(safe_file(root, "primary-provenance.json").read_bytes())
    primary_names = set()
    for record in primary["files"]:
        require(record["path"] in seen, "primary file not in manifest")
        require(record["path"] not in primary_names, "duplicate primary file")
        primary_names.add(record["path"])
        check_record(root, record)
        if "derived_from" in record:
            require(record["derived_from"] in seen, "missing primary derivation input")
    require({p for p in seen if p.startswith("private/")}
            == upstream_names | primary_names, "unaccounted private evidence")
    return {"integrity": "verified", "payloads": len(records),
            "external_anchors": len(anchor_names), "pinned_blobs": len(upstream_names),
            "primary_pdf_count": sum(p.endswith(".pdf") for p in primary_names),
            "manifest_sha256": expected,
            "mathematics_or_contribution_certified": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--expected-manifest", required=True)
    parser.add_argument("--repo-root", type=Path, required=True)
    parser.add_argument("--bundle-root", type=Path, default=Path(__file__).parent)
    args = parser.parse_args()
    try:
        result = verify(args.bundle_root.resolve(strict=True),
                        args.repo_root.resolve(strict=True), args.expected_manifest)
        print(json.dumps(result, sort_keys=True))
        return 0
    except (ValueError, KeyError, TypeError, OSError) as exc:
        print("INTEGRITY FAILURE: " + str(exc), file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
