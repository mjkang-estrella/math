#!/usr/bin/env python3
"""MIT. Offline, read-only integrity verifier. No mathematics is certified."""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import stat

PIN = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"
SCOPE = "837137e682d13cae985a97173e731a79db7418df6221de38df3626bc93275618"
OWNED = "frontier/campaigns/2026-10-14/fresh-analytic-discovery-r108"
PACKAGE = Path(__file__).absolute().parents[1]
REPO = PACKAGE.parents[3]


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def safe_path(base, relative):
    p = PurePosixPath(relative)
    require(not p.is_absolute() and str(p) == relative and
            all(part not in ("", ".", "..") for part in p.parts),
            "unsafe/noncanonical relative path")
    current = base
    for part in p.parts:
        current = current / part
        require(not current.is_symlink(), "symlink is forbidden: " + str(current))
    require(current.is_file(), "missing regular file: " + str(current))
    require(stat.S_ISREG(current.stat().st_mode), "nonregular file")
    return current


def inventory(package):
    files, directories = [], []
    for p in package.rglob("*"):
        require(not p.is_symlink(), "owned symlink is forbidden")
        relative = p.relative_to(package).as_posix()
        if p.is_dir():
            directories.append(relative)
        else:
            require(stat.S_ISREG(p.stat().st_mode), "owned nonregular file")
            if relative != "manifest.json":
                files.append(relative)
    return sorted(files), sorted(directories)


def validate(manifest):
    require(PACKAGE.relative_to(REPO).as_posix() == OWNED, "wrong owned root")
    require(manifest["owned_directory"] == OWNED, "wrong manifest root")
    require(manifest["revision"] == PIN, "wrong revision")
    require(manifest["target"] == "T273NC108", "wrong target")
    require(manifest["count_change"] == 0, "unauthorized count credit")
    require(manifest["status"] == "AUTHOR_PROOF_COMPLETE_UNREVIEWED_CONTRIBUTION_UNRESOLVED",
            "unexpected research status")
    actual_files, actual_dirs = inventory(PACKAGE)
    payloads = manifest["payloads"]
    require(len(payloads) == len({x["path"] for x in payloads}), "duplicate payload")
    require(actual_files == sorted(x["path"] for x in payloads), "owned file inventory mismatch")
    require(actual_dirs == manifest["directories"], "owned directory inventory mismatch")
    for row in payloads:
        body = safe_path(PACKAGE, row["path"]).read_bytes()
        require(len(body) == row["bytes"] and sha(body) == row["sha256"],
                "payload changed: " + row["path"])
    anchors = manifest["external_anchors"]
    require(len(anchors) == len({x["path"] for x in anchors}), "duplicate external anchor")
    for row in anchors:
        require(not row["path"].startswith(OWNED + "/"), "anchor is not external")
        body = safe_path(REPO, row["path"]).read_bytes()
        require(sha(body) == row["sha256"] and len(body) == row["bytes"],
                "external anchor changed: " + row["path"])
    required = {"AGENTS.md", "sources/upstream.json", "sources/CONTENTS.md",
                "sources/preprints-tree.json", "frontier/NEW-TEN-2026-10-14.md"}
    require(required <= {x["path"] for x in anchors}, "missing required external anchor")
    upstream = json.loads((REPO / "sources/upstream.json").read_bytes())
    require(upstream["commit"] == PIN, "upstream revision mismatch")
    tree = json.loads((REPO / "sources/preprints-tree.json").read_bytes())
    entries = tree["tree"]
    require(tree["truncated"] is False and len(entries) == 13223, "tree is incomplete")
    paths = {x["path"]: x for x in entries}
    require(len(paths) == 13223, "duplicate complete-tree entry")
    source_rows = json.loads((PACKAGE / "private/retrieval.json").read_bytes())
    require(len(source_rows) == 74, "unexpected pinned evidence inventory")
    for row in source_rows:
        body = safe_path(PACKAGE, row["path"]).read_bytes()
        blob = hashlib.sha1(b"blob " + str(len(body)).encode() + b"\0" + body).hexdigest()
        entry = paths[row["upstream_path"]]
        require(entry["type"] == "blob" and entry["sha"] == blob == row["git_blob"],
                "pinned Git blob mismatch: " + row["upstream_path"])
        require(sha(body) == row["sha256"], "pinned SHA256 mismatch")
        require(row["url"] == "https://raw.githubusercontent.com/openai/math/" + PIN + "/" + row["upstream_path"],
                "non-pinned raw URL")
    selected = "preprints/The-entropy-photon-number-inequality-September-24-2026/"
    complete_family_tex = {x["path"] for x in entries if x["type"] == "blob" and
                           x["path"].startswith(selected) and x["path"].endswith(".tex")}
    copied_family_tex = {x["upstream_path"] for x in source_rows if x["upstream_path"].startswith(selected)}
    require(complete_family_tex == copied_family_tex and len(complete_family_tex) == 9,
            "selected source family incomplete")
    primaries = json.loads((PACKAGE / "private/primary-retrieval.json").read_bytes())
    for row in primaries:
        if "error" in row:
            continue
        require(sha(safe_path(PACKAGE, row["path"]).read_bytes()) == row["sha256"], "primary body mismatch")
        require(sha(safe_path(PACKAGE, row["reading_view"]).read_bytes()) == row["view_sha256"], "primary view mismatch")
    freeze = json.loads((PACKAGE / "scope-freeze.json").read_bytes())
    require(freeze["target"] == "T273NC108" and freeze["sha256"] == SCOPE, "scope receipt changed")
    require(sha((PACKAGE / "public/frozen-target.md").read_bytes()) == SCOPE, "frozen scope changed")
    return {"status": "INTEGRITY_ONLY", "payloads": len(payloads),
            "external_anchors": len(anchors), "pinned_blobs": len(source_rows),
            "complete_tree_entries": len(entries), "selected_family_tex": len(complete_family_tex),
            "successful_primary_bodies": sum("error" not in x for x in primaries),
            "meaning": "Byte/provenance checks only. No proof, contribution, acceptance, or priority gate."}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--expected-sha256", required=True,
                        help="Detached manifest SHA256 obtained outside this package")
    args = parser.parse_args()
    body = safe_path(PACKAGE, "manifest.json").read_bytes()
    require(len(args.expected_sha256) == 64 and sha(body) == args.expected_sha256,
            "detached manifest anchor mismatch")
    print(json.dumps(validate(json.loads(body)), indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
