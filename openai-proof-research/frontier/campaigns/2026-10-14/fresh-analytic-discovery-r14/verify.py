#!/usr/bin/env python3
"""Read-only PCW package verifier. Copyright 2026 Myeongjin Kang; MIT.

Requires a detached external SHA256 anchor. No payload JSON is parsed until
the seal and then its manifest have been authenticated. No live ledger or
historical program is a verification dependency. Integrity is not mathematics.
"""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat


class Rejected(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise Rejected(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def unique_object(pairs):
    out = {}
    for key, value in pairs:
        require(key not in out, "duplicate JSON object key")
        out[key] = value
    return out


def parse(data):
    return json.loads(data, object_pairs_hook=unique_object)


def canonical(path):
    require(isinstance(path, str) and bool(path), "empty/nonstring path")
    require(re.fullmatch(r"[A-Za-z0-9_./()-]+", path) is not None,
            "noncanonical path alphabet")
    require(not path.startswith("/") and not path.endswith("/"),
            "absolute/trailing-slash path")
    parts = path.split("/")
    require(all(p not in ("", ".", "..") for p in parts),
            "noncanonical path component")
    require(str(PurePosixPath(path)) == path, "normalized path alias")
    require("__pycache__" not in parts and
            not path.endswith((".pyc", ".pyo")), "bytecode rejected")
    return path


def entries(records):
    require(isinstance(records, list), "file records must be a list")
    found = {}
    for record in records:
        require(isinstance(record, dict) and
                set(record) == {"path", "size", "sha256", "role"},
                "invalid file record")
        name = canonical(record["path"])
        require(name not in found, "duplicate manifest path")
        require(type(record["size"]) is int and record["size"] >= 0,
                "invalid byte size")
        require(isinstance(record["sha256"], str) and
                re.fullmatch(r"[0-9a-f]{64}", record["sha256"]) is not None,
                "invalid digest")
        require(record["role"] in ("input-third-party", "input-provenance",
                                   "output-original", "output-code"),
                "invalid role")
        found[name] = record
    require(list(found) == sorted(found), "unsorted manifest")
    return found


def match_bytes(data, record):
    require(len(data) == record["size"] and sha(data) == record["sha256"],
            "size/hash mismatch: " + record["path"])


def actual_members(root):
    require(not root.is_symlink(), "symlink package root")
    files, directories = set(), set()
    for here, dirs, names in os.walk(root, followlinks=False):
        base = Path(here)
        for name in dirs:
            path = base / name
            rel = canonical(path.relative_to(root).as_posix())
            require(stat.S_ISDIR(path.lstat().st_mode), "symlink/special directory")
            directories.add(rel)
        for name in names:
            path = base / name
            rel = canonical(path.relative_to(root).as_posix())
            require(stat.S_ISREG(path.lstat().st_mode), "symlink/special file")
            files.add(rel)
    return files, directories


def same_members(actual_files, actual_dirs, wanted_files, wanted_dirs):
    require(actual_files == wanted_files, "unlisted/missing file")
    require(actual_dirs == wanted_dirs, "unlisted/missing directory")


def authenticate(root, anchor):
    require(re.fullmatch(r"[0-9a-f]{64}", anchor) is not None,
            "external SHA256 anchor required")
    seal_path = root / "seal.json"
    require(stat.S_ISREG(seal_path.lstat().st_mode), "nonregular seal")
    seal_bytes = seal_path.read_bytes()
    # Authentication boundary: no JSON payload has been parsed above.
    require(sha(seal_bytes) == anchor, "external seal anchor mismatch")
    seal = parse(seal_bytes)
    require(set(seal) == {"schema", "manifest", "scope_sha256"} and
            seal["schema"] == "PCW-private-research-seal-v1", "invalid seal")
    m = seal["manifest"]
    require(set(m) == {"path", "size", "sha256"} and
            canonical(m["path"]) == "manifest.json", "invalid manifest binding")
    manifest_path = root / m["path"]
    require(stat.S_ISREG(manifest_path.lstat().st_mode), "nonregular manifest")
    manifest_bytes = manifest_path.read_bytes()
    match_bytes(manifest_bytes, m)
    manifest = parse(manifest_bytes)
    require(set(manifest) == {"schema", "files", "directories"} and
            manifest["schema"] == "PCW-exact-inventory-v1", "invalid manifest")
    records = entries(manifest["files"])
    dirs = manifest["directories"]
    require(isinstance(dirs, list) and all(isinstance(p, str) for p in dirs),
            "invalid directory inventory")
    require(dirs == sorted(set(dirs)), "duplicate/unsorted directory paths")
    for p in dirs:
        canonical(p)
    require(not set(records).intersection({"manifest.json", "seal.json"}),
            "self-referential inventory")
    require(not set(records).intersection(dirs), "file/directory collision")
    wanted = set(records) | {"manifest.json", "seal.json"}
    actual_files, actual_dirs = actual_members(root)
    same_members(actual_files, actual_dirs, wanted, set(dirs))
    payload = {}
    for name, record in records.items():
        data = (root / name).read_bytes()
        match_bytes(data, record)
        payload[name] = data
    # Every payload byte is authenticated before semantic payload parsing.
    return seal, records, payload, actual_files, actual_dirs


def semantics(seal, payload):
    status = parse(payload["status.json"])
    require(status["target"] == "PCW" and
            status["mathematics_status"] == "FULL_PROOF_PROPOSED" and
            status["independent_proof_verdict"] is None and
            status["independent_contribution_verdict"] is None and
            status["counted"] is False and status["campaign_accepted"] == 4,
            "counterfeit verdict/count")
    require(status["author"] == "Myeongjin Kang" and
            status["affiliation"] is None, "author metadata")
    require(all(status[k] is False for k in
                ("manuscript", "formalization", "publication", "subagents",
                 "numerical_experiments", "historical_mathematical_programs_executed")),
            "scope/status metadata")
    scope_hash = sha(payload["original-scope.md"])
    freeze = parse(payload["freeze-record.json"])
    require(scope_hash == seal["scope_sha256"] ==
            status["original_scope_sha256"] == freeze["scope_sha256"],
            "frozen scope mismatch")
    upstream = parse(payload["inputs/context/upstream.json"])
    pinned_commit = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"
    require(upstream["commit"] == pinned_commit == status["source_commit"],
            "source revision mismatch")
    tree = parse(payload["inputs/context/preprints-tree.json"])
    require(tree["truncated"] is False and len(tree["tree"]) == 13223,
            "incomplete source catalogue")
    catalogue = {}
    for item in tree["tree"]:
        name = canonical(item["path"])
        require(name not in catalogue, "duplicate catalogue path")
        catalogue[name] = item
    sources = parse(payload["inputs/source-authentication.json"])
    require(sources["commit"] == pinned_commit and
            sources["catalogue_entries"] == 13223 and
            sources["truncated"] is False, "source receipt identity")
    seen = set()
    for record in sources["records"]:
        path = canonical(record["path"])
        require(path not in seen, "duplicate source record")
        seen.add(path)
        data = payload[path]
        match_bytes(data, record)
        entry = catalogue[canonical(record["upstream_path"])]
        git = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        require(entry["type"] == "blob" and entry["size"] == len(data) and
                entry["sha"] == record["git_blob"] == git,
                "pinned Git blob mismatch")
        require(record["url"] == "https://raw.githubusercontent.com/openai/math/" +
                pinned_commit + "/" + record["upstream_path"], "unpinned source URL")
    require(len(seen) == 15, "unexpected source count")
    context = parse(payload["inputs/context-receipt-before.json"])
    for record in context:
        data = payload[canonical(record["snapshot"])]
        require(len(data) == record["size"] and sha(data) == record["sha256"],
                "internal context snapshot mismatch")
    # No live external path in a receipt is followed.
    return len(seen)


def controls(records, payload, files, dirs):
    passed = []

    def rejects(label, callback):
        try:
            callback()
        except Rejected:
            passed.append(label)
        else:
            raise Rejected("negative control failed: " + label)

    for p in ("../a", "a//b", "./a", "/a", "a/", "a\\b", "a/__pycache__/x"):
        rejects("noncanonical:" + p, lambda p=p: canonical(p))
    sample = list(records.values())
    rejects("duplicate-path", lambda: entries(sample + [sample[0]]))
    rejects("unlisted-file", lambda: same_members(files | {"unlisted"}, dirs, files, dirs))
    rejects("unlisted-directory", lambda: same_members(files, dirs | {"unlisted"}, files, dirs))
    name = "original-scope.md"
    rejects("changed-scope-byte", lambda: match_bytes(payload[name] + b"\n", records[name]))
    rejects("duplicate-json-key", lambda: parse(b'{"x":1,"x":2}'))
    return passed


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--anchor", required=True)
    parser.add_argument("--controls", action="store_true")
    args = parser.parse_args()
    root = Path(__file__).absolute().parent
    seal, records, payload, files, dirs = authenticate(root, args.anchor)
    source_count = semantics(seal, payload)
    tested = controls(records, payload, files, dirs) if args.controls else []
    print(json.dumps({"integrity": "VERIFIED", "files": len(files),
                      "directories": len(dirs), "pinned_blobs": source_count,
                      "negative_controls": tested,
                      "mathematics": "NOT_CERTIFIED",
                      "contribution": "NOT_CERTIFIED"}, sort_keys=True))


if __name__ == "__main__":
    main()
