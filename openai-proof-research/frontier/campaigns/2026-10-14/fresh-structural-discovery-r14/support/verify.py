#!/usr/bin/env python3
# Copyright (c) 2026 Myeongjin Kang. MIT license. Read-only integrity checker.
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys
sys.dont_write_bytecode = True

PIN = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"
SCOPE = "1b6e3b67f7a9ff756eb507a3c8f332048de2cbab0eae5e62b9fe8cd4e0a7e80a"
BRIEF = "56aac13aa84140897d92c4d5904ae5846fc293464511c6c754e496b4a3065931"
META = {"input-manifest.json", "output-manifest.json", "seal.json"}

def require(condition, message):
    if not condition:
        raise ValueError(message)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def main():
    parser = argparse.ArgumentParser(description="Integrity only; no mathematics or live-state reads.")
    parser.add_argument("--seal-sha256", required=True)
    parser.add_argument("--root", type=Path, default=Path(__file__).resolve().parent.parent)
    args = parser.parse_args()
    require(re.fullmatch(r"[0-9a-f]{64}", args.seal_sha256) is not None, "invalid external anchor")
    root = args.root.resolve()
    all_paths = list(root.rglob("*"))
    require(not any(p.is_symlink() for p in all_paths), "symlink in owned package")
    blobs = {p.relative_to(root).as_posix(): p.read_bytes() for p in all_paths if p.is_file()}
    require("seal.json" in blobs, "missing seal")
    require(sha(blobs["seal.json"]) == args.seal_sha256, "external seal anchor mismatch")
    seal = json.loads(blobs["seal.json"])
    require(seal["schema"] == "r14-integrity-v1", "unknown seal schema")
    require(seal["source_commit"] == PIN and seal["scope_sha256"] == SCOPE, "wrong frozen contract")
    require(seal["verdict"] == "UNRESOLVED_FULL_FT2", "wrong research disposition")
    declared = {}
    role_totals = {}
    for role, name in [("inputs", "input-manifest.json"), ("outputs", "output-manifest.json")]:
        meta = seal[role]
        require(meta["manifest"] == name, "wrong manifest path")
        raw = blobs[name]
        require(len(raw) == meta["manifest_size"] and sha(raw) == meta["manifest_sha256"], "manifest changed: " + name)
        manifest = json.loads(raw)
        require(manifest["role"] == role, "wrong manifest role")
        entries = manifest["files"]
        names = [entry["path"] for entry in entries]
        require(names == sorted(set(names)), "unsorted or duplicate membership")
        total = 0
        for entry in entries:
            path = entry["path"]
            parts = Path(path).parts
            require(parts and not Path(path).is_absolute() and ".." not in parts and "." not in parts, "unsafe path")
            require(path not in META and path not in declared, "duplicate or metadata payload")
            is_input = path.startswith("inputs/") or path.startswith("private/")
            require(is_input == (role == "inputs"), "wrong input/output partition")
            require(path in blobs, "missing file: " + path)
            data = blobs[path]
            require(len(data) == entry["size"] and sha(data) == entry["sha256"], "changed file: " + path)
            declared[path] = entry
            total += len(data)
        require(len(entries) == manifest["count"] == meta["count"], "wrong role count")
        require(total == manifest["total_bytes"] == meta["total_bytes"], "wrong role bytes")
        role_totals[role] = {"files": len(entries), "bytes": total}
    require(set(blobs) == set(declared) | META, "exact owned membership mismatch")
    require(sha(blobs["original-scope.md"]) == SCOPE, "scope altered")
    require(sha(blobs["inputs/context/r2-brief.txt"]) == BRIEF, "mandatory continuity altered")
    require(json.loads(blobs["inputs/context/upstream.json"])["commit"] == PIN, "wrong upstream snapshot")
    tree = json.loads(blobs["inputs/context/preprints-tree.json"])
    require(tree["truncated"] is False, "truncated catalogue")
    items = tree["tree"]
    require(len(items) == 13223, "wrong complete tree extent")
    mapping = {item["path"]: item for item in items}
    require(len(mapping) == len(items), "duplicate catalogue paths")
    require(all(re.fullmatch(r"[0-9a-f]{40}", item["sha"]) for item in items), "invalid Git identity")
    pinned = json.loads(blobs["inputs/pinned-records.json"])
    require(len(pinned) == 15 and len({r["path"] for r in pinned}) == 15, "wrong pinned membership")
    for rec in pinned:
        data = blobs[rec["file"]]
        git = hashlib.sha1(b"blob " + str(len(data)).encode("ascii") + b"\0" + data).hexdigest()
        require(git == rec["git_blob"] == mapping[rec["path"]]["sha"], "pinned Git mismatch")
        require(len(data) == rec["size"] == mapping[rec["path"]]["size"], "pinned size mismatch")
        require(sha(data) == rec["sha256"], "pinned SHA256 mismatch")
    for rec in json.loads(blobs["inputs/context/snapshots.json"]):
        data = blobs[rec["snapshot"]]
        require(len(data) == rec["size"] and sha(data) == rec["sha256"], "context snapshot changed")
    for rec in json.loads(blobs["inputs/primary-records.json"])["records"]:
        for item in rec["files"]:
            data = blobs[item["path"]]
            require(len(data) == item["size"] and sha(data) == item["sha256"], "private primary changed")
    receipt = json.loads(blobs["inputs/unchanged-source-receipt.json"])
    require(receipt["future_live_state_bound"] is False, "receipt must not bind live state")
    for rec in receipt["records"]:
        require(sha(blobs[rec["snapshot"]]) == rec["before_sha256"], "receipt baseline not bound")
        require(rec["unchanged_when_checked"] == (rec["before_sha256"] == rec["after_sha256"]), "invalid historical receipt")
    status = json.loads(blobs["status.json"])
    require(status["status"] == "UNRESOLVED_FULL_FT2" and status["scope_sha256"] == SCOPE, "wrong status")
    require(status["counted"] is False and status["campaign_accepted"] == 4, "unauthorized acceptance")
    require(status["full_proof"] is False and status["counterexample_to_assertion"] is False, "unsupported conclusion")
    print(json.dumps({"result": "INTEGRITY_OK_ONLY", "owned_files": len(blobs),
                      "owned_bytes": sum(map(len, blobs.values())), "roles": role_totals,
                      "metadata_files": 3, "pinned_blobs": len(pinned),
                      "research_status": "UNRESOLVED_FULL_FT2", "mathematical_check_executed": False,
                      "live_external_files_read": 0, "files_written": 0}, sort_keys=True))

if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError, OSError, TypeError) as error:
        print("INTEGRITY_REJECT: " + str(error), file=sys.stderr)
        sys.exit(1)
