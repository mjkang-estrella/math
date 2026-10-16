#!/usr/bin/env python3
"""Myeongjin Kang; no affiliation. Original code MIT.

Read-only identity verifier. No external files, network, subprocesses,
mathematical diagnostics, repairs, or acceptance gates are executed.
Supply the detached seal SHA256 from OUTSIDE this directory.
"""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import sys

SCOPE = "dc98c7a1b62d7a44ead17140b057e82fdfc5e42083c01b3f679fcf3782e4345c"
PRIOR = "87339b6771c8e4e08a05f3a346baeb6d0199459618a8a0b46550564e2ed8f482"
STATUS = "UNRESOLVED_FULL_LR_AFTER_TWO_ATTEMPTS"
COMMIT = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"


def need(condition, reason):
    if not condition:
        raise ValueError(reason)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seal-sha256", required=True)
    args = parser.parse_args()
    root = Path(__file__).resolve().parent

    seal_bytes = (root / "seal.json").read_bytes()
    need(sha(seal_bytes) == args.seal_sha256, "external seal anchor mismatch")
    seal = json.loads(seal_bytes)
    manifest_bytes = (root / "manifest.json").read_bytes()
    need(len(manifest_bytes) == seal["manifest_size"], "manifest size")
    need(sha(manifest_bytes) == seal["manifest_sha256"], "manifest hash")
    manifest = json.loads(manifest_bytes)
    need(manifest["format"] == "linear-lr-r2-exact-membership-v1", "manifest format")
    need(manifest["owned_root"] ==
         "frontier/campaigns/2026-10-14/linear-ryser-r2", "owned root identity")
    need(manifest["metadata"] == ["manifest.json", "seal.json"], "metadata membership")
    need(seal["status"] == STATUS and seal["scope_sha256"] == SCOPE,
         "seal scope/status")

    actual_files = set()
    actual_dirs = {"."}
    for path in root.rglob("*"):
        need(not path.is_symlink(), "symlink rejected")
        rel = path.relative_to(root).as_posix()
        if path.is_file():
            actual_files.add(rel)
        elif path.is_dir():
            actual_dirs.add(rel)
        else:
            need(False, "special filesystem entry")

    entries = manifest["files"]
    names = [entry["path"] for entry in entries]
    need(len(set(names)) == len(names), "duplicate manifest paths")
    for name in names:
        p = PurePosixPath(name)
        need(not p.is_absolute() and ".." not in p.parts and str(p) == name
             and name not in ("", "."), "noncanonical payload path")
    need(actual_files == set(names) | set(manifest["metadata"]),
         "exact file membership")
    need(len(set(manifest["directories"])) == len(manifest["directories"]),
         "duplicate directory names")
    need(actual_dirs == set(manifest["directories"]), "exact directory membership")
    directory_roles = {d: ("inputs" if d == "inputs" or d.startswith("inputs/")
                           else "mixed" if d == "." else "outputs")
                       for d in actual_dirs}
    need(manifest["directory_roles"] == directory_roles, "directory roles")
    need(len(actual_files) == seal["owned_files"], "sealed file count")
    need(len(actual_dirs) == seal["owned_directories"], "sealed directory count")

    roles = {"inputs": {"files": 0, "bytes": 0},
             "outputs": {"files": 0, "bytes": 0}}
    for entry in entries:
        data = (root / entry["path"]).read_bytes()
        need(len(data) == entry["size"], "size: " + entry["path"])
        need(sha(data) == entry["sha256"], "hash: " + entry["path"])
        expected_role = ("inputs" if entry["path"].startswith("inputs/")
                         or entry["path"] == "original-scope.md" else "outputs")
        need(entry["role"] == expected_role, "role: " + entry["path"])
        roles[expected_role]["files"] += 1
        roles[expected_role]["bytes"] += len(data)
    need(roles == manifest["roles"], "role totals")

    def read_json(name):
        return json.loads((root / name).read_bytes())

    need(sha((root / "original-scope.md").read_bytes()) == SCOPE, "scope bytes")
    status = read_json("status.json")
    need(status["status"] == STATUS and status["scope_sha256"] == SCOPE,
         "research status/scope")
    need(status["counted"] is False and status["newAccepted"] == 4
         and status["independent_pass"] is False
         and status["witness"] is False and status["universal_refutation"] is False,
         "no mathematical acceptance or count claim")
    need(status["upstream_commit"] == COMMIT and
         read_json("inputs/context/upstream.json")["commit"] == COMMIT,
         "pinned upstream identity")

    prior = read_json("inputs/r15-authentication.json")
    need(prior["external_anchor"] == PRIOR, "historical external anchor")
    need(len(prior["files"]) == 39 and len(prior["directories"]) == 5,
         "historical exact-membership receipt counts")
    need(prior["bytes"] == sum(v["size"] for v in prior["files"]),
         "historical byte total")
    old_scope = [v for v in prior["files"] if v["path"] == "original-scope.md"]
    need(len(old_scope) == 1 and old_scope[0]["sha256"] == SCOPE,
         "historical scope receipt")

    pins = read_json("inputs/pinned-records.json")
    tree = read_json("inputs/tree-membership.json")
    need(tree["truncated"] is False and tree["total_entries"] == 13223,
         "historical full-tree receipt")
    tree_blobs = {v["path"]: v["sha"] for v in tree["entries"]}
    need(len(pins) == 3 and len(tree_blobs) == 3, "pinned source membership")
    for record in pins:
        data = (root / record["local"]).read_bytes()
        blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        need(len(data) == record["size"] and sha(data) == record["sha256"],
             "pinned byte receipt")
        need(blob == record["git_blob"] == tree_blobs[record["path"]],
             "pinned Git blob")

    for record in read_json("inputs/primary-records.json"):
        data = (root / record["local"]).read_bytes()
        need(len(data) == record["size"] and sha(data) == record["sha256"],
             "primary reading-copy receipt")
    for record in read_json("inputs/context-records.json"):
        data = (root / record["snapshot"]).read_bytes()
        need(len(data) == record["size"] and sha(data) == record["sha256"],
             "internal context snapshot receipt")

    receipts = read_json("unchanged-source-receipts.json")
    need(receipts["all_fixed_unchanged"] is True and
         receipts["fixed_count"] == len(receipts["fixed_files"]),
         "historical unchanged-source receipt")
    for record in receipts["fixed_files"]:
        need(record["unchanged"] is True and record["before"] == record["after"],
             "historical source equality")
    need(receipts["mutable_ledger"]["future_verification_dependency"] is False,
         "mutable ledger dependency forbidden")

    print(json.dumps({"result": "INTEGRITY_OK_ONLY", "research_status": STATUS,
                      "owned_files": len(actual_files),
                      "owned_directories": len(actual_dirs),
                      "payload_bytes": sum(e["size"] for e in entries),
                      "roles": roles, "pinned_blobs": len(pins),
                      "files_written": 0, "live_external_files_read": 0,
                      "mathematical_program_run": False}, sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError, OSError, TypeError) as error:
        print("INTEGRITY_REJECT: " + str(error), file=sys.stderr)
        sys.exit(1)
