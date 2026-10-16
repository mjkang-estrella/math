#!/usr/bin/env python3
# Myeongjin Kang; no affiliation. Original code MIT.
"""Read-only artifact verification. Does not prove any mathematical claim."""
import argparse
import hashlib
import json
from pathlib import Path
import sys

META = {"inputs-manifest.json", "outputs-manifest.json", "seal.json", "seal.sha256"}
OLD_ANCHOR = "bcfbac0e38180f79dcb4461dd344ef2888291511c9de914e6a58c625226b7892"
PIN = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"
OLD = "frontier/campaigns/2026-10-14/fresh-analytic-discovery-r10"
HISTORICAL = {
    "frontier/campaigns/2026-10-14/fresh-analytic-discovery-r9":
        "13658895e2242a0eb3ecbed3f1910345666d10afc83de4d32befe9a9647585c4",
    "frontier/campaigns/2026-10-14/fk-stable-cut-proof-r1":
        "ef5a8c05f9dbd183763c87e6474189d01404da2d46b5219bc49156de65d701e8",
    "frontier/campaigns/2026-10-14/fk-stable-cut-contribution-r1":
        "e31a08e0498163b01bad12f87326e42aab80df9a65d9ed14cada9aee19018c81",
}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(data):
    return hashlib.sha256(data).hexdigest()


def safe(base, relative):
    p = Path(relative)
    require(not p.is_absolute() and ".." not in p.parts, "unsafe relative path")
    q = base / p
    require(not any(x.is_symlink() for x in [q, *q.parents]), "symlink path")
    return q


def authenticate(base, record):
    b = safe(base, record["path"]).read_bytes()
    require(len(b) == record["size"], "size mismatch: " + record["path"])
    require(sha(b) == record["sha256"], "hash mismatch: " + record["path"])
    return b


def members(root):
    files, dirs = set(), set()
    for p in root.rglob("*"):
        require(not p.is_symlink(), "symlink member")
        rel = p.relative_to(root).as_posix()
        if p.is_file():
            files.add(rel)
        elif p.is_dir():
            dirs.add(rel)
        else:
            raise ValueError("nonregular member")
    return files, dirs


def anchor_package(repo, path, anchor):
    root = safe(repo, path)
    require(sha((root / "seal.json").read_bytes()) == anchor, "old anchor mismatch")
    require((root / "seal.sha256").read_text() == anchor + "  seal.json\n",
            "old detached seal mismatch")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seal-sha256", required=True)
    parser.add_argument("--repo-root", type=Path)
    parser.add_argument("--require-status", default="UNRESOLVED_FULL_P")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    repo = args.repo_root.resolve() if args.repo_root else root.parents[3]
    raw = (root / "seal.json").read_bytes()
    require(sha(raw) == args.seal_sha256, "external anchor mismatch")
    require((root / "seal.sha256").read_text() == args.seal_sha256 + "  seal.json\n",
            "detached seal mismatch")
    seal = json.loads(raw)
    manifests = {}
    for kind in ("inputs", "outputs"):
        require(seal[kind]["path"] == kind + "-manifest.json", "manifest path mismatch")
        manifests[kind] = json.loads(authenticate(root, seal[kind]))
    ins, outs = manifests["inputs"], manifests["outputs"]
    local = ins["files"] + outs["files"]
    paths = [x["path"] for x in local]
    require(len(paths) == len(set(paths)), "duplicate local member")
    require(all(x["path"].startswith("inputs/") for x in ins["files"]), "input namespace")
    require(not any(x["path"].startswith("inputs/") for x in outs["files"]), "output namespace")
    for r in local:
        authenticate(root, r)
    actual_files, actual_dirs = members(root)
    require(actual_files == set(paths) | META, "exact local file membership mismatch")
    require(actual_dirs == set(ins["directories"]) | set(outs["directories"]),
            "exact local directory membership mismatch")
    external = ins["external_files"]
    require(len({x["path"] for x in external}) == len(external), "duplicate external member")
    for r in external:
        authenticate(repo, r)
    baseline_raw = (root / "external-input-baseline.json").read_bytes()
    baseline = json.loads(baseline_raw)
    require(external == baseline["files"], "external baseline mismatch")
    require(baseline["r10_external_anchor"] == OLD_ANCHOR, "old anchor binding mismatch")
    for group in baseline["exact_groups"]:
        files, _ = members(safe(repo, group["root"]))
        require(files == set(group["members"]), "external exact membership mismatch")
    anchor_package(repo, OLD, OLD_ANCHOR)
    for path, anchor in HISTORICAL.items():
        anchor_package(repo, path, anchor)
    old = repo / OLD
    old_seal = json.loads((old / "seal.json").read_bytes())
    for kind in ("inputs", "outputs"):
        authenticate(old, old_seal[kind])
    tree = json.loads((repo / "sources/preprints-tree.json").read_bytes())
    require(tree["truncated"] is False, "truncated source tree")
    entries = {x["path"]: x for x in tree["tree"] if x["type"] == "blob"}
    retrievals = json.loads((old / "source-retrieval.json").read_bytes())
    for r in retrievals:
        data = authenticate(old, r)
        blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        require(blob == r["git_blob_sha1"] == entries[r["upstream_path"]]["sha"],
                "pinned Git blob mismatch")
        require(r["url"] == "https://raw.githubusercontent.com/openai/math/" + PIN + "/"
                + r["upstream_path"], "pinned URL mismatch")
    require(len(retrievals) == 71, "inherited blob count mismatch")
    require(json.loads((repo / "sources/upstream.json").read_bytes())["commit"] == PIN,
            "source pin mismatch")
    identities = json.loads((root / "source-identities.json").read_bytes())
    require(identities["upstream_commit"] == PIN and len(identities["files"]) == 7,
            "used source identity mismatch")
    for r in identities["files"]:
        data = authenticate(repo, r)
        blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        require(blob == r["git_blob_sha1"] == entries[r["upstream_path"]]["sha"],
                "used source blob mismatch")
    freeze = json.loads((root / "scope-freeze.json").read_bytes())
    scope = authenticate(root, freeze)
    require(scope == (old / "original-scope.md").read_bytes(), "scope changed from r10")
    require(freeze["before_sustained_proof"] and freeze["unchanged_from_r10"], "scope freeze mismatch")
    receipt = json.loads((root / "unchanged-input-receipt.json").read_bytes())
    require(receipt["baseline_sha256"] == sha(baseline_raw), "unchanged receipt binding mismatch")
    require(receipt["all_unchanged"] and receipt["protected_file_records"] == len(external),
            "unchanged receipt mismatch")
    require(receipt["current_records_sha256"] == sha(json.dumps(external, sort_keys=True).encode()),
            "unchanged aggregate mismatch")
    status = json.loads((root / "status.json").read_bytes())
    require(status["status"] == args.require_status, "required mathematical status mismatch")
    require(status["counted"] is False and status["accepted_count"] == 4, "count changed")
    require(seal["mathematical_status"] == "UNRESOLVED_FULL_P"
            and seal["counted"] is False, "seal status mismatch")
    print(json.dumps({"status": "PASS_ARTIFACT_INTEGRITY_ONLY", "mathematics": status["status"],
                      "local_files": len(actual_files), "local_inputs": len(ins["files"]),
                      "local_outputs": len(outs["files"]), "external_files": len(external),
                      "sealed_package_members": [len(g["members"]) for g in baseline["exact_groups"]],
                      "pinned_blobs": len(retrievals), "used_source_sections": 7,
                      "scope_unchanged": True, "protected_inputs_unchanged": True,
                      "mathematical_checker_or_simulation_run": False,
                      "counted": False, "writes": False}, sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except Exception as exc:
        print(json.dumps({"status": "FAIL", "reason": str(exc), "writes": False}, sort_keys=True))
        sys.exit(2)
