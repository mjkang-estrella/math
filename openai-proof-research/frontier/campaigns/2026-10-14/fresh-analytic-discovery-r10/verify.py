#!/usr/bin/env python3
# Original code MIT. Myeongjin Kang; no affiliation.
"""Read-only artifact authentication; proves no mathematical assertion."""
import argparse
import hashlib
import json
from pathlib import Path
import sys

META = {"inputs-manifest.json", "outputs-manifest.json", "seal.json", "seal.sha256"}


def digest(data):
    return hashlib.sha256(data).hexdigest()


def require(test, message):
    if not test:
        raise ValueError(message)


def safe_path(base, relative):
    q = Path(relative)
    require(not q.is_absolute() and ".." not in q.parts, "unsafe relative path")
    result = base / q
    require(not any(p.is_symlink() for p in [result, *result.parents]), "symlink path")
    return result


def authenticate(base, record):
    path = safe_path(base, record["path"])
    data = path.read_bytes()
    require(len(data) == record["size"], "size mismatch: " + str(path))
    require(digest(data) == record["sha256"], "hash mismatch: " + str(path))
    return data


def file_members(root):
    result = set()
    for path in root.rglob("*"):
        require(not path.is_symlink(), "symlink member: " + str(path))
        if path.is_file():
            result.add(path.relative_to(root).as_posix())
    return result


def historical_package(repo, record):
    """Authenticate legacy manifests as data, without executing legacy code."""
    root = safe_path(repo, record["path"])
    raw = (root / "seal.json").read_bytes()
    require(digest(raw) == record["seal_sha256"], "historical anchor mismatch")
    seal = json.loads(raw)
    require((root / "seal.sha256").read_text().strip()
            == record["seal_sha256"] + "  seal.json", "historical detached seal")
    manifests = {}
    for kind in ("inputs", "outputs"):
        name = kind + "-manifest.json"
        data = (root / name).read_bytes()
        if kind in seal:
            bound = seal[kind]
            require(bound["path"] == name, "historical manifest path")
            require(len(data) == bound["size"] and digest(data) == bound["sha256"],
                    "historical manifest binding")
        else:
            require(digest(data) == seal[kind + "_manifest_sha256"],
                    "historical manifest binding")
        manifests[kind] = json.loads(data)
    input_base = safe_path(repo, record["input_base"])
    for item in manifests["inputs"]["files"]:
        authenticate(input_base, item)
    for item in manifests["inputs"].get("external_files", []):
        relative = Path(item["path"]).relative_to(repo)
        authenticate(repo, {**item, "path": relative.as_posix()})
    for item in manifests["outputs"]["files"]:
        authenticate(root, item)
    expected = META | {x["path"] for x in manifests["outputs"]["files"]}
    if input_base == root:
        expected |= {x["path"] for x in manifests["inputs"]["files"]}
    require(file_members(root) == expected, "historical exact membership")
    return len(expected)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--seal-sha256", required=True)
    parser.add_argument("--repo-root", type=Path)
    parser.add_argument("--require-status", default="UNRESOLVED")
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    repo = args.repo_root.resolve() if args.repo_root else root.parents[3]
    raw = (root / "seal.json").read_bytes()
    require(digest(raw) == args.seal_sha256, "external anchor mismatch")
    require((root / "seal.sha256").read_text().strip()
            == args.seal_sha256 + "  seal.json", "detached seal mismatch")
    seal = json.loads(raw)
    manifests = {}
    for kind in ("inputs", "outputs"):
        name = kind + "-manifest.json"
        require(seal[kind]["path"] == name, "manifest path")
        manifests[kind] = json.loads(authenticate(root, seal[kind]))
    inputs, outputs = manifests["inputs"], manifests["outputs"]
    local = inputs["files"] + outputs["files"]
    paths = [x["path"] for x in local]
    require(len(set(paths)) == len(paths), "duplicate inventory member")
    require(all(x.startswith("inputs/") for x in [r["path"] for r in inputs["files"]]),
            "input namespace")
    require(not any(x.startswith("inputs/") for x in [r["path"] for r in outputs["files"]]),
            "output namespace")
    for record in local:
        authenticate(root, record)
    require(file_members(root) == set(paths) | META, "exact local file membership")
    directories = {p.relative_to(root).as_posix() for p in root.rglob("*") if p.is_dir()}
    require(directories == set(inputs["directories"]) | set(outputs["directories"]),
            "exact local directory membership")
    for record in inputs["external_files"]:
        authenticate(repo, record)
    legacy_counts = [historical_package(repo, x) for x in inputs["external_packages"]]
    tree = json.loads((repo / "sources/preprints-tree.json").read_bytes())
    require(tree["truncated"] is False, "truncated source tree")
    entries = {x["path"]: x for x in tree["tree"] if x["type"] == "blob"}
    retrievals = json.loads((root / "source-retrieval.json").read_bytes())
    for record in retrievals:
        data = authenticate(root, record)
        blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        require(blob == record["git_blob_sha1"] == entries[record["upstream_path"]]["sha"],
                "pinned Git blob mismatch")
        require(record["url"] == "https://raw.githubusercontent.com/openai/math/"
                + seal["upstream_commit"] + "/" + record["upstream_path"], "pinned URL")
    pin = json.loads((repo / "sources/upstream.json").read_bytes())
    require(pin["commit"] == seal["upstream_commit"], "upstream commit mismatch")
    freeze = json.loads((root / "scope-freeze.json").read_bytes())
    authenticate(root, freeze)
    require(freeze["before_sustained_proof"] is True, "scope freeze flag")
    status = json.loads((root / "status.json").read_bytes())
    require(status["status"] == args.require_status, "required mathematical status mismatch")
    require(status["counted"] is False and status["accepted_count"] == 4, "count changed")
    print(json.dumps({"status": "PASS_ARTIFACT_INTEGRITY_ONLY", "mathematics": "UNRESOLVED",
                      "local_payloads": len(local), "external_files": len(inputs["external_files"]),
                      "historical_package_members": legacy_counts,
                      "pinned_blobs": len(retrievals), "research_or_legacy_code_executed": False,
                      "writes": False, "counted": False}, sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except Exception as exc:
        print(json.dumps({"status": "FAIL", "reason": str(exc), "writes": False}, sort_keys=True))
        sys.exit(2)
