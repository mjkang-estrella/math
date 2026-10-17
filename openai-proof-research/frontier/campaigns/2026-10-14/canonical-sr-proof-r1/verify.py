#!/usr/bin/env python3
"""Read-only review authentication. MIT; copyright 2026 Myeongjin Kang.

Requires the review manifest hash reported separately by the reviewer.
Checks bytes and identities only; it does not prove CS or contribution.
"""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath


def require(condition, message):
    if not condition:
        raise ValueError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def read_json(data):
    def unique(pairs):
        result = {}
        for key, value in pairs:
            require(key not in result, "duplicate JSON key")
            result[key] = value
        return result
    return json.loads(data, object_pairs_hook=unique)


def packet(root, anchor, expected_format):
    require(len(anchor) == 64 and all(c in "0123456789abcdef" for c in anchor),
            "invalid manifest anchor")
    require(not root.is_symlink(), "symlink packet root")
    manifest_path = root / "manifest.json"
    require(not manifest_path.is_symlink(), "symlink manifest")
    raw = manifest_path.read_bytes()
    require(digest(raw) == anchor, "manifest anchor mismatch")
    manifest = read_json(raw)
    require(manifest["format"] == expected_format, "wrong packet format")
    records = manifest["files"]
    names = [r["path"] for r in records]
    require(len(names) == len(set(names)), "duplicate payload path")
    for name in names + manifest["directories"]:
        path = PurePosixPath(name)
        require(name and name != "." and str(path) == name
                and not path.is_absolute() and ".." not in path.parts
                and "\\" not in name and name != "manifest.json",
                "noncanonical payload path")
    actual_files, actual_dirs = set(), set()
    for path in root.rglob("*"):
        require(not path.is_symlink(), "symlink payload")
        rel = path.relative_to(root).as_posix()
        if path.is_file():
            actual_files.add(rel)
        elif path.is_dir():
            actual_dirs.add(rel)
        else:
            raise ValueError("nonregular payload")
    require(actual_files == set(names) | {"manifest.json"}, "file inventory mismatch")
    require(actual_dirs == set(manifest["directories"]), "directory inventory mismatch")
    payloads = {}
    for record in records:
        data = (root / record["path"]).read_bytes()
        require(len(data) == record["bytes"] and digest(data) == record["sha256"],
                "payload mismatch: " + record["path"])
        payloads[record["path"]] = data
    return payloads


def verify(root, anchor):
    own = packet(root, anchor, "cs-independent-proof-r1-v1")
    inputs = read_json(own["inputs.json"])
    require(inputs["author_directory"] == "../fresh-analytic-discovery-r18",
            "unexpected author directory")
    author = packet(root.parent / "fresh-analytic-discovery-r18",
                    inputs["author_manifest_sha256"], "cs-review-packet-v1")
    require(digest(author["candidate.md"]) == inputs["candidate_sha256"],
            "candidate mismatch")
    require(digest(author["original-scope.md"]) == inputs["scope_sha256"],
            "scope mismatch")
    source = read_json(author["source-receipt.json"])
    require(source["commit"] == inputs["pinned_revision"], "revision mismatch")
    for record in source["pinned_blobs_verified"]:
        data = author[record["local"]]
        git_blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        require(git_blob == record["git_blob"] and digest(data) == record["sha256"]
                and len(data) == record["bytes"], "pinned source mismatch")
    scope = read_json(own["scope-check.json"])
    require(scope["candidate_sha256"] == inputs["candidate_sha256"]
            and scope["scope_sha256"] == inputs["scope_sha256"], "review binding mismatch")
    require(scope["verdict"] == "PASS_FULL_CS" and scope["counted"] is False
            and not scope["required_repairs"], "review status mismatch")
    return {"status": "AUTHENTICATED_BYTES_ONLY", "review_payloads": len(own),
            "author_payloads": len(author),
            "pinned_blobs": len(source["pinned_blobs_verified"]),
            "recorded_verdict": scope["verdict"], "counted": False,
            "writes": 0, "mathematical_program_run": False}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest-sha256", required=True)
    args = parser.parse_args()
    try:
        result = verify(Path(__file__).absolute().parent, args.manifest_sha256)
    except (ValueError, TypeError, KeyError, OSError) as error:
        parser.exit(1, "AUTHENTICATION_REJECT: " + str(error) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
