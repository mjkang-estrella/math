#!/usr/bin/env python3
"""Read-only sealed-packet verifier. MIT; copyright 2026 Myeongjin Kang.

The required manifest SHA256 must come from the sender's external receipt.
This authenticates bytes and source identities, not mathematical correctness.
"""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath


def require(ok, message):
    if not ok:
        raise ValueError(message)


def sha256(data):
    return hashlib.sha256(data).hexdigest()


def verify(root, anchor):
    require(len(anchor) == 64 and all(c in "0123456789abcdef" for c in anchor),
            "invalid external manifest hash")
    require(not (root / "manifest.json").is_symlink(), "symlink manifest")
    raw = (root / "manifest.json").read_bytes()
    require(sha256(raw) == anchor, "manifest hash mismatch")
    manifest = json.loads(raw)
    require(manifest["format"] == "cs-review-packet-v1", "unknown format")
    records = manifest["files"]
    names = [r["path"] for r in records]
    require(len(names) == len(set(names)), "duplicate payload path")
    for name in names:
        p = PurePosixPath(name)
        require(not p.is_absolute() and ".." not in p.parts
                and str(p) == name and name != "manifest.json", "unsafe path")
    actual_files, actual_dirs = set(), set()
    for path in root.rglob("*"):
        require(not path.is_symlink(), "symlink in packet")
        rel = path.relative_to(root).as_posix()
        if path.is_file():
            actual_files.add(rel)
        elif path.is_dir():
            actual_dirs.add(rel)
        else:
            raise ValueError("nonregular packet entry")
    require(actual_files == set(names) | {"manifest.json"}, "file inventory mismatch")
    require(actual_dirs == set(manifest["directories"]), "directory inventory mismatch")
    payloads = {}
    for r in records:
        data = (root / r["path"]).read_bytes()
        require(len(data) == r["bytes"] and sha256(data) == r["sha256"],
                "payload mismatch: " + r["path"])
        payloads[r["path"]] = data
    # Parse dependent JSON only after all payload hashes are authenticated.
    status = json.loads(payloads["status.json"])
    require(sha256(payloads[status["scope"]]) == status["scope_sha256"], "scope mismatch")
    receipt = json.loads(payloads["source-receipt.json"])
    require(receipt["commit"] == status["pinned_revision"], "revision mismatch")
    for r in receipt["pinned_blobs_verified"]:
        data = payloads[r["local"]]
        git_blob = hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest()
        require(git_blob == r["git_blob"] and sha256(data) == r["sha256"]
                and len(data) == r["bytes"], "source identity mismatch")
    return {"status": "SEALED_BYTES_VERIFIED", "files": len(records),
            "pinned_blobs": len(receipt["pinned_blobs_verified"]),
            "manifest_sha256": anchor, "mathematical_review": "PENDING"}


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--manifest-sha256", required=True)
    args = parser.parse_args()
    try:
        result = verify(Path(__file__).resolve().parent, args.manifest_sha256)
    except (ValueError, KeyError, TypeError, OSError) as error:
        parser.exit(1, "VERIFICATION_FAILED: " + str(error) + "\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
