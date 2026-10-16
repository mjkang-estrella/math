#!/usr/bin/env python3
# Copyright 2026 Myeongjin Kang. MIT License (see LICENSE-CODE).
"""Recheck the frozen package: public manifest and ZIP, output manifest,
SHA256SUMS, and (with --with-inputs) every input hash in the repository."""
import argparse
import hashlib
import json
from pathlib import Path
import sys
import zipfile

ROOT = Path(__file__).resolve().parents[1]
ZIP_NAME = "kn-minus-edge-manuscript-public.zip"
FAILURES = []


def digest(data):
    return hashlib.sha256(data).hexdigest()


def check(condition, message):
    if not condition:
        FAILURES.append(message)


def check_entries(entries, base):
    for item in entries:
        file = base / item["path"]
        if not file.is_file():
            check(False, f"missing {file}")
            continue
        data = file.read_bytes()
        check(len(data) == item["bytes"] and digest(data) == item["sha256"], f"hash/size mismatch {item['path']}")


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--with-inputs", action="store_true", help="also verify input-manifest.json against the repository")
    args = parser.parse_args()

    public = json.loads((ROOT / "public-files.json").read_text())["files"]
    manifest = json.loads((ROOT / "public-manifest.json").read_text())
    check(public == [item["path"] for item in manifest["files"]], "public manifest differs from allowlist")
    check(not any(p.startswith(("work/", "checks/pages/")) for p in public), "excluded path in allowlist")
    check_entries(manifest["files"], ROOT)
    with zipfile.ZipFile(ROOT / ZIP_NAME) as archive:
        check(archive.namelist() == public + ["public-manifest.json"], "ZIP contents differ from allowlist")
        for item in manifest["files"]:
            data = archive.read(item["path"])
            check(digest(data) == item["sha256"] and len(data) == item["bytes"], f"ZIP member mismatch {item['path']}")
        check(archive.read("public-manifest.json") == (ROOT / "public-manifest.json").read_bytes(), "ZIP manifest differs")
    check_entries(json.loads((ROOT / "output-manifest.json").read_text())["files"], ROOT)
    for line in (ROOT / "SHA256SUMS").read_text().splitlines():
        expected, path = line.split("  ", 1)
        check(digest((ROOT / path).read_bytes()) == expected, f"SHA256SUMS mismatch {path}")
    if args.with_inputs:
        # The package sits at <project>/frontier/campaigns/<date>/<package>/.
        check_entries(json.loads((ROOT / "input-manifest.json").read_text())["inputs"], ROOT.parents[3])

    if FAILURES:
        print("VERIFY FAILED")
        for failure in FAILURES:
            print("  " + failure)
        sys.exit(1)
    print("VERIFY PASSED" + (" (including inputs)" if args.with_inputs else ""))


if __name__ == "__main__":
    main()
