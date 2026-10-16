#!/usr/bin/env python3
# Copyright 2026 Myeongjin Kang. MIT License.
"""Verify public payload, optional internal frozen inputs, and archive boundary."""
import argparse
import hashlib
import json
from pathlib import Path
import zipfile

ROOT = Path(__file__).resolve().parents[1]


def digest(data):
    return hashlib.sha256(data).hexdigest()


def check_entries(entries, key="path"):
    for entry in entries:
        file = ROOT / entry[key]
        data = file.read_bytes()
        assert len(data) == entry["bytes"] and digest(data) == entry["sha256"], file


def contract_path(source):
    old = source["path"]
    if "/build/sections/" in old:
        paper = old.split("/build/sections/")[0].split("/")[-1]
        return ROOT / "inputs/pinned" / paper / Path(old).name
    if old.endswith("i21-signed-saxl-dominance.md"):
        return ROOT / "inputs/provenance/i21-signed-saxl-dominance.md"
    return ROOT / old


def input_audit(write=False):
    manifest = json.loads((ROOT / "input-manifest.json").read_text())
    check_entries(manifest["inputs"], "snapshot")
    contracts = json.loads((ROOT / "inputs/provenance/source-contracts.json").read_text())
    slices = []
    for contract in contracts["contracts"]:
        source = contract["source"]
        file = contract_path(source)
        raw = file.read_bytes()
        assert digest(raw) == source["file_sha256"], file
        lines = raw.decode().splitlines(keepends=True)
        selected = "".join(lines[source["start_line"] - 1:source["end_line"]]).encode()
        assert digest(selected) == source["slice_sha256"], contract["id"]
        slices.append({"id": contract["id"], "path": str(file.relative_to(ROOT)),
                       "lines": [source["start_line"], source["end_line"]],
                       "slice_sha256": digest(selected), "status": "PASS"})
    result = {"input_entries_verified": len(manifest["inputs"]),
              "input_manifest_sha256": digest((ROOT / "input-manifest.json").read_bytes()),
              "source_contracts_verified": len(slices), "source_slices": slices,
              "frozen_inputs_modified": False, "status": "PASS"}
    if write:
        (ROOT / "checks/input-audit.json").write_text(json.dumps(result, indent=2) + "\n")
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--with-inputs", action="store_true")
    parser.add_argument("--audit-inputs-only", action="store_true")
    args = parser.parse_args()
    if args.audit_inputs_only:
        result = input_audit(write=True)
        print("PASS:", result["input_entries_verified"], "frozen inputs;", result["source_contracts_verified"], "contract slices")
        return
    public = json.loads((ROOT / "public-files.json").read_text())["files"]
    assert len(public) == len(set(public))
    for path in public:
        assert not path.startswith("inputs/") and ".." not in Path(path).parts
    manifest = json.loads((ROOT / "public-manifest.json").read_text())
    assert public == [entry["path"] for entry in manifest["files"]]
    check_entries(manifest["files"])
    archive = ROOT / "staircase-manuscript-public.zip"
    if archive.exists():
        with zipfile.ZipFile(archive) as z:
            assert z.namelist() == public + ["public-manifest.json"]
            for entry in manifest["files"]:
                data = z.read(entry["path"])
                assert digest(data) == entry["sha256"] and len(data) == entry["bytes"]
            assert z.read("public-manifest.json") == (ROOT / "public-manifest.json").read_bytes()
    outputs = ROOT / "output-manifest.json"
    if outputs.exists():
        check_entries(json.loads(outputs.read_text())["files"])
    sums = ROOT / "SHA256SUMS"
    if sums.exists():
        for line in sums.read_text().splitlines():
            expected, path = line.split("  ", 1)
            assert digest((ROOT / path).read_bytes()) == expected, path
    if args.with_inputs:
        input_audit()
    print("PASS: all frozen payload hashes and public ZIP allowlist; inputs excluded")


if __name__ == "__main__":
    main()
