#!/usr/bin/env python3
# SPDX-License-Identifier: MIT
"""Parent identity check; no mathematical diagnostic or truth certification."""
import hashlib
import json
import pathlib
import stat
import subprocess
import sys

PROJECT = pathlib.Path(__file__).resolve().parents[4]
ROOT = PROJECT / "frontier/campaigns/2026-10-14/complex-projector-borsuk-review-r1"
ANCHOR = "c9527d05aff931a233962ef61a0f2de62d962a5fc3375735ac5afdcacdfaaa44"


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def unique(items):
    result = {}
    for key, value in items:
        assert key not in result, key
        result[key] = value
    return result


def read_json(path):
    return json.loads(path.read_bytes(), object_pairs_hook=unique)


def member(root, name):
    p = pathlib.PurePosixPath(name)
    assert name and name != "." and str(p) == name and not p.is_absolute()
    assert ".." not in p.parts and "\\" not in name and ":" not in name
    assert all(ord(c) >= 32 for c in name)
    path = root / p
    for ancestor in path.parents:
        assert not ancestor.is_symlink()
    assert stat.S_ISREG(path.lstat().st_mode) and not path.is_symlink()
    return path


assert digest(ROOT / "seal.json") == ANCHOR
assert (ROOT / "seal.json").stat().st_size == 440
seal = read_json(ROOT / "seal.json")
assert digest(ROOT / "manifest.json") == seal["manifest_sha256"]
assert (ROOT / "manifest.json").stat().st_size == seal["manifest_size"]
manifest = read_json(ROOT / "manifest.json")
expected = {"seal.json", "manifest.json"}
for entry in manifest["files"]:
    name = entry["path"]
    assert name not in expected
    expected.add(name)
    path = member(ROOT, name)
    assert path.stat().st_size == entry["size"] and digest(path) == entry["sha256"]
files, directories = set(), {"."}
for path in ROOT.rglob("*"):
    assert not path.is_symlink()
    rel = path.relative_to(ROOT).as_posix()
    if path.is_dir():
        directories.add(rel)
    else:
        assert stat.S_ISREG(path.lstat().st_mode)
        files.add(rel)
assert files == expected and directories == set(manifest["directories"])
assert len(manifest["directories"]) == len(directories)
assert (len(files), len(directories)) == (30, 5)
baseline = read_json(ROOT / "inputs/fixed-reference-baseline.json")
references = baseline["author_files"] + baseline["fixed_references"]
assert len(references) == 40
protected = {ROOT / name for name in expected}
for entry in references:
    path = member(PROJECT, entry["path"])
    assert path not in protected
    protected.add(path)
    assert path.stat().st_size == entry["size"] and digest(path) == entry["sha256"]
tree = read_json(PROJECT / "sources/preprints-tree.json")
assert tree["truncated"] is False and len(tree["tree"]) == 13223
catalogue = {entry["path"]: entry for entry in tree["tree"]}
assert len(catalogue) == len(tree["tree"])
pins = read_json(ROOT / "inputs/pinned-catalogue-check.json")["pinned"]
assert len(pins) == 14
for entry in pins:
    data = member(PROJECT, entry["local_reference"]).read_bytes()
    blob = hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()
    assert blob == entry["git_blob_sha1"] == catalogue[entry["path"]]["sha"]
    assert len(data) == entry["size"] == catalogue[entry["path"]]["size"]
before = {str(path): digest(path) for path in protected}
runs = []
# verify.py was read in full before this replay. It installs a read-only
# audit hook and executes no payload, subprocess, or network operation.
for name, anchor, code in [("positive", ANCHOR, 0), ("wrong-anchor", "0" * 64, 1)]:
    run = subprocess.run(
        [sys.executable, "-I", "-B", str(ROOT / "verify.py"), "--seal-sha256", anchor],
        capture_output=True, text=True, timeout=60,
    )
    assert run.returncode == code, (name, run.stdout, run.stderr)
    if name == "wrong-anchor":
        assert "external seal anchor mismatch" in run.stderr
    runs.append(dict(name=name, exit_code=run.returncode, stdout=run.stdout, stderr=run.stderr))
assert before == {str(path): digest(path) for path in protected}
print(json.dumps(dict(
    anchor=ANCHOR, seal_size=440, independent_authentication=True,
    owned_files=len(files), owned_directories_including_root=len(directories),
    fixed_external_files=len(references), pinned_blobs=len(pins),
    protected_files=len(protected), all_unchanged_during_verification=True,
    runs=runs, limits="Integrity only; no numerical diagnostic or proof certification."
), indent=2))
