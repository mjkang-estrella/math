#!/usr/bin/env python3
"""T212M contribution review r1: read-only identity verifier.

Adapted from frontier/campaigns/2026-10-14/agm063-contribution-r1/verify.py
(same author/campaign helper pattern) and the r74 author verify.py lstat walk.
It checks bytes and exact membership only: no proof, no contribution verdict,
no acceptance. Every anchor is supplied by the caller; nothing is written.
"""
import argparse
import hashlib
import json
import os
import re
import stat
import sys
from pathlib import Path, PurePosixPath

PIN = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"
SCHEMA = "t212m-contribution-r1-v1"
ROOT = Path(__file__).absolute().parent
AUTHOR = ROOT.parent / "fresh-analytic-discovery-r74"
# Control transcripts are written after sealing; exempt by exact name only.
CONTROL_CASES = (
    "positive", "wrong-review-manifest", "wrong-author-manifest",
    "wrong-author-proof", "changed-review-file", "missing-review-file",
    "extra-review-file", "extra-review-directory", "symlink-entry",
    "hardlink-entry", "fifo-entry", "changed-author-file", "root-symlink")
CONTROL_NAMES = frozenset("controls/%s.txt" % c for c in CONTROL_CASES)
AUTHOR_ANCHORS = (("manifest", "manifest.json"), ("proof", "candidate-proof.md"),
                  ("scope", "scope-status.json"), ("completion", "author-completion.json"))


def fail(msg):
    raise ValueError(msg)


def sha_bytes(b):
    return hashlib.sha256(b).hexdigest()


def check_hex(label, value):
    if re.fullmatch(r"[0-9a-f]{64}", value) is None:
        fail("malformed anchor: " + label)


def no_symlink_ancestry(path):
    if path.is_symlink() or any(p.is_symlink() for p in path.parents):
        fail("symlink root ancestry")


def safe(base, name):
    p = PurePosixPath(name)
    if (not isinstance(name, str) or p.is_absolute() or not p.parts
            or any(x in (".", "..") for x in p.parts) or str(p) != name):
        fail("unsafe path: " + repr(name))
    return base.joinpath(*p.parts)


def walk(base, exempt=frozenset()):
    """lstat walk: rejects symlinks, nonregular entries and hardlinks."""
    files, dirs = {}, set()
    for top, ds, fs in os.walk(base):
        for name in ds + fs:
            p = Path(top) / name
            s = p.lstat()
            rel = p.relative_to(base).as_posix()
            if stat.S_ISLNK(s.st_mode):
                fail("symlink entry: " + rel)
            if stat.S_ISDIR(s.st_mode):
                dirs.add(rel)
                continue
            if not stat.S_ISREG(s.st_mode):
                fail("nonregular entry: " + rel)
            if s.st_nlink != 1:
                fail("hardlink entry: " + rel)
            if rel != "manifest.json" and rel not in exempt:
                b = p.read_bytes()
                files[rel] = {"bytes": len(b), "sha256": sha_bytes(b)}
    return files, dirs


def exact(expected, actual, what):
    if set(expected) != set(actual):
        fail("%s membership mismatch: missing=%s extra=%s" % (
            what, sorted(set(expected) - set(actual)), sorted(set(actual) - set(expected))))


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--manifest-sha256", required=True)
    for key, _ in AUTHOR_ANCHORS:
        ap.add_argument("--author-%s-sha256" % key, required=True)
    a = vars(ap.parse_args())
    supplied = {"manifest": a["manifest_sha256"]}
    supplied.update({"author_" + k: a["author_%s_sha256" % k] for k, _ in AUTHOR_ANCHORS})
    for k, v in supplied.items():
        check_hex(k, v)

    # 1. Own review packet.
    no_symlink_ancestry(ROOT)
    raw = (ROOT / "manifest.json").read_bytes()
    if sha_bytes(raw) != supplied["manifest"]:
        fail("external review manifest anchor mismatch")
    own = json.loads(raw)
    if set(own) != {"schema", "pin", "verdict", "author_anchors",
                    "author_verify_sha256", "files", "directories"}:
        fail("unexpected review manifest schema")
    if own["schema"] != SCHEMA or own["pin"] != PIN:
        fail("wrong schema or pin")
    rows = own["files"]
    names = [r["path"] for r in rows]
    if names != sorted(set(names)):
        fail("duplicate or unsorted review files")
    files, dirs = walk(ROOT, CONTROL_NAMES)
    exact(names, files, "review file")
    exact(own["directories"], dirs, "review directory")
    for r in rows:
        if set(r) != {"path", "bytes", "sha256"}:
            fail("unexpected record fields")
        safe(ROOT, r["path"])
        if files[r["path"]] != {"bytes": r["bytes"], "sha256": r["sha256"]}:
            fail("review byte mismatch: " + r["path"])

    # 2. Caller's author anchors must equal the review-sealed ones.
    for key, _ in AUTHOR_ANCHORS:
        if own["author_anchors"][key] != supplied["author_" + key]:
            fail("author %s anchor differs from review-sealed value" % key)

    # 3. Frozen author packet, re-verified without running its code.
    no_symlink_ancestry(AUTHOR)
    for key, name in AUTHOR_ANCHORS:
        if sha_bytes((AUTHOR / name).read_bytes()) != supplied["author_" + key]:
            fail("external author anchor mismatch: " + name)
    if sha_bytes((AUTHOR / "verify.py").read_bytes()) != own["author_verify_sha256"]:
        fail("author verify.py differs")
    inv = json.loads((AUTHOR / "manifest.json").read_text())
    afiles, adirs = walk(AUTHOR)
    exact(inv["files"], afiles, "author file")
    exact(inv["directories"], adirs, "author directory")
    for rel, rec in inv["files"].items():
        safe(AUTHOR, rel)
        if afiles[rel] != {"bytes": rec["bytes"], "sha256": rec["sha256"]}:
            fail("author byte mismatch: " + rel)
    if inv.get("accepted") is not False or inv.get("count_change") != 0:
        fail("author status mismatch")

    # 4. Non-mutating self-test of both membership-rejection branches.
    probe = set(names)
    for sim in (probe | {"__extra__"}, probe - {names[0]}):
        try:
            exact(probe, sim, "selftest")
        except ValueError:
            continue
        fail("membership selftest did not reject")

    print(json.dumps({
        "status": "IDENTITY_PASS_ONLY", "review_files": len(names),
        "review_directories": len(dirs), "author_files": len(afiles),
        "author_directories": len(adirs), "verdict_recorded": own["verdict"],
        "verdict_checked": False, "control_transcripts_bound": False,
        "writes": 0, "count_change": 0}, sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except Exception as exc:  # noqa: BLE001 - every failure must reject
        print("VERIFY_FAIL: " + str(exc), file=sys.stderr)
        sys.exit(1)
