#!/usr/bin/env python3
"""AGM063 contribution review r1: read-only identity verifier.

It checks bytes and membership only. It does not check the proof, the
contribution verdict or acceptance. Every anchor is supplied by the caller.
"""
import argparse
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import sys

PIN = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"
ROOT = Path(__file__).resolve().parent
AUTHOR = ROOT.parent / "fresh-arithmetic-discovery-r18"
REPO = ROOT.parents[3]
FAMILY = "preprints/The-Generalized-Mukai-Conjecture-September-24-2026/"
# Control transcripts are written after sealing. They are exempt from the
# manifest by exact name only; their contents are not bound.
CONTROL_NAMES = {
    "controls/" + n + ".txt" for n in (
        "positive", "wrong-review-manifest", "wrong-author-manifest",
        "wrong-author-proof", "wrong-author-scope", "wrong-author-checkpoint")
}


def fail(msg):
    raise ValueError(msg)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def check_hex(label, value):
    if re.fullmatch(r"[0-9a-f]{64}", value) is None:
        fail("malformed anchor: " + label)


def safe(base, name):
    p = PurePosixPath(name)
    if (not isinstance(name, str) or p.is_absolute() or not p.parts
            or any(x in (".", "..") for x in p.parts) or str(p) != name):
        fail("unsafe path: " + repr(name))
    return base.joinpath(*p.parts)


def walk(base, exempt=frozenset()):
    files, dirs = set(), set()
    for p in base.rglob("*"):
        if p.is_symlink():
            fail("symlink: " + str(p))
        rel = p.relative_to(base).as_posix()
        if p.is_dir():
            dirs.add(rel)
        elif p.is_file():
            if rel != "manifest.json" and rel not in exempt:
                files.add(rel)
        else:
            fail("special file: " + rel)
    return files, dirs


def exact(expected, actual, what):
    if expected != actual:
        fail(what + " membership mismatch: missing=%s extra=%s"
             % (sorted(expected - actual), sorted(actual - expected)))


def verify_rows(base, rows, fields):
    for row in rows:
        if set(row) != fields:
            fail("unexpected record fields")
        p = safe(base, row["path"])
        if p.stat().st_size != row["bytes"] or sha(p) != row["sha256"]:
            fail("byte identity mismatch: " + row["path"])


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    for label in ("manifest", "author-manifest", "author-proof",
                  "author-scope", "author-checkpoint"):
        ap.add_argument("--" + label + "-sha256", required=True)
    a = ap.parse_args()
    supplied = {
        "manifest": a.manifest_sha256, "author_manifest": a.author_manifest_sha256,
        "author_proof": a.author_proof_sha256, "author_scope": a.author_scope_sha256,
        "author_checkpoint": a.author_checkpoint_sha256,
    }
    for k, v in supplied.items():
        check_hex(k, v)

    # 1. Own review packet.
    if sha(ROOT / "manifest.json") != supplied["manifest"]:
        fail("external review manifest anchor mismatch")
    own = json.loads((ROOT / "manifest.json").read_text())
    if set(own) != {"schema", "pin", "verdict", "author_anchors",
                    "author_verify_sha256", "files", "directories"}:
        fail("unexpected review manifest schema")
    if own["schema"] != "agm063-contribution-r1-v1" or own["pin"] != PIN:
        fail("wrong schema or pin")
    names = [r["path"] for r in own["files"]]
    if names != sorted(set(names)):
        fail("duplicate or unsorted review files")
    files, dirs = walk(ROOT, CONTROL_NAMES)
    exact(set(names), files, "review file")
    exact(set(own["directories"]), dirs - {"controls"}, "review directory")
    verify_rows(ROOT, own["files"], {"path", "bytes", "sha256"})

    # 2. The caller's author anchors must equal the ones sealed in this review.
    for key in ("manifest", "proof", "scope", "checkpoint"):
        if own["author_anchors"][key] != supplied["author_" + key]:
            fail("author %s anchor differs from review-sealed value" % key)

    # 3. Frozen author packet, re-verified independently and without running its code.
    for name, key in (("manifest.json", "author_manifest"), ("proof.md", "author_proof"),
                      ("fixed-scope.md", "author_scope"), ("checkpoint.md", "author_checkpoint")):
        if sha(AUTHOR / name) != supplied[key]:
            fail("external author anchor mismatch: " + name)
    if sha(AUTHOR / "verify.py") != own["author_verify_sha256"]:
        fail("author verify.py differs")
    inv = json.loads((AUTHOR / "manifest.json").read_text())
    if inv.get("pin") != PIN or inv.get("schema") != "arithmetic-r18-v1":
        fail("author schema or pin")
    afiles, adirs = walk(AUTHOR)
    exact({r["path"] for r in inv["files"]}, afiles, "author file")
    exact(set(inv["directories"]), adirs, "author directory")
    verify_rows(AUTHOR, inv["files"], {"path", "bytes", "sha256"})

    # 4. Cross-check against the repository's complete tree (not the truncated tree.json).
    for rel in ("sources/preprints-tree.json", "sources/upstream.json"):
        if (REPO / rel).read_bytes() != (AUTHOR / "private/context" / rel).read_bytes():
            fail("author context copy differs from repository " + rel)
    if json.loads((REPO / "sources/upstream.json").read_text())["commit"] != PIN:
        fail("repository pin differs")
    tree = json.loads((REPO / "sources/preprints-tree.json").read_text())
    if tree.get("truncated") is not False:
        fail("repository preprint tree truncated")
    blobs = {e["path"]: e["sha"] for e in tree["tree"]
             if e["type"] == "blob" and e["path"].startswith(FAMILY)}
    receipts = json.loads((AUTHOR / "receipts.json").read_text())
    seen = set()
    for row in receipts:
        b = safe(AUTHOR, row["path"]).read_bytes()
        g = hashlib.sha1(b"blob " + str(len(b)).encode() + b"\0" + b).hexdigest()
        if g != blobs.get(row["upstream_path"]) or g != row["git_blob_sha1"]:
            fail("pinned Git blob mismatch: " + row["upstream_path"])
        seen.add(row["upstream_path"])
    text_blobs = {p for p in blobs if p.endswith((".tex", ".bib", ".md"))}
    exact(text_blobs, seen, "family063 text blob")
    for row in json.loads((AUTHOR / "primary-receipts.json").read_text()):
        if sha(safe(AUTHOR, row["pdf"])) != row["sha256"]:
            fail("primary PDF mismatch")

    # 5. Non-mutating self-test of both membership-rejection branches.
    probe = set(names)
    for sim in (probe | {"__extra__"}, probe - {names[0]}):
        try:
            exact(probe, sim, "selftest")
        except ValueError:
            continue
        fail("membership selftest did not reject")

    print(json.dumps({
        "status": "IDENTITY_PASS_ONLY", "review_files": len(names),
        "author_files": len(inv["files"]), "author_directories": len(adirs),
        "family063_text_blobs": len(seen),
        "family063_blobs_in_tree": len(blobs),
        "verdict_recorded": own["verdict"], "verdict_checked": False,
        "control_transcripts_bound": False, "writes": 0, "count_change": 0,
    }, sort_keys=True))


if __name__ == "__main__":
    try:
        main()
    except Exception as exc:  # noqa: BLE001 - every failure must reject
        print("VERIFY_FAIL: " + str(exc), file=sys.stderr)
        sys.exit(1)
