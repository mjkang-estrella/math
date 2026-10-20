#!/usr/bin/env python3
"""Read-only verifier for the T106O133 contribution review r1.

Usage:
  python -B verify.py --root REVIEW_ROOT --project PROJECT \
      --finalhash DETACHED_FINAL_SHA256 --author-finalhash DETACHED_AUTHOR_FINAL_SHA256

Both hashes must be supplied from a detached source (the parent handoff), not
read from files in the root. The script opens files for reading only and
writes nothing. Exit status 0 means every check passed.

--author-root and --parent-dir exist only so that controls.py can point the
checks at copies; by default they are derived from PROJECT.
"""
import argparse
import hashlib
import json
import os
import sys

sys.dont_write_bytecode = True

PIN = "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"
TREE_SHA256 = "eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b"
CAMPAIGN = "frontier/campaigns/2026-10-14"


def sha256_file(path):
    with open(path, "rb") as fh:
        return hashlib.sha256(fh.read()).hexdigest()


def blob_sha1(data):
    return hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()


def aggregate(root):
    out = {}
    for r, dirs, files in os.walk(root):
        dirs.sort()
        for f in sorted(files):
            p = os.path.join(r, f)
            with open(p, "rb") as fh:
                b = fh.read()
            out[os.path.relpath(p, root)] = [len(b), hashlib.sha256(b).hexdigest()]
    agg = hashlib.sha256(json.dumps(out, sort_keys=True).encode()).hexdigest()
    return len(out), agg


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", required=True)
    ap.add_argument("--project", required=True)
    ap.add_argument("--finalhash", required=True)
    ap.add_argument("--author-finalhash", required=True)
    ap.add_argument("--author-root")
    ap.add_argument("--parent-dir")
    a = ap.parse_args()

    root = os.path.abspath(a.root)
    project = os.path.abspath(a.project)
    author_root = os.path.abspath(a.author_root or os.path.join(
        project, CAMPAIGN, "fresh-structural-discovery-r133"))
    parent_dir = os.path.abspath(a.parent_dir or os.path.join(
        project, CAMPAIGN, "discovery-structural-r133-parent"))
    results = []

    def check(name, ok, detail=""):
        results.append((name, bool(ok), detail))

    def guarded(name, fn):
        try:
            fn()
        except Exception as exc:  # any unreadable or malformed input is a failure
            check(name, False, f"{type(exc).__name__}: {exc}")

    packet = os.path.join(root, "packet")
    final_path = os.path.join(root, "FINAL.json")
    state = {}

    def c_final():
        h = sha256_file(final_path)
        check("final.detached_anchor", h == a.finalhash.lower(), h)
        with open(final_path, "rb") as fh:
            state["final"] = json.loads(fh.read())
        f = state["final"]
        check("final.status", f.get("status") == "SEALED_CONTRIBUTION_REVIEW")
        check("final.pin", f.get("pin") == PIN)
        check("final.no_gate", f.get("assigns") == {
            "correctness_gate": False, "acceptance": False, "count": False})
        for key, rel in [("manifest_sha256", "packet/MANIFEST.json"),
                         ("report_sha256", "REPORT.md"),
                         ("review_sha256", "packet/public/review.md"),
                         ("verdict_sha256", "packet/public/verdict.json"),
                         ("input_fingerprints_sha256", "packet/public/input-fingerprints.json")]:
            check(f"final.binds.{rel}", sha256_file(os.path.join(root, rel)) == f.get(key))
        with open(os.path.join(packet, "public/verdict.json"), "rb") as fh:
            v = json.loads(fh.read())
        check("final.verdict_matches", v.get("verdict") == f.get("verdict") == "TECHNICAL")
        check("final.author_anchor_recorded", f.get("author_final_sha256") == a.author_finalhash.lower())

    def c_manifest():
        with open(os.path.join(packet, "MANIFEST.json"), "rb") as fh:
            m = json.loads(fh.read())
        entries = m["entries"]
        listed_files, listed_dirs, bad = set(), set(), []
        for rel, e in entries.items():
            p = os.path.normpath(os.path.join(packet, rel))
            if e["type"] == "dir":
                listed_dirs.add(os.path.normpath(rel))
                if not os.path.isdir(p):
                    bad.append("missing dir " + rel)
                continue
            listed_files.add(os.path.normpath(rel))
            if not os.path.isfile(p):
                bad.append("missing " + rel)
                continue
            with open(p, "rb") as fh:
                b = fh.read()
            if len(b) != e["bytes"] or hashlib.sha256(b).hexdigest() != e["sha256"]:
                bad.append("mismatch " + rel)
        actual_files, actual_dirs = set(), set()
        for r, dirs, files in os.walk(packet):
            actual_dirs.add(os.path.normpath(os.path.relpath(r, packet)))
            for f in files:
                actual_files.add(os.path.normpath(os.path.relpath(os.path.join(r, f), packet)))
        actual_files.discard("MANIFEST.json")
        extra = sorted(actual_files - listed_files)
        missing = sorted(listed_files - actual_files)
        check("manifest.entries", not bad, "; ".join(bad[:5]))
        check("manifest.closed_files", not extra and not missing, f"extra={extra[:5]} missing={missing[:5]}")
        check("manifest.closed_dirs", actual_dirs == listed_dirs, str(sorted(actual_dirs ^ listed_dirs)[:5]))

    def c_sources():
        tree_path = os.path.join(project, "sources/preprints-tree.json")
        check("source.tree_sha256", sha256_file(tree_path) == TREE_SHA256)
        with open(tree_path, "rb") as fh:
            tree = json.loads(fh.read())
        check("source.tree_complete", tree.get("truncated") is False and len(tree["tree"]) == 13223)
        blobs = {e["path"]: e for e in tree["tree"] if e["type"] == "blob"}
        src = os.path.join(packet, "private/source")
        with open(os.path.join(src, "receipts.json"), "rb") as fh:
            receipts = json.loads(fh.read())
        bad = []
        for r in receipts:
            p = os.path.join(src, r["path"])
            with open(p, "rb") as fh:
                b = fh.read()
            e = blobs.get(r["path"])
            if e is None or blob_sha1(b) != e["sha"] or len(b) != e["size"] \
                    or r["git_blob_sha1"] != e["sha"] or hashlib.sha256(b).hexdigest() != r["sha256"] \
                    or PIN not in r["url"]:
                bad.append(r["path"])
        on_disk = set()
        for rr, dirs, files in os.walk(src):
            for f in files:
                on_disk.add(os.path.relpath(os.path.join(rr, f), src))
        on_disk.discard("receipts.json")
        uncovered = on_disk - {r["path"] for r in receipts}
        check("source.blob_authenticated", not bad, "; ".join(bad[:5]))
        check("source.receipts_cover_all", not uncovered, str(sorted(uncovered)[:5]))

    def c_inputs():
        with open(os.path.join(packet, "public/input-fingerprints.json"), "rb") as fh:
            fp = json.loads(fh.read())
        anchors = fp["author_detached_anchors"]
        check("author.detached_final", sha256_file(os.path.join(author_root, "FINAL.json"))
              == a.author_finalhash.lower() == anchors["FINAL.json"])
        for rel, h in anchors.items():
            check(f"author.anchor.{rel}", sha256_file(os.path.join(author_root, rel)) == h)
        n, agg = aggregate(author_root)
        check("author.root_unchanged", n == fp["author_root"]["files"]
              and agg == fp["author_root"]["aggregate_sha256"], f"{n} {agg}")
        for rel, h in fp["parent_inputs_used"].items():
            p = os.path.join(parent_dir, os.path.basename(rel))
            check(f"parent.input.{os.path.basename(rel)}", sha256_file(p) == h)
        for rel in ("AGENTS.md", "sources/preprints-tree.json", "sources/upstream.json"):
            check(f"project.{rel}", sha256_file(os.path.join(project, rel)) == fp["project_files"][rel])

    guarded("final", c_final)
    guarded("manifest", c_manifest)
    guarded("sources", c_sources)
    guarded("inputs", c_inputs)

    failed = [r for r in results if not r[1]]
    for name, ok, detail in results:
        print(("PASS " if ok else "FAIL ") + name + (f"  [{detail}]" if detail and not ok else ""))
    print(f"{len(results) - len(failed)}/{len(results)} checks passed")
    print("VERIFY " + ("PASS" if not failed and results else "FAIL"))
    print("Artifact checks are not a correctness or contribution judgment.")
    sys.exit(0 if not failed and results else 1)


if __name__ == "__main__":
    main()
