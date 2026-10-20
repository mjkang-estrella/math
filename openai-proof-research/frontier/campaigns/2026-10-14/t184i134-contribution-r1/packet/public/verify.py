#!/usr/bin/env python3
"""Read-only verifier for the T184I134 contribution-review root.

Usage:
  python3 -B verify.py --root <review root> --project <openai-proof-research> \
      --final <FINAL.json sha256> --manifest <packet/MANIFEST.json sha256> --report <REPORT.md sha256>

The three anchors must be supplied explicitly (detached). Nothing is written.
"""
import argparse, hashlib, json, os, sys
from pathlib import Path


def sha256(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def blob_sha1(data: bytes) -> str:
    return hashlib.sha1(b"blob %d\0" % len(data) + data).hexdigest()


def main() -> int:
    ap = argparse.ArgumentParser()
    for k in ("root", "project", "final", "manifest", "report"):
        ap.add_argument("--" + k, required=True)
    a = ap.parse_args()
    root, project = Path(a.root), Path(a.project)
    errs = []

    def need(cond, msg):
        if not cond:
            errs.append(msg)

    final_p, man_p, rep_p = root / "FINAL.json", root / "packet/MANIFEST.json", root / "REPORT.md"
    for p in (final_p, man_p, rep_p):
        if not p.is_file() or p.is_symlink():
            print(f"FAIL missing or symlink {p}")
            return 1
    need(sha256(final_p) == a.final, "FINAL.json anchor mismatch")
    need(sha256(man_p) == a.manifest, "MANIFEST anchor mismatch")
    need(sha256(rep_p) == a.report, "REPORT anchor mismatch")
    final = json.loads(final_p.read_bytes())
    need(final.get("manifest_sha256") == a.manifest, "FINAL manifest field mismatch")
    need(final.get("report_sha256") == a.report, "FINAL report field mismatch")
    need(final.get("verdict") == "TECHNICAL", "FINAL verdict field changed")

    man = json.loads(man_p.read_bytes())
    listed = {}
    for e in man["files"]:
        p = root / "packet" / e["path"]
        listed[e["path"]] = e
        if not p.is_file() or p.is_symlink():
            errs.append(f"missing or symlink {e['path']}")
            continue
        need(p.stat().st_size == e["size"], f"size mismatch {e['path']}")
        need(sha256(p) == e["sha256"], f"hash mismatch {e['path']}")
    actual = set()
    for dp, dn, fn in os.walk(root / "packet"):
        for f in fn:
            rel = (Path(dp) / f).relative_to(root / "packet").as_posix()
            if rel != "MANIFEST.json":
                actual.add(rel)
    need(actual == set(listed), f"packet file set differs: extra={sorted(actual - set(listed))} missing={sorted(set(listed) - actual)}")
    for key, rel in (("review_sha256", "public/review.md"), ("reading_limits_sha256", "public/reading-limits.md")):
        need(rel in listed and final.get(key) == listed[rel]["sha256"], f"FINAL {key} mismatch")
    report_text = rep_p.read_text()
    need(a.manifest in report_text, "REPORT does not cite MANIFEST")

    # pinned sources: Git blob SHA-1 against the complete tree
    tree = json.loads((project / "sources/preprints-tree.json").read_bytes())
    need(tree.get("truncated") is False and len(tree["tree"]) == 13223, "tree not complete")
    blobs = {e["path"]: e["sha"] for e in tree["tree"] if e["type"] == "blob"}
    rec = json.loads((root / "packet/private/source/receipts.json").read_bytes())
    for e in rec["files"]:
        p = root / "packet/private/source" / e["path"]
        need(p.is_file() and blob_sha1(p.read_bytes()) == e["git_blob_sha1"] == blobs.get(e["path"]), f"source blob mismatch {e['path']}")
    prim = json.loads((root / "packet/private/primary/receipts.json").read_bytes())
    for name, e in prim["files"].items():
        d = root / "packet/private/primary"
        need((d / name).is_file() and sha256(d / name) == e["sha256"], f"primary mismatch {name}")
        need((d / e["text"]).is_file() and sha256(d / e["text"]) == e["text_sha256"], f"primary text mismatch {e['text']}")

    # stable inputs and immutable author anchors
    inp = json.loads((root / "packet/public/inputs.json").read_bytes())
    for rel, h in inp["project_files"].items():
        p = project / rel
        need(p.is_file() and sha256(p) == h, f"input changed {rel}")
    aroot = project / inp["author_anchors"]["root"]
    for rel, h in inp["author_anchors"].items():
        if rel == "root":
            continue
        p = aroot / rel
        need(p.is_file() and sha256(p) == h, f"author anchor mismatch {rel}")

    if errs:
        for e in errs:
            print("FAIL", e)
        return 1
    print(f"REVIEW_ARTIFACTS_VERIFIED packet_files={len(listed)} sources={len(rec['files'])} primaries={len(prim['files'])}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
