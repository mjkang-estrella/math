#!/usr/bin/env python3
"""Read-only local integrity verifier; explicit detached anchors required."""
import argparse, hashlib, json
from pathlib import Path, PurePosixPath

def sha(data):
    return hashlib.sha256(data).hexdigest()

def main():
    ap = argparse.ArgumentParser()
    for name in ("final", "manifest", "report"):
        ap.add_argument("--" + name + "-sha256", required=True)
    args = ap.parse_args()
    root = Path(__file__).resolve().parent
    def read(rel):
        p = PurePosixPath(rel)
        if p.is_absolute() or ".." in p.parts or str(p) != rel:
            raise ValueError("unsafe path")
        path = root.joinpath(*p.parts)
        if path.is_symlink() or not path.resolve().is_relative_to(root):
            raise ValueError("unsafe resolved path")
        return path.read_bytes()
    anchors = {"packet/FINAL.md": args.final_sha256,
               "packet/MANIFEST.json": args.manifest_sha256,
               "REPORT.md": args.report_sha256}
    for rel, expected in anchors.items():
        if sha(read(rel)) != expected:
            raise ValueError("detached anchor mismatch: " + rel)
    manifest = json.loads(read("packet/MANIFEST.json"))
    entries = manifest["files"]
    names = [e["path"] for e in entries]
    if len(names) != len(set(names)):
        raise ValueError("duplicate entry")
    excluded = set(anchors) | {"ANCHORS.json"}
    actual = {p.relative_to(root).as_posix() for p in root.rglob("*") if p.is_file()}
    if set(names) != actual - excluded:
        raise ValueError("payload membership mismatch")
    for e in entries:
        b = read(e["path"])
        if len(b) != e["bytes"] or sha(b) != e["sha256"]:
            raise ValueError("payload mismatch: " + e["path"])
    detached = json.loads(read("ANCHORS.json"))
    if detached != anchors:
        raise ValueError("detached anchor record mismatch")
    ctl = json.loads(read("private/controls/control.json"))
    lo, hi = ctl["byte_interval"]
    expected = ctl["expected_sha256"]
    if sha(read(ctl["source"])[lo:hi]) != expected:
        raise ValueError("control source mismatch")
    if sha(read(ctl["copied"])) != expected:
        raise ValueError("copied control rejected")
    if sha(read(ctl["changed"])) == expected:
        raise ValueError("changed control falsely accepted")
    print(json.dumps({"integrity": "PASS", "payload_files": len(entries),
                      "copied_control": "accepted", "changed_control": "rejected",
                      "mathematical_gate": False}))

if __name__ == "__main__":
    main()
