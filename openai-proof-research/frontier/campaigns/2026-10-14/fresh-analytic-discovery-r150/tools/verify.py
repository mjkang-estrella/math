"""Read-only exact-file verifier. Explicit detached envelope anchors are mandatory."""
import argparse
import hashlib
import json
import os
from pathlib import Path, PurePosixPath
import re
import stat
import sys

ENVELOPES = ("FINAL.md", "MANIFEST.json", "REPORT.md")

def sha(raw):
    return hashlib.sha256(raw).hexdigest()

def inventory(root):
    found = {}
    def walk(directory):
        for ent in sorted(os.scandir(directory), key=lambda e: e.name):
            p = Path(ent.path)
            st = ent.stat(follow_symlinks=False)
            if stat.S_ISLNK(st.st_mode):
                raise ValueError("symlink: " + str(p))
            if stat.S_ISDIR(st.st_mode):
                walk(p)
            elif stat.S_ISREG(st.st_mode) and st.st_nlink == 1:
                b = p.read_bytes()
                found[p.relative_to(root).as_posix()] = {
                    "size": len(b), "sha256": sha(b)
                }
            else:
                raise ValueError("nonregular or multiply linked object: " + str(p))
    walk(root)
    return found

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("root")
    for k in ("final", "manifest", "report"):
        ap.add_argument("--" + k + "-sha256", required=True)
    args = ap.parse_args()
    root = Path(args.root)
    if root.is_symlink() or not root.is_dir():
        raise ValueError("root must be a real directory")
    root = root.resolve()
    observed = inventory(root)
    for name, anchor in zip(ENVELOPES, (args.final_sha256, args.manifest_sha256, args.report_sha256)):
        if not re.fullmatch("[0-9a-f]{64}", anchor):
            raise ValueError("invalid explicit anchor: " + name)
        if name not in observed or observed[name]["sha256"] != anchor:
            raise ValueError("detached anchor mismatch: " + name)
    manifest = json.loads((root / "MANIFEST.json").read_text())
    if manifest["version"] != 1 or manifest["envelopes"] != list(ENVELOPES):
        raise ValueError("unsupported manifest envelope schema")
    expected = {}
    for row in manifest["files"]:
        name = row["path"]
        p = PurePosixPath(name)
        if p.is_absolute() or ".." in p.parts or p.as_posix() != name or name in ENVELOPES:
            raise ValueError("invalid payload path: " + name)
        if name in expected:
            raise ValueError("duplicate payload path: " + name)
        expected[name] = {"size": row["size"], "sha256": row["sha256"]}
    actual = {p: v for p, v in observed.items() if p not in ENVELOPES}
    if actual.keys() != expected.keys():
        raise ValueError("membership mismatch; missing=" + repr(sorted(expected.keys() - actual.keys()))
                         + "; extra=" + repr(sorted(actual.keys() - expected.keys())))
    bad = [p for p in expected if expected[p] != actual[p]]
    if bad:
        raise ValueError("payload size/hash mismatch: " + repr(bad))
    print(json.dumps({"artifact_check": "PASS", "payload_files": len(expected),
                      "envelopes": 3, "read_only": True,
                      "mathematical_gate": False}))

if __name__ == "__main__":
    try:
        main()
    except Exception as e:
        print("FAIL: " + str(e), file=sys.stderr)
        sys.exit(1)
