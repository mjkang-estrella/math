#!/usr/bin/env python3
"""Read-only artifact verifier for the T096N126 contribution review r1.

Checks (artifact integrity only, never a mathematical or contribution gate):
  * SHA256 of the exact packet/MANIFEST.json equals --expected-final;
  * the detached FINAL file, if present, carries the same hash;
  * every packet file is listed exactly once with matching size and SHA256,
    and no unlisted file exists under packet/ (exact names);
  * the outside REPORT.md hashes to --expected-report (and REPORT.sha256 agrees);
  * the inputs recorded in packet/public/inputs.json are unchanged under --project.

It opens files for reading only and writes nothing. Run with python -B.
"""
import argparse
import hashlib
import json
import os
import sys


def sha(path):
    h = hashlib.sha256()
    with open(path, "rb") as fh:
        for block in iter(lambda: fh.read(1 << 20), b""):
            h.update(block)
    return h.hexdigest()


def main():
    here = os.path.dirname(os.path.abspath(__file__))
    default_root = os.path.dirname(os.path.dirname(here))
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", default=default_root, help="review directory")
    ap.add_argument("--project", default=None, help="project root for inputs")
    ap.add_argument("--expected-final", required=True)
    ap.add_argument("--expected-report", required=True)
    ap.add_argument("--skip-inputs", action="store_true")
    a = ap.parse_args()
    root = os.path.abspath(a.root)
    project = os.path.abspath(a.project) if a.project else os.path.abspath(
        os.path.join(root, "..", "..", "..", ".."))
    errors = []
    packet = os.path.join(root, "packet")
    man_path = os.path.join(packet, "MANIFEST.json")
    if not os.path.isfile(man_path):
        print(json.dumps({"status": "FAIL", "errors": ["missing MANIFEST.json"]}))
        return 1
    if sha(man_path) != a.expected_final:
        errors.append("MANIFEST sha256 != expected FINAL")
    final_file = os.path.join(root, "FINAL")
    if os.path.exists(final_file):
        with open(final_file, encoding="utf-8") as fh:
            if fh.read().strip() != a.expected_final:
                errors.append("FINAL file != expected FINAL")
    else:
        errors.append("missing detached FINAL file")
    with open(man_path, encoding="utf-8") as fh:
        manifest = json.load(fh)
    listed = {}
    for entry in manifest.get("files", []):
        name = entry["path"]
        if name in listed:
            errors.append("duplicate manifest entry " + name)
        listed[name] = entry
    present = set()
    for dirpath, dirnames, filenames in os.walk(packet):
        for fn in filenames:
            rel = os.path.relpath(os.path.join(dirpath, fn), packet).replace(os.sep, "/")
            if rel != "MANIFEST.json":
                present.add(rel)
    for rel in sorted(present - set(listed)):
        errors.append("unlisted packet file " + rel)
    for rel in sorted(set(listed) - present):
        errors.append("missing packet file " + rel)
    for rel in sorted(present & set(listed)):
        p = os.path.join(packet, rel)
        if os.path.getsize(p) != listed[rel]["size"]:
            errors.append("size mismatch " + rel)
        if sha(p) != listed[rel]["sha256"]:
            errors.append("sha256 mismatch " + rel)
    rep = os.path.join(root, "REPORT.md")
    if not os.path.isfile(rep):
        errors.append("missing REPORT.md")
    else:
        if sha(rep) != a.expected_report:
            errors.append("REPORT sha256 != expected REPORT")
        rs = os.path.join(root, "REPORT.sha256")
        if os.path.isfile(rs):
            with open(rs, encoding="utf-8") as fh:
                if fh.read().split()[0] != a.expected_report:
                    errors.append("REPORT.sha256 != expected REPORT")
        else:
            errors.append("missing REPORT.sha256")
    checked_inputs = 0
    if not a.skip_inputs:
        with open(os.path.join(packet, "public", "inputs.json"), encoding="utf-8") as fh:
            inputs = json.load(fh)
        for rel, digest in sorted(inputs["files"].items()):
            p = os.path.join(project, rel)
            if not os.path.isfile(p):
                errors.append("missing input " + rel)
            elif sha(p) != digest:
                errors.append("changed input " + rel)
            checked_inputs += 1
    out = {
        "status": "PASS" if not errors else "FAIL",
        "packet_files": len(present),
        "inputs_checked": checked_inputs,
        "errors": errors,
        "note": "artifact integrity only; not a mathematical or contribution gate",
    }
    print(json.dumps(out, indent=1))
    return 0 if not errors else 1


if __name__ == "__main__":
    sys.exit(main())
