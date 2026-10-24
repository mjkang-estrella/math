#!/usr/bin/env python3
"""Read-only exact-packet verification. Artifact checks are not mathematical gates."""
import argparse, hashlib, json, os, stat
from pathlib import Path, PurePosixPath
ROOT_REL = "frontier/campaigns/2026-10-14/structural-r220-isolated-continuation/fresh-structural-discovery-r233"
OUTSIDE = {"FINAL.md", "MANIFEST.json", "REPORT.md", "ANCHORS.json", "SEAL-CHECK.json"}

def digest(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

def regular(p):
    s = p.lstat()
    if not stat.S_ISREG(s.st_mode):
        raise ValueError("not a regular non-symlink file: " + str(p))
    return s

def safe_name(s):
    p = PurePosixPath(s)
    if not isinstance(s, str) or not s or p.is_absolute() or ".." in p.parts or "\\" in s or p.as_posix() != s:
        raise ValueError("unsafe or noncanonical selected path")
    return s

def verify_payload(base, entries, selected):
    names = [safe_name(e["path"]) for e in entries]
    wanted = [safe_name(s) for s in selected]
    if names != sorted(set(names)) or wanted != sorted(set(wanted)) or names != wanted:
        raise ValueError("exact selection mismatch")
    for e in entries:
        p = base / e["path"]
        s = regular(p)
        if s.st_size != e["bytes"] or digest(p) != e["sha256"]:
            raise ValueError("byte/hash mismatch: " + e["path"])
        if format(stat.S_IMODE(s.st_mode), "04o") != e["mode"]:
            raise ValueError("mode mismatch: " + e["path"])

def surface_files(base):
    found = set()
    for d, dirs, files in os.walk(base, followlinks=False):
        for name in dirs:
            if (Path(d) / name).is_symlink():
                raise ValueError("symlink directory in packet root")
        for name in files:
            p = Path(d) / name
            regular(p)
            found.add(p.relative_to(base).as_posix())
    return found

def verify_packet(base, anchors):
    for name, expected in anchors.items():
        regular(base / name)
        if len(expected) != 64 or digest(base / name) != expected:
            raise ValueError("detached anchor mismatch: " + name)
        if stat.S_IMODE((base / name).stat().st_mode) != 0o444:
            raise ValueError("detached mode mismatch: " + name)
    manifest = json.loads((base / "MANIFEST.json").read_bytes())
    selection = json.loads((base / "selection.json").read_bytes())
    if manifest["root"] != ROOT_REL or selection["root"] != ROOT_REL:
        raise ValueError("root identity mismatch")
    sd = digest(base / "selection.json")
    if manifest["selection_sha256"] != sd:
        raise ValueError("selection digest mismatch")
    if ("selection_sha256=" + sd) not in (base / "FINAL.md").read_text().splitlines():
        raise ValueError("FINAL does not bind exact selection")
    verify_payload(base, manifest["entries"], selection["paths"])
    expected = set(selection["paths"])
    actual = surface_files(base)
    if expected - actual or actual - expected - OUTSIDE:
        raise ValueError("root surface differs from selected packet plus explicit detached files")
    return {"artifact_verification": "exact selected bytes and modes verified", "selected_files": len(expected),
            "detached_anchors": anchors, "read_only": True, "mathematical_verdict": "none"}

def main():
    p = argparse.ArgumentParser()
    p.add_argument("--root", required=True)
    p.add_argument("--final-sha256", required=True)
    p.add_argument("--manifest-sha256", required=True)
    p.add_argument("--report-sha256", required=True)
    a = p.parse_args()
    anchors = {"FINAL.md": a.final_sha256, "MANIFEST.json": a.manifest_sha256, "REPORT.md": a.report_sha256}
    print(json.dumps(verify_packet(Path(a.root), anchors), indent=2, sort_keys=True))

if __name__ == "__main__":
    main()
