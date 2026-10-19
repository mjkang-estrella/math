#!/usr/bin/env python3
"""Integrity-only mutations on temporary copies; never mutates sealed original."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import shutil
import subprocess
import sys
import tempfile

def sha(b):
    return hashlib.sha256(b).hexdigest()

def snapshot(root):
    paths = [root / "FINAL.json", root / "MANIFEST.json"] + sorted((root / "packet").rglob("*"))
    return {p.relative_to(root).as_posix(): ("directory" if p.is_dir() else sha(p.read_bytes())) for p in paths}

def reseal(root):
    packet = root / "packet"
    files = [{"path": p.relative_to(packet).as_posix(), "bytes": p.stat().st_size, "sha256": sha(p.read_bytes())}
             for p in sorted(packet.rglob("*")) if p.is_file()]
    dirs = sorted(p.relative_to(packet).as_posix() for p in packet.rglob("*") if p.is_dir())
    m = {"format": "r118-exact-packet-v1", "files": files, "directories": dirs}
    (root / "MANIFEST.json").write_text(json.dumps(m, indent=2, sort_keys=True) + "\n")
    f = json.loads((root / "FINAL.json").read_text())
    f["manifest_sha256"] = sha((root / "MANIFEST.json").read_bytes())
    f["report_sha256"] = sha((packet / "public/report.md").read_bytes())
    (root / "FINAL.json").write_text(json.dumps(f, indent=2, sort_keys=True) + "\n")

def main():
    ap = argparse.ArgumentParser(description=__doc__)
    for name in ["root", "tree", "finalhash", "reporthash"]:
        ap.add_argument("--" + name, required=True)
    args = ap.parse_args()
    root = Path(args.root).resolve()
    tree = Path(args.tree).resolve()
    controls = root / "controls"
    assert controls.is_dir()
    original = snapshot(root)
    verifier = root / "packet/public/verify.py"
    source = json.loads((root / "packet/public/source-register.json").read_text())[0]["file"]
    primary = json.loads((root / "packet/public/primary-register.json").read_text())[0]["pdf"]
    rows = []
    cases = [
        ("baseline", None),
        ("missing-finalhash", "--finalhash"),
        ("missing-reporthash", "--reporthash"),
        ("wrong-finalhash", "detached finalhash mismatch"),
        ("wrong-reporthash", "detached reporthash mismatch"),
        ("changed-report", "packet file bytes/hash mismatch"),
        ("changed-source", "packet file bytes/hash mismatch"),
        ("changed-primary", "packet file bytes/hash mismatch"),
        ("missing-file", "packet file membership mismatch"),
        ("extra-file", "packet file membership mismatch"),
        ("extra-empty-directory", "packet directory membership mismatch"),
        ("symlink-file", "non-regular or symlink file"),
        ("symlink-directory", "non-directory or symlink directory"),
        ("hardlink-file", "hard-linked file"),
        ("changed-manifest", "manifest hash mismatch"),
        ("changed-final", "detached finalhash mismatch"),
        ("changed-verifier", "packet file bytes/hash mismatch"),
        ("coherent-reseal-old-anchor", "detached finalhash mismatch"),
        ("wrong-external-tree", "external complete tree hash mismatch"),
    ]
    for name, expected in cases:
        with tempfile.TemporaryDirectory(prefix=name + "-", dir=controls) as td:
            copy = Path(td) / "copy"
            copy.mkdir()
            shutil.copytree(root / "packet", copy / "packet")
            for anchor in ["MANIFEST.json", "FINAL.json"]:
                shutil.copyfile(root / anchor, copy / anchor)
            packet = copy / "packet"
            finalhash, reporthash, tree_arg = args.finalhash, args.reporthash, str(tree)
            if name == "wrong-finalhash": finalhash = "0" * 64
            if name == "wrong-reporthash": reporthash = "0" * 64
            changes = {"changed-report": "public/report.md", "changed-source": source,
                       "changed-primary": primary, "changed-verifier": "public/verify.py"}
            if name in changes:
                p = packet / changes[name]; p.write_bytes(p.read_bytes() + b"\ncontrol mutation\n")
            if name == "missing-file": (packet / "public/report.md").unlink()
            if name == "extra-file": (packet / "public/extra-control.txt").write_text("extra")
            if name == "extra-empty-directory": (packet / "extra-control-directory").mkdir()
            if name == "symlink-file":
                p = packet / "public/report.md"; p.unlink(); p.symlink_to("RIGHTS.md")
            if name == "symlink-directory": (packet / "extra-link").symlink_to("public", target_is_directory=True)
            if name == "hardlink-file":
                p = packet / "public/report.md"; p.unlink(); os.link(packet / "public/RIGHTS.md", p)
            if name in ["changed-manifest", "changed-final"]:
                p = copy / ("MANIFEST.json" if name == "changed-manifest" else "FINAL.json")
                p.write_bytes(p.read_bytes() + b" ")
            if name == "coherent-reseal-old-anchor":
                p = packet / "public/report.md"; p.write_text(p.read_text() + "\ncoherent changed report\n")
                reseal(copy)
            if name == "wrong-external-tree":
                p = Path(td) / "wrong-tree.json"; p.write_text("{}\n"); tree_arg = str(p)
            cmd = [sys.executable, str(verifier), "--root", str(copy), "--tree", tree_arg]
            if name != "missing-finalhash": cmd += ["--finalhash", finalhash]
            if name != "missing-reporthash": cmd += ["--reporthash", reporthash]
            proc = subprocess.run(cmd, capture_output=True, text=True, timeout=30)
            ok = (proc.returncode == 0 and "INTEGRITY_OK_ONLY" in proc.stdout) if expected is None else (proc.returncode != 0 and expected in proc.stderr)
            rows.append({"name": name, "expected": "accept" if expected is None else expected,
                         "passed": ok, "returncode": proc.returncode,
                         "stdout": proc.stdout.strip(), "stderr": proc.stderr.strip().replace(str(copy), "<copy>")})
            assert ok, json.dumps(rows[-1])
    after = snapshot(root)
    assert after == original, "Original changed during copied controls"
    result = {"status": "INTEGRITY_CONTROLS_ONLY", "cases": rows, "original_unchanged": True,
              "original_inventory_sha256": sha(json.dumps(original, sort_keys=True).encode()),
              "finalhash": args.finalhash, "reporthash": args.reporthash}
    (controls / "results.json").write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({"controls": len(rows), "all_expected": True, "original_unchanged": True}, sort_keys=True))

if __name__ == "__main__":
    main()
