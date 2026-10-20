#!/usr/bin/env python3
"""Mutates only fresh copied artifacts under the exclusive root's work/controls.
Run after sealing with the same three detached anchors as verify.py.
No deletion, overwrite, network, nested agents, or original-input writes.
"""
import argparse
import datetime
import json
from pathlib import Path
import shutil
import subprocess
import sys


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--root", required=True, type=Path)
    ap.add_argument("--project", required=True, type=Path)
    for label in ("final", "manifest", "report"):
        ap.add_argument("--" + label + "-sha256", required=True)
    a = ap.parse_args()
    root = a.root.resolve()
    project = a.project.resolve()
    expected = project / "frontier/campaigns/2026-10-14/fresh-structural-discovery-r136"
    if root != expected or (root / "work").is_symlink():
        raise ValueError("exclusive writable root required")
    controls = root / "work/controls"
    controls.mkdir(exist_ok=False)
    records = []
    for name in ("baseline", "payload", "extra", "missing", "final", "manifest", "report", "symlink"):
        dest = controls / name
        dest.mkdir()
        shutil.copytree(root / "packet", dest / "packet")
        for f in ("FINAL.json", "REPORT.md"):
            shutil.copy2(root / f, dest / f)
        target = dest / "packet/public/derivations.md"
        if name == "payload":
            target.write_bytes(target.read_bytes() + b"\ncontrol mutation\n")
        elif name == "extra":
            (dest / "packet/extra.txt").write_text("copied extra control\n")
        elif name == "missing":
            target.rename(dest / "removed-payload.md")
        elif name in ("final", "manifest", "report"):
            path = dest / {"final": "FINAL.json", "manifest": "packet/MANIFEST.json", "report": "REPORT.md"}[name]
            path.write_bytes(path.read_bytes() + b"\n")
        elif name == "symlink":
            moved = dest / "removed-payload.md"
            target.rename(moved)
            target.symlink_to(moved)
        command = [sys.executable, "-B", str(root / "packet/public/verify.py"),
                   "--root", str(dest), "--project", str(project),
                   "--final-sha256", a.final_sha256, "--manifest-sha256", a.manifest_sha256,
                   "--report-sha256", a.report_sha256]
        result = subprocess.run(command, capture_output=True, text=True)
        okay = result.returncode == 0 if name == "baseline" else result.returncode != 0
        records.append({"case": name, "expected": "verify" if name == "baseline" else "reject",
                        "returncode": result.returncode, "expected_behavior": okay,
                        "stdout": result.stdout, "stderr": result.stderr})
    receipt = {"utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
               "anchors": {"final": a.final_sha256, "manifest": a.manifest_sha256, "report": a.report_sha256},
               "records": records, "all_expected": all(r["expected_behavior"] for r in records),
               "scope": "Post-seal copied artifact controls; this receipt is outside the sealed packet."}
    (root / "work/control-receipt.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({"cases": len(records), "all_expected": receipt["all_expected"]}))
    if not receipt["all_expected"]:
        sys.exit(1)


if __name__ == "__main__":
    main()
