#!/usr/bin/env python3
"""Copied integrity controls for structural round r133.

Usage:
    python -B packet/public/controls.py --root ROOT --project PROJECT --finalhash DETACHED_SHA256

Each case copies ROOT's FINAL.json, REPORT.md and packet/ into a temporary directory inside ROOT
(ROOT/.controls-tmp), optionally tampers with the copy, and runs the actual packet verifier on the
copy. The actual root is fingerprinted before and after; the receipt ROOT/artifact-controls.json is
written only if it is unchanged and every case has its expected outcome. These are artifact
checks, not mathematical gates.
"""
import argparse
import hashlib
import json
import os
import pathlib
import shutil
import subprocess
import sys

TMP = ".controls-tmp"
RECEIPT = "artifact-controls.json"


def sha256_bytes(b: bytes) -> str:
    return hashlib.sha256(b).hexdigest()


def fingerprint(root: pathlib.Path) -> str:
    h = hashlib.sha256()
    for dirpath, dirnames, filenames in os.walk(root):
        d = pathlib.Path(dirpath)
        rel_d = d.relative_to(root).as_posix()
        if rel_d == TMP or rel_d.startswith(TMP + "/"):
            dirnames[:] = []
            continue
        dirnames.sort()
        for name in sorted(filenames):
            p = d / name
            rel = p.relative_to(root).as_posix()
            if rel == RECEIPT:
                continue
            h.update(rel.encode() + b"\0" + sha256_bytes(p.read_bytes()).encode() + b"\n")
        for name in dirnames:
            h.update((d / name).relative_to(root).as_posix().encode() + b"/\n")
    return h.hexdigest()


def manifest_entries(packet: pathlib.Path) -> dict:
    entries = {".": {"type": "dir"}}
    for dirpath, dirnames, filenames in os.walk(packet):
        d = pathlib.Path(dirpath)
        for name in dirnames + filenames:
            p = d / name
            rel = p.relative_to(packet).as_posix()
            if p.is_dir():
                entries[rel] = {"type": "dir"}
            elif rel != "MANIFEST.json":
                entries[rel] = {"type": "file", "bytes": p.stat().st_size,
                                "sha256": sha256_bytes(p.read_bytes())}
    return dict(sorted(entries.items()))


def reseal(case: pathlib.Path) -> str:
    """Consistently rebuild MANIFEST and FINAL in a copy; return the new FINAL hash."""
    packet = case / "packet"
    (packet / "MANIFEST.json").write_text(
        json.dumps({"version": 1, "entries": manifest_entries(packet)}, indent=1, sort_keys=True) + "\n")
    final = json.loads((case / "FINAL.json").read_text())
    final["manifest_sha256"] = sha256_bytes((packet / "MANIFEST.json").read_bytes())
    final["frozen_statement_sha256"] = sha256_bytes((packet / "public/frozen-statement.md").read_bytes())
    final["proof_sha256"] = sha256_bytes((packet / "public/proof.md").read_bytes())
    final["public_report_sha256"] = sha256_bytes((packet / "public/report.md").read_bytes())
    final["report_sha256"] = sha256_bytes((case / "REPORT.md").read_bytes())
    (case / "FINAL.json").write_text(json.dumps(final, indent=1, sort_keys=True) + "\n")
    return sha256_bytes((case / "FINAL.json").read_bytes())


def append(p: pathlib.Path, text: bytes = b"\ntampered\n") -> None:
    p.write_bytes(p.read_bytes() + text)


def main() -> None:
    ap = argparse.ArgumentParser()
    ap.add_argument("--root", required=True)
    ap.add_argument("--project", required=True)
    ap.add_argument("--finalhash", required=True)
    a = ap.parse_args()
    root = pathlib.Path(a.root).resolve()
    verifier = root / "packet/public/verify.py"
    tmp = root / TMP
    if tmp.exists():
        sys.exit(f"{tmp} already exists; refusing to proceed")
    before = fingerprint(root)
    src_body = ("packet/private/source/preprints/Hardness-of-finding-large-independent-sets-in-"
                "three-colorable-graphs-September-24-2026/build/source/sections/construction.tex")

    def t_final_status(c):
        f = json.loads((c / "FINAL.json").read_text())
        f["status"] = "ACCEPTED"
        (c / "FINAL.json").write_text(json.dumps(f, indent=1, sort_keys=True) + "\n")
        return sha256_bytes((c / "FINAL.json").read_bytes())

    def t_reseal_source(c):
        p = c / src_body
        append(p, b"% altered\n")
        rp = c / "packet/private/source/receipts.json"
        rec = json.loads(rp.read_text())
        rel = src_body[len("packet/private/source/"):]
        for r in rec:
            if r["path"] == rel:
                r["sha256"] = sha256_bytes(p.read_bytes())
        rp.write_text(json.dumps(rec, indent=1) + "\n")
        return reseal(c)

    def t_reseal_frozen(c):
        append(c / "packet/public/frozen-statement.md", b"\nk >= 2 only\n")
        return reseal(c)

    cases = [
        ("baseline", None, "accept", True),
        ("missing-detached-anchor", None, "reject", False),
        ("wrong-detached-anchor", lambda c: "0" * 64, "reject", True),
        ("changed-public-proof", lambda c: append(c / "packet/public/proof.md"), "reject", True),
        ("changed-private-source", lambda c: append(c / src_body), "reject", True),
        ("changed-primary", lambda c: append(c / "packet/private/primary/kowz-arxiv-2003.11351.txt"), "reject", True),
        ("extra-packet-file", lambda c: (c / "packet/public/extra.md").write_text("x\n"), "reject", True),
        ("missing-packet-file", lambda c: (c / "packet/public/rights.md").unlink(), "reject", True),
        ("changed-outside-report", lambda c: append(c / "REPORT.md"), "reject", True),
        ("self-promoted-status-with-new-anchor", t_final_status, "reject", True),
        ("consistent-reseal-altered-source", t_reseal_source, "reject", True),
        ("consistent-reseal-altered-frozen-statement", t_reseal_frozen, "reject", True),
    ]
    results = []
    ok_all = True
    try:
        tmp.mkdir()
        for name, tamper, expected, with_anchor in cases:
            c = tmp / name
            c.mkdir()
            shutil.copy2(root / "FINAL.json", c / "FINAL.json")
            shutil.copy2(root / "REPORT.md", c / "REPORT.md")
            shutil.copytree(root / "packet", c / "packet")
            anchor = a.finalhash
            if tamper is not None:
                r = tamper(c)
                if isinstance(r, str):
                    anchor = r
            fp_copy = fingerprint(c)
            cmd = [sys.executable, "-B", str(verifier), "--root", str(c), "--project", a.project]
            if with_anchor:
                cmd += ["--finalhash", anchor]
            proc = subprocess.run(cmd, capture_output=True, text=True)
            outcome = "accept" if proc.returncode == 0 else "reject"
            good = outcome == expected
            ok_all &= good
            results.append({"case": name, "expected": expected, "exit": proc.returncode,
                            "expected_outcome": good, "copied_input_unchanged": fingerprint(c) == fp_copy,
                            "output": (proc.stdout + proc.stderr)[-600:]})
            ok_all &= results[-1]["copied_input_unchanged"]
    finally:
        if tmp.exists():
            shutil.rmtree(tmp)
    after = fingerprint(root)
    if before != after:
        sys.exit("actual root changed during controls; no receipt written")
    if not ok_all:
        print(json.dumps(results, indent=1))
        sys.exit("some control case had an unexpected outcome; no receipt written")
    receipt = {"cases": results, "actual_root_fingerprint_before": before,
               "actual_root_fingerprint_after": after, "actual_root_unchanged": True,
               "detached_final_sha256": a.finalhash, "mathematical_gate": False}
    (root / RECEIPT).write_text(json.dumps(receipt, indent=1) + "\n")
    print(json.dumps({"cases": len(results), "all_expected": True, "actual_root_unchanged": True}))


if __name__ == "__main__":
    main()
