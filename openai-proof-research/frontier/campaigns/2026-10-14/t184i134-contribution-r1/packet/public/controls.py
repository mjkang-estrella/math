#!/usr/bin/env python3
"""Copied integrity controls: run verify.py on copies of the sealed root, clean and tampered.

Usage: python3 -B controls.py <root> <project> <final> <manifest> <report> <out.json>
Copies go to <root>/tmp/controls/<case>; the originals are never modified. Copies are removed afterwards.
"""
import hashlib, json, shutil, subprocess, sys
from pathlib import Path


def tree_hash(d: Path) -> str:
    h = hashlib.sha256()
    for p in sorted(x for x in d.rglob("*") if x.is_file()):
        h.update(p.relative_to(d).as_posix().encode() + b"\0" + hashlib.sha256(p.read_bytes()).digest())
    return h.hexdigest()


def flip(p: Path):
    b = bytearray(p.read_bytes())
    b[len(b) // 2] ^= 1
    p.write_bytes(bytes(b))


def main():
    root, project, fin, man, rep, out = sys.argv[1:7]
    root, project = Path(root), Path(project)
    base = root / "tmp/controls"
    if base.exists():
        shutil.rmtree(base)
    cases = {
        "clean": (lambda c: None, True),
        "review-byte": (lambda c: flip(c / "packet/public/review.md"), False),
        "final-byte": (lambda c: flip(c / "FINAL.json"), False),
        "manifest-byte": (lambda c: flip(c / "packet/MANIFEST.json"), False),
        "report-byte": (lambda c: flip(c / "REPORT.md"), False),
        "extra-packet-file": (lambda c: (c / "packet/public/extra.txt").write_text("x"), False),
        "deleted-file": (lambda c: (c / "packet/public/rights.md").unlink(), False),
        "primary-byte": (lambda c: flip(c / "packet/private/primary/arxiv-2609.04654v1.pdf"), False),
        "source-byte": (lambda c: flip(next((c / "packet/private/source").rglob("optimizer.tex"))), False),
        "kang-text-byte": (lambda c: flip(c / "packet/private/primary/kang-zenodo-23351325.txt"), False),
    }
    results = {}
    orig_before = tree_hash(root / "packet")
    for name, (mut, expect) in cases.items():
        c = base / name
        c.mkdir(parents=True)
        shutil.copytree(root / "packet", c / "packet")
        for f in ("FINAL.json", "REPORT.md"):
            shutil.copy2(root / f, c / f)
        mut(c)
        before = tree_hash(c)
        r = subprocess.run([sys.executable, "-B", str(root / "packet/public/verify.py"), "--root", str(c),
                            "--project", str(project), "--final", fin, "--manifest", man, "--report", rep],
                           capture_output=True, text=True)
        after = tree_hash(c)
        ok = (r.returncode == 0) == expect
        results[name] = {"expected_accept": expect, "returncode": r.returncode, "as_expected": ok,
                         "copy_unchanged_by_verifier": before == after, "stdout_head": r.stdout.strip().splitlines()[:2]}
    wrong = subprocess.run([sys.executable, "-B", str(root / "packet/public/verify.py"), "--root", str(base / "clean"),
                            "--project", str(project), "--final", "0" * 64, "--manifest", man, "--report", rep],
                           capture_output=True, text=True)
    results["wrong-final-anchor"] = {"expected_accept": False, "returncode": wrong.returncode,
                                     "as_expected": wrong.returncode != 0, "copy_unchanged_by_verifier": True}
    shutil.rmtree(base)
    summary = {"all_as_expected": all(v["as_expected"] and v["copy_unchanged_by_verifier"] for v in results.values()),
               "original_packet_unchanged": orig_before == tree_hash(root / "packet"), "cases": results}
    Path(out).write_text(json.dumps(summary, indent=1) + "\n")
    print(json.dumps({k: summary[k] for k in ("all_as_expected", "original_packet_unchanged")}))


if __name__ == "__main__":
    main()
