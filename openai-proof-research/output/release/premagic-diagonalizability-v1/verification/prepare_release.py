#!/usr/bin/env python3
"""Prepare a source-and-proof archive, excluding dependencies and source papers."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import shutil
import subprocess
import zipfile

ROOT = Path(__file__).resolve().parents[1]
NAME = "premagic-diagonalizability-v1"


def digest(path):
    return sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out-dir", type=Path, default=ROOT / "dist")
    args = parser.parse_args()
    out = args.out_dir.resolve()
    package = out / NAME
    package.mkdir(parents=True, exist_ok=True)
    selected = [p for p in ROOT.iterdir() if p.is_file() and p.suffix in {".md", ".txt"}]
    for folder, suffixes in [("paper", {".tex"}), ("formal", {".lean", ".py", ".json", ".toml", ".md"}),
                             ("verification", {".py"}), ("notes", {".md"})]:
        selected += [p for p in (ROOT / folder).iterdir() if p.is_file() and p.suffix in suffixes]
    selected += [ROOT / "formal/lean-toolchain", ROOT / "sources/source-manifest.json"]
    selected += list((ROOT / "formal/notes").glob("*.md"))
    for source in selected:
        target = package / source.relative_to(ROOT)
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(source, target)
    shutil.copyfile(ROOT / "build/main.pdf", package / "paper.pdf")
    evidence = package / "verification/receipts"
    evidence.mkdir(parents=True, exist_ok=True)
    shutil.copyfile(ROOT / "build/paper-build.json", evidence / "paper-build.json")
    for name in ("mutation-checks.json", "source-validation.json"):
        shutil.copyfile(ROOT / "build" / name, evidence / name)
    checks = subprocess.check_output(["python3", str(ROOT / "verification/independent_check.py")], text=True)
    (evidence / "independent-check.json").write_text(checks)
    for path in (ROOT / "formal/build").glob("*"):
        if path.is_file() and path.suffix in {".json", ".stdout", ".stderr", ".log", ".txt"}:
            shutil.copyfile(path, evidence / ("lean-" + path.name))
    metadata = {
        "title": "A positive counterexample to the premagic diagonalizability conjecture",
        "author": "Myeongjin Kang", "date": "2026-10-25", "version": "1",
        "problem_url": "https://mathdb.com/p/336488",
        "status": "Prepared locally; not submitted or externally peer reviewed",
        "claim": "A strictly positive 3x3 premagic matrix need not be diagonalizable over C or R.",
        "novelty": "New to this project; worldwide priority not established",
        "licenses": {"prose": "CC-BY-4.0", "original_code": "MIT"},
        "keywords": ["premagic matrix", "diagonalizability", "Jordan chain", "Lean 4", "stochastic matrix"]
    }
    (package / "metadata.json").write_text(json.dumps(metadata, indent=2) + "\n")
    files = sorted(p for p in package.rglob("*") if p.is_file() and p.name != "SHA256SUMS")
    (package / "SHA256SUMS").write_text("".join(f"{digest(p)}  {p.relative_to(package).as_posix()}\n" for p in files))
    archive = out / (NAME + ".zip")
    with zipfile.ZipFile(archive, "w", compression=zipfile.ZIP_DEFLATED) as z:
        for path in sorted(p for p in package.rglob("*") if p.is_file()):
            entry = zipfile.ZipInfo((Path(NAME) / path.relative_to(package)).as_posix(), (2026, 10, 25, 0, 0, 0))
            entry.compress_type = zipfile.ZIP_DEFLATED
            entry.external_attr = 0o644 << 16
            z.writestr(entry, path.read_bytes())
    receipt = {"archive": str(archive), "sha256": digest(archive), "file_count": len(files) + 1}
    print(json.dumps(receipt, indent=2))


if __name__ == "__main__":
    main()
