#!/usr/bin/env python3
"""Package a reviewed outcome with source, proof, paper and verification receipts."""
import argparse
import hashlib
import json
from pathlib import Path
import shutil
import zipfile

ROOT = Path(__file__).resolve().parent


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("outcome", type=Path)
    p.add_argument("--out-dir", type=Path, required=True)
    a = p.parse_args()
    source = a.outcome.resolve()
    meta = json.loads((source / "outcome.json").read_text())
    if meta["status"] != "verified":
        raise SystemExit("Only independently reviewed, verified outcomes can be released")
    proof = source / "formal" / (meta["module"] + ".lean")
    proof_hash = hashlib.sha256(proof.read_bytes()).hexdigest()
    paper_hash = hashlib.sha256((source / "main.tex").read_bytes()).hexdigest()
    audit = json.loads((source / "build/audit.json").read_text())
    paper_audit = json.loads((source / "build/paper-build.json").read_text())
    if audit["status"] != "PASS" or audit["sha256"] != proof_hash:
        raise SystemExit("Proof differs from the compiled certificate")
    if paper_audit["exit_code"] != 0 or paper_audit["issues"] or paper_audit["tex_sha256"] != paper_hash:
        raise SystemExit("Paper differs from the successful build")
    if meta.get("reviewed_proof_sha256") != proof_hash or meta.get("reviewed_paper_sha256") != paper_hash:
        raise SystemExit("Current sources lack a matching independent review record")
    if not (source / "review.md").is_file():
        raise SystemExit("Independent review file is missing")
    name = str(meta["mathdb_id"]) + "-" + source.name + "-v1"
    dest = a.out_dir.resolve() / name
    dest.mkdir(parents=True, exist_ok=True)
    files = [p for p in source.rglob("*") if p.is_file() and "build" not in p.parts
             and "__pycache__" not in p.parts and p.suffix in {".lean", ".md", ".json", ".tex", ".txt"}]
    for f in files:
        q = dest / f.relative_to(source)
        q.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(f, q)
    for name2 in ("verify_outcome.py", "build_paper.py", "pins.json"):
        shutil.copyfile(ROOT / name2, dest / name2)
    shutil.copyfile(source / "build/main.pdf", dest / "paper.pdf")
    receipts = dest / "receipts"
    receipts.mkdir(exist_ok=True)
    for fname in ("audit.json", "Checks.log", "paper-build.json"):
        shutil.copyfile(source / "build" / fname, receipts / fname)
    allfiles = sorted(f for f in dest.rglob("*") if f.is_file() and f.name != "SHA256SUMS")
    (dest / "SHA256SUMS").write_text("".join(
        hashlib.sha256(f.read_bytes()).hexdigest() + "  " + f.relative_to(dest).as_posix() + "\n"
        for f in allfiles))
    archive = dest.with_suffix(".zip")
    with zipfile.ZipFile(archive, "w", zipfile.ZIP_DEFLATED) as z:
        for f in sorted(q for q in dest.rglob("*") if q.is_file()):
            item = zipfile.ZipInfo((Path(name) / f.relative_to(dest)).as_posix(), (2026, 10, 25, 0, 0, 0))
            item.compress_type = zipfile.ZIP_DEFLATED
            item.external_attr = 0o644 << 16
            z.writestr(item, f.read_bytes())
    print(json.dumps({"archive": str(archive), "sha256": hashlib.sha256(archive.read_bytes()).hexdigest()}, indent=2))


if __name__ == "__main__":
    main()
