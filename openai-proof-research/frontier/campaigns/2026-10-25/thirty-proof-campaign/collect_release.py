#!/usr/bin/env python3
"""Collect exactly thirty verified, individually reproducible outcome packages."""
import hashlib
import json
from pathlib import Path, PurePosixPath
import re
import stat
import zipfile

ROOT = Path(__file__).resolve().parent
PROJECT = ROOT.parents[3]


def sha(data):
    return hashlib.sha256(data).hexdigest()


def validate_ledger(ledger):
    entries = ledger["verified"]
    if ledger.get("target") != 30 or ledger.get("verified_count") != 30 or len(entries) != 30:
        raise SystemExit("Collection requires thirty accepted outcomes")
    if any(type(e.get("mathdb_id")) is not int or e["mathdb_id"] <= 0 for e in entries):
        raise SystemExit("Invalid source identifier")
    if len({e["mathdb_id"] for e in entries}) != 30:
        raise SystemExit("Duplicate source question")
    if (any(type(e.get("ordinal")) is not int for e in entries) or
            [e.get("ordinal") for e in entries] != list(range(1, 31))):
        raise SystemExit("Invalid outcome ordinals")
    for e in entries:
        if e.get("replay") != "PASS" or e.get("independent_review") != "PASS":
            raise SystemExit("An outcome lacks review or replay acceptance")
        if not re.fullmatch(r"[0-9a-f]{64}", e.get("archive_sha256", "")):
            raise SystemExit("An accepted archive hash is missing")
        path = e.get("package", "")
        if e["mathdb_id"] == 336488:
            expected = "../premagic-diagonalizability"
            if path != expected:
                raise SystemExit("Invalid premagic package path")
        elif e.get("inherited_from") == "twenty-proof-campaign":
            if not re.fullmatch(r"../twenty-proof-campaign/outcomes/[a-z0-9-]+", path):
                raise SystemExit("Invalid inherited package path")
        elif not re.fullmatch(r"outcomes/[a-z0-9-]+", path):
            raise SystemExit("Invalid extension package path")
        archive = e.get("archive", "")
        if not re.fullmatch(r"output/release/(?:twenty-proofs/|thirty-proofs/)?[a-z0-9-]+\.zip", archive):
            raise SystemExit("Invalid release archive path")
    return entries


def validate_members(z):
    names = z.namelist()
    manifests = [n for n in names if n.endswith("/SHA256SUMS")]
    if len(manifests) != 1 or len(names) != len(set(names)):
        raise SystemExit("Invalid archive inventory")
    prefix = manifests[0].removesuffix("SHA256SUMS")
    if len(PurePosixPath(prefix).parts) != 1:
        raise SystemExit("Unexpected archive root")
    for info in z.infolist():
        path = PurePosixPath(info.filename)
        if (path.is_absolute() or ".." in path.parts or "\\" in info.filename or
                not info.filename.startswith(prefix)):
            raise SystemExit("Unsafe archive member path")
        if stat.S_ISLNK(info.external_attr >> 16):
            raise SystemExit("Archive contains a symbolic link")
    listed = {}
    for line in z.read(manifests[0]).decode().splitlines():
        digest, relative = line.split("  ", 1)
        name = prefix + relative
        if name in listed or not re.fullmatch(r"[0-9a-f]{64}", digest):
            raise SystemExit("Invalid or duplicate manifest entry")
        listed[name] = digest
    actual = {n for n in names if not n.endswith("/") and n != manifests[0]}
    if set(listed) != actual:
        raise SystemExit("Manifest member mismatch")
    for name, digest in listed.items():
        if sha(z.read(name)) != digest:
            raise SystemExit(f"Member hash mismatch: {name}")
    return prefix


def replay_records():
    records = []
    for path in list((ROOT / "build").glob("*replay*.json")) + list((ROOT.parent / "twenty-proof-campaign/build").glob("*replay*.json")):
        data = json.loads(path.read_text())
        if isinstance(data, list):
            records.extend(r for r in data if isinstance(r, dict))
    return records


def validate_acceptance(z, prefix, entry, replays):
    canonical = (ROOT / entry["package"]).resolve()
    if not canonical.is_dir():
        raise SystemExit("Canonical package does not exist")
    if entry["mathdb_id"] == 336488:
        meta = json.loads(z.read(prefix + "metadata.json"))
        if meta.get("problem_url") != "https://mathdb.com/p/336488":
            raise SystemExit("Premagic source identifier mismatch")
        for name in ["formal/Premagic.lean", "paper/main.tex", "notes/final-review.md"]:
            if z.read(prefix + name) != (canonical / name).read_bytes():
                raise SystemExit("Premagic accepted source or review changed")
        audit = json.loads((canonical / "build/release-replay" /
                            prefix / "formal/build/audit.json").read_text())
        proof_hash = sha(z.read(prefix + "formal/Premagic.lean"))
        if audit["sources"]["Premagic.lean"] != proof_hash or audit["declarations_checked"] != 37:
            raise SystemExit("Premagic extracted-replay evidence mismatch")
        return proof_hash
    meta = json.loads(z.read(prefix + "outcome.json"))
    if meta.get("status") != "verified" or meta.get("mathdb_id") != entry["mathdb_id"]:
        raise SystemExit("Unaccepted or mismatched source outcome")
    if meta != json.loads((canonical / "outcome.json").read_text()):
        raise SystemExit("Archived outcome metadata differs from accepted metadata")
    module = meta.get("module", "")
    if not re.fullmatch(r"[A-Za-z_]\w*", module):
        raise SystemExit("Invalid Lean module name")
    proof_name = "formal/" + module + ".lean"
    for name in [proof_name, "main.tex", "review.md", "verify_outcome.py", "pins.json", "paper.pdf"]:
        if prefix + name not in z.namelist():
            raise SystemExit("Missing required standalone package artifact: " + name)
    proof, paper = z.read(prefix + proof_name), z.read(prefix + "main.tex")
    if proof != (canonical / proof_name).read_bytes() or paper != (canonical / "main.tex").read_bytes():
        raise SystemExit("Archived proof or paper differs from accepted source")
    if z.read(prefix + "paper.pdf") != (canonical / "build/main.pdf").read_bytes():
        raise SystemExit("Archived PDF differs from current inspected build")
    proof_hash, paper_hash = sha(proof), sha(paper)
    audit = json.loads(z.read(prefix + "receipts/audit.json"))
    paper_audit = json.loads(z.read(prefix + "receipts/paper-build.json"))
    if (meta.get("reviewed_proof_sha256") != proof_hash or
            meta.get("reviewed_paper_sha256") != paper_hash or
            audit.get("status") != "PASS" or audit.get("sha256") != proof_hash or
            audit.get("declarations") != entry.get("formal_declarations") or
            paper_audit.get("tex_sha256") != paper_hash or
            paper_audit.get("exit_code") != 0 or paper_audit.get("issues")):
        raise SystemExit("Accepted proof/paper evidence does not bind these bytes")
    if not any(r.get("status") == "PASS" and r.get("sha256") == entry["archive_sha256"] and
               r.get("proof_sha256") == proof_hash for r in replays):
        raise SystemExit("No matching extracted-archive replay evidence")
    return proof_hash


def main():
    ledger = json.loads((ROOT / "ledger.json").read_text())
    entries = validate_ledger(ledger)
    replays = replay_records()
    artifacts = []
    records = []
    for e in entries:
        archive = PROJECT / e["archive"]
        data = archive.read_bytes()
        if e["archive_sha256"] != sha(data):
            raise SystemExit(f"Ledger hash mismatch: {archive}")
        with zipfile.ZipFile(archive) as z:
            prefix = validate_members(z)
            proof_hash = validate_acceptance(z, prefix, e, replays)
        artifacts.append(("packages/" + archive.name, data))
        records.append({"ordinal": e["ordinal"], "mathdb_id": e["mathdb_id"],
                        "archive": archive.name, "sha256": sha(data), "manifest": "PASS",
                        "acceptance": "PASS", "replay": "PASS", "proof_sha256": proof_hash})
    readme = """# Thirty Lean-verified mathematical outcomes

This collection contains thirty distinct MathDB source-question outcomes.
Each nested ZIP includes a paper, full claimed-outcome Lean proof, source
provenance, independent review, and reproduction instructions. Each package
was rebuilt from an extracted archive before acceptance; every member hash
was checked again when this collection was assembled.

These are not thirty claims of new mathematical discovery. Known-result
formalizations, counterexamples, and explicitly labeled literal-source
corrections are included. Read each package's scope and prior-status notes.
The original twenty releases are preserved byte for byte.
The two arithmetic inequalities share a joint paper and common proof module,
but have distinct source questions and final theorems. No supporting lemma,
dimension, or normalization is counted as an extra outcome.

Extract the desired nested package and follow its README. Lean 4.34.1 and
the pinned, compiled mathlib dependencies are required. The collection
manifest lists the exact SHA256 of every package. See ledger.json for the
individual outcomes and limitations.
"""
    artifacts += [("README.md", readme.encode()),
                  ("ledger.json", (ROOT / "ledger.json").read_bytes()),
                  ("collection-manifest.json", (json.dumps(records, indent=2) + "\n").encode())]
    sums = "".join(f"{sha(data)}  {name}\n" for name, data in artifacts)
    artifacts.append(("SHA256SUMS", sums.encode()))
    dest = PROJECT / "output/release/thirty-proofs-v1.zip"
    with zipfile.ZipFile(dest, "w", zipfile.ZIP_DEFLATED) as z:
        for name, data in artifacts:
            info = zipfile.ZipInfo("thirty-proofs-v1/" + name, (2026, 10, 25, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o644 << 16
            z.writestr(info, data)
    with zipfile.ZipFile(dest) as z:
        prefix = validate_members(z)
        nested = [n for n in z.namelist() if n.startswith(prefix + "packages/")]
        if len(nested) != 30:
            raise SystemExit("Final collection does not contain thirty packages")
        for record in records:
            if sha(z.read(prefix + "packages/" + record["archive"])) != record["sha256"]:
                raise SystemExit("Final collection package readback mismatch")
    receipt = {"outcomes": 30, "archive": str(dest), "sha256": sha(dest.read_bytes()),
               "packages": records}
    (ROOT / "collection-verification.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({k: v for k, v in receipt.items() if k != "packages"}, indent=2))


if __name__ == "__main__":
    main()
