#!/usr/bin/env python3
"""Collect exactly twenty verified, individually reproducible outcome packages."""
import hashlib
import json
from pathlib import Path
import zipfile

ROOT = Path(__file__).resolve().parent
PROJECT = ROOT.parents[3]


def sha(data):
    return hashlib.sha256(data).hexdigest()


def main():
    ledger = json.loads((ROOT / "ledger.json").read_text())
    entries = ledger["verified"]
    if ledger["verified_count"] != 20 or len(entries) != 20:
        raise SystemExit("Collection requires twenty accepted outcomes")
    if len({e["mathdb_id"] for e in entries}) != 20:
        raise SystemExit("Duplicate source question")
    artifacts = []
    records = []
    for e in entries:
        if e["mathdb_id"] == 336488:
            archive = PROJECT / "output/release/premagic-diagonalizability-v1.zip"
        else:
            stem = f"{e['mathdb_id']}-{Path(e['package']).name}-v1.zip"
            archive = PROJECT / "output/release/twenty-proofs" / stem
        data = archive.read_bytes()
        if e.get("archive_sha256") and e["archive_sha256"] != sha(data):
            raise SystemExit(f"Ledger hash mismatch: {archive}")
        with zipfile.ZipFile(archive) as z:
            names = z.namelist()
            manifests = [n for n in names if n.endswith("/SHA256SUMS")]
            if len(manifests) != 1 or len(names) != len(set(names)):
                raise SystemExit(f"Invalid archive inventory: {archive}")
            prefix = manifests[0].removesuffix("SHA256SUMS")
            listed = {}
            for line in z.read(manifests[0]).decode().splitlines():
                digest, relative = line.split("  ", 1)
                listed[prefix + relative] = digest
            actual = {n for n in names if not n.endswith("/") and n != manifests[0]}
            if set(listed) != actual:
                raise SystemExit(f"Manifest member mismatch: {archive}")
            for name, digest in listed.items():
                if sha(z.read(name)) != digest:
                    raise SystemExit(f"Member hash mismatch: {archive}:{name}")
        artifacts.append(("packages/" + archive.name, data))
        records.append({"ordinal": e["ordinal"], "mathdb_id": e["mathdb_id"],
                        "archive": archive.name, "sha256": sha(data), "manifest": "PASS"})
    readme = """# Twenty Lean-verified mathematical outcomes

This collection contains twenty distinct MathDB source-question outcomes.
Each nested ZIP includes a paper, full claimed-outcome Lean proof, source
provenance, independent review, and reproduction instructions. Each package
was rebuilt from an extracted archive before acceptance; every member hash
was checked again when this collection was assembled.

These are not twenty claims of new mathematical discovery. Known-result
formalizations, counterexamples, and explicitly labeled literal-source
corrections are included. Read each package's scope and prior-status notes.
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
    dest = PROJECT / "output/release/twenty-proofs-v1.zip"
    with zipfile.ZipFile(dest, "w", zipfile.ZIP_DEFLATED) as z:
        for name, data in artifacts:
            info = zipfile.ZipInfo("twenty-proofs-v1/" + name, (2026, 10, 25, 0, 0, 0))
            info.compress_type = zipfile.ZIP_DEFLATED
            info.external_attr = 0o644 << 16
            z.writestr(info, data)
    receipt = {"outcomes": 20, "archive": str(dest), "sha256": sha(dest.read_bytes()),
               "packages": records}
    (ROOT / "collection-verification.json").write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps({k: v for k, v in receipt.items() if k != "packages"}, indent=2))


if __name__ == "__main__":
    main()
