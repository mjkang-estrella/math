#!/usr/bin/env python3
"""Read-only verification of frozen inputs, with explicit reviewer read extents.

Original review code: copyright 2026 Myeongjin Kang, MIT license.
Hashing bytes is not a claim to have mathematically read them.
"""
import hashlib
import json
from pathlib import Path

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[3]
CAND = HERE.parent / "fresh-algebra-discovery-r1"


def digest(data):
    return hashlib.sha256(data).hexdigest()


def describe(path, ranges=None, kind="semantic_read"):
    raw = path.read_bytes()
    out = {"path": str(path.relative_to(ROOT)), "bytes": len(raw), "sha256": digest(raw),
           "extent_kind": kind}
    if ranges is not None:
        lines = raw.decode().splitlines(keepends=True)
        out["file_lines"] = len(lines)
        out["read_ranges_inclusive"] = []
        for start, end in ranges:
            end = len(lines) if end is None else end
            assert 1 <= start <= end <= len(lines)
            selected = "".join(lines[start - 1:end]).encode()
            out["read_ranges_inclusive"].append({"start": start, "end": end,
                "bytes": len(selected), "sha256": digest(selected)})
    return out


def main():
    expected = {
        "candidate.md": (17969, "6b2e14d58ef3e132a666e3cdc6dbb3a2caa53a514301dc30323b6b7cf652c179"),
        "output-manifest.json": (13355, "79b0fcddd7d33b980d07a951b5152ecc6a1c19e5fe8d5f3bb5e7464562f4dec9"),
    }
    for name, (size, sha) in expected.items():
        b = (CAND / name).read_bytes()
        assert (len(b), digest(b)) == (size, sha)
    manifest = json.loads((CAND / "output-manifest.json").read_text())
    for entry in manifest["files"]:
        b = (CAND / entry["path"]).read_bytes()
        assert (len(b), digest(b)) == (entry["bytes"], entry["sha256"])
    checksum_count = 0
    for line in (CAND / "SHA256SUMS").read_text().splitlines():
        sha, name = line.split(maxsplit=1)
        name = name.removeprefix("*")
        assert digest((CAND / name).read_bytes()) == sha
        checksum_count += 1
    contracts = json.loads((CAND / "source-contracts.json").read_text())
    for c in contracts["contracts"]:
        s = c["source"]
        raw = (CAND / s["path"]).read_bytes()
        assert digest(raw) == s["file_sha256"]
        selected = "".join(raw.decode().splitlines(keepends=True)[s["start_line"] - 1:s["end_line"]]).encode()
        assert digest(selected) == s["slice_sha256"]

    pinned = CAND / "inputs/pinned/preprints"
    cy = pinned / "A-Cyclic-Polytabloid-Proof-of-Saxls-Conjecture-September-24-2026/build/sections"
    un = pinned / "Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/build/sections"
    reads = [(ROOT / "AGENTS.md", [(1, None)]),
             (ROOT / "sources/upstream.json", [(1, None)]),
             (ROOT / "sources/CONTENTS.md", [(4670, 4694)]),
             (CAND / "candidate.md", [(1, None)]),
             (CAND / "source-contracts.json", [(1, None)]),
             (CAND / "RIGHTS.md", [(1, None)]),
             (cy / "specht-tools.tex", [(1, None)]),
             (cy / "dominance.tex", [(1, None)]),
             (cy / "band-quotient.tex", [(1, 80)]),
             (un / "introduction.tex", [(1, 60)]),
             (un / "preliminaries.tex", [(1, 105), (150, 193)]),
             (un / "balance.tex", [(33, 114)]),
             (CAND / "inputs/context/frontier/iterations/i21-signed-saxl-dominance.md", [(1, 220)]),
             (CAND / "inputs/primary/harman-ryba-2023.txt", [(1, None)]),
             (CAND / "inputs/primary/ikenmeyer-2015.txt", [(277, 420)]),
             (CAND / "inputs/primary/bbs-2021.txt", [(313, 320), (1310, 1410)]),
             (CAND / "inputs/primary/bessenrodt-bowman-2023.txt", [(330, 480)])]
    result = {"candidate_frozen_matches": True, "manifest_entries_verified": len(manifest["files"]),
              "sha256sums_entries_verified": checksum_count,
              "source_contract_slices_verified": len(contracts["contracts"]),
              "line_convention": "UTF-8 decode then str.splitlines(keepends=True); includes form-feed boundaries in PDF text extractions, matching the candidate source-contract manifest",
              "semantic_reads": [describe(p, r) for p, r in reads],
              "additional_code_inspection": describe(CAND / "freeze_artifacts.py", [(10, 37), (63, 78)],
                  kind="source-slice construction and metadata helper inspection only; not executed"),
              "metadata_only": [describe(CAND / name, kind="parsed_or_hashed_metadata_not_full_semantic_read")
                                for name in ("output-manifest.json", "SHA256SUMS", "source-manifest.json", "read-manifest.json")],
              "not_read_or_used_as_premises": ["candidate finite-check source programs",
                    "candidate saved finite-check results", "parent authentication verdict",
                    "GLM computation or report"],
              "status": "PASS"}
    print(json.dumps(result, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
