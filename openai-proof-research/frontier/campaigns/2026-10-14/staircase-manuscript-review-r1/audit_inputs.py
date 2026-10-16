#!/usr/bin/env python3
# Copyright 2026 Myeongjin Kang, no affiliation. MIT License.
"""Hash every input this review read or authenticated, with read extents,
and assert the hashes fixed in the task brief. Output: JSON on stdout."""
import hashlib
import json
from pathlib import Path

CAMPAIGN = Path(__file__).resolve().parents[1]
ROOT = CAMPAIGN.parents[2]

BRIEF = {
    "staircase-manuscript/main.tex": ("015e76c58ebbd6b92c8868d2de9cf49f533f18408e5017b720df8d02f4767495", 15845),
    "staircase-manuscript/main.pdf": ("40aebbdda3c407298f499895b7cd8aee543025864efbcb94808441e1b6b6f54c", 89299),
    "staircase-manuscript/output-manifest.json": ("0fab9a185d016faca5fb035a07aa7b78ddc99dc8437e370f6499897cc989383e", None),
    "staircase-manuscript/input-manifest.json": ("bff337d335a1a14ab806414eb5f38a61c4d275dbecfdfb981f39b61a289da3c0", None),
    "fresh-algebra-discovery-r1/candidate.md": ("6b2e14d58ef3e132a666e3cdc6dbb3a2caa53a514301dc30323b6b7cf652c179", 17969),
    "staircase-proof-r1/review.md": ("85cdaff75e27300815f81a28fc709a5714b16fa1941d023f44238b302e549e80", None),
    "staircase-contribution-factory-r1/review.md": ("47de7398e889efb726de5e993384ace4e3e1f83d095e37a68a309f5aaa64b060", None),
    "staircase-manuscript/inputs/provenance/i21-signed-saxl-dominance.md": ("607c2c3296b6e020d8f0ae12526ee593ba3369e00fa5c4f393e53ee5b6936b6a", None),
}

M = "staircase-manuscript/"
P = M + "inputs/primary/"
C = M + "inputs/pinned/A-Cyclic-Polytabloid-Proof-of-Saxls-Conjecture-September-24-2026/"
U = M + "inputs/pinned/Universal-Tensor-Squares-for-Symmetric-Groups-September-24-2026/"
PAPER = "fresh-algebra-discovery-r1/inputs/pinned/preprints/A-Cyclic-Polytabloid-Proof-of-Saxls-Conjecture-September-24-2026/build/"

READ = {
    M + "main.tex": "full (194 lines), line-by-line reconstruction",
    M + "references.tex": "full",
    M + "main.pdf": "all 6 pages rendered at 120 dpi from a fresh copy and visually inspected",
    M + "output-manifest.json": "hash only; checked by package verifier on copy",
    M + "input-manifest.json": "hash only; checked by package verifier on copy",
    M + "README.md": "full", M + "HANDOFF.md": "full", M + "RIGHTS.md": "full",
    M + "attribution-response.md": "full", M + "source-to-claim.md": "full",
    M + "formal-scope.json": "full", M + "metadata.json": "full", M + "public-files.json": "full",
    M + "support/PROVENANCE.md": "full",
    M + "support/reproduce.py": "full", M + "support/build.py": "full",
    M + "support/verify_package.py": "full",
    M + "support/proof_controls.py": "executed on copy only (via reproduce.py)",
    M + "support/coordinate_controls.py": "executed on copy only (via reproduce.py)",
    M + "staircase-manuscript-public.zip": "member list only (32 names; no inputs/, no I21)",
    P + "bryant-kovacs-1972.txt": "full (Lemma (i)-(iii), proofs, Theorems 1-2)",
    P + "harman-ryba-2023.txt": "full (Thm 1.1, Def 2.2, Ex 2.3, Thm 2.4, Cor 2.5, Section 3, Rem 3.3)",
    P + "ikenmeyer-2015.txt": "lines 1-60 and 180-440 (Sections 4-5, beta, eq. (5.2), uniqueness argument)",
    P + "bbs-2021.txt": "lines 1-20, 295-320 (Strengthened Saxl Conjecture, p.1029), 1299-1400 (Section 5, Thm 5.2)",
    P + "bessenrodt-bowman-2023.txt": "lines 1-12, 130 (Thm D header), 380-392, 460-482 (Thm 3.7, Rem 3.8)",
    C + "dominance.tex": "full (thm:cyclic-saxl, dom:pair-letter-map, dom:square-minimum, dom:noncancellation, dom:permutation-quotient)",
    C + "specht-tools.tex": "lines 33-100 (position tensors, lem:polytabloid)",
    C + "README.md": "full",
    U + "introduction.tex": "lines 1-40 (companion thm:main)",
    PAPER + "paper.tex": "lines 1-80 (section order and theorem counter: Theorem 3.1 numbering)",
    PAPER + "sections/introduction.tex": "lines 1-30",
    M + "inputs/provenance/i21-signed-saxl-dominance.md": "lines 1-140 (Sections 1-2.3, including 2.1)",
    "fresh-algebra-discovery-r1/candidate.md": "hash only; content via appended reviews and the manuscript",
    "staircase-proof-r1/review.md": "hash only; content as appended to brief",
    "staircase-contribution-factory-r1/review.md": "hash only; content as appended to brief",
    "staircase-parent/glm-disposition.json": "full",
    "staircase-formal-v1/README.txt": "lines 1-60",
    "staircase-formal-v1/paper-correspondence.json": "full",
}


def main():
    records = []
    for rel, extent in sorted(READ.items()):
        data = (CAMPAIGN / rel).read_bytes()
        rec = {"path": "frontier/campaigns/2026-10-14/" + rel, "bytes": len(data),
               "sha256": hashlib.sha256(data).hexdigest(), "read": extent}
        if rel in BRIEF:
            exp, size = BRIEF[rel]
            assert rec["sha256"] == exp, rel
            if size is not None:
                assert rec["bytes"] == size, rel
            rec["matches_brief"] = True
        records.append(rec)
    for rel in BRIEF:
        assert rel in READ, rel
    upstream = json.loads((ROOT / "sources/upstream.json").read_text())
    assert upstream["commit"] == "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"
    print(json.dumps({"inputs": records, "count": len(records),
                      "pinned_openai_commit": upstream["commit"],
                      "brief_hashes_verified": len(BRIEF), "status": "PASS"}, indent=1))


if __name__ == "__main__":
    main()
