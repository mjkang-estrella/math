#!/usr/bin/env python3
# Copyright 2026 Myeongjin Kang. MIT License.
"""Write input-hashes.json and outputs.json for this review directory."""
import hashlib
import json
import os

ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..", "..", ".."))
HERE = "frontier/campaigns/2026-10-14/staircase-contribution-factory-r1"
C = "frontier/campaigns/2026-10-14"
F = C + "/fresh-algebra-discovery-r1"

INPUTS = [
    ("AGENTS.md", "full", "rules"),
    ("sources/upstream.json", "full", "pin"),
    ("frontier/NEW-TEN-2026-10-14.md", "full", "campaign standard"),
    (C + "/tasks.json", "fields campaign/target/newAccepted and last task records", "status"),
    (F + "/candidate.md", "full, lines 1-151", "frozen candidate"),
    (F + "/output-manifest.json", "hash only", "frozen manifest"),
    (F + "/literature-comparison.md", "full", "author comparison"),
    (F + "/source-contracts.json", "full", "author source contracts"),
    (F + "/exploration-notes.md", "full", "rejected approaches"),
    (F + "/RIGHTS.md", "full", "rights"),
    (F + "/LICENSE-CODE", "header", "license"),
    (F + "/inputs/primary/harman-ryba-2023.txt", "full", "primary"),
    (F + "/inputs/primary/ikenmeyer-2015.txt", "lines 200-429", "primary"),
    (F + "/inputs/primary/bbs-2021.txt", "lines 255-334, 1300-1389", "primary"),
    (F + "/inputs/primary/bessenrodt-bowman-2023.txt", "lines 1-140, 330-479, 1555-1579", "primary"),
    (F + "/inputs/pinned/preprints/A-Cyclic-Polytabloid-Proof-of-Saxls-Conjecture-September-24-2026/build/sections/dominance.tex", "full", "pinned source"),
    (F + "/inputs/pinned/preprints/A-Cyclic-Polytabloid-Proof-of-Saxls-Conjecture-September-24-2026/build/sections/specht-tools.tex", "full", "pinned source"),
    (F + "/inputs/context/frontier/iterations/i21-signed-saxl-dominance.md", "lines 1-120", "project antecedent"),
    (F + "/inputs/context/sources/CONTENTS.md", "keyword search", "catalogue"),
    (F + "/inputs/context/sources/preprints-tree.json", "keyword search", "tree"),
    (C + "/staircase-proof-r1/review.md", "full", "proof gate PASS"),
    (C + "/staircase-proof-r1/output-manifest.json", "hash only", "proof manifest"),
    (C + "/staircase-parent/proof-disposition.json", "full", "proof disposition"),
    (C + "/staircase-parent/candidate-authentication.json", "full", "parent authentication"),
    (C + "/staircase-parent/contribution-review-brief.md", "full", "original brief"),
    (C + "/staircase-parent/preliminary-reading.md", "full", "parent reading"),
    (HERE + "/external/bryant-kovacs-1972.pdf", "full (via text extraction)", "primary, retrieved for this review; third-party rights"),
    (HERE + "/external/bryant-kovacs-1972.txt", "full", "pdftotext -layout extraction"),
]

OUTPUTS = ["review.md", "sources.md", "coordinate_controls.py", "coordinate-controls.json",
           "make_manifests.py", "input-hashes.json"]


def rec(rel):
    p = os.path.join(ROOT, rel)
    with open(p, "rb") as fh:
        data = fh.read()
    return {"path": rel, "sha256": hashlib.sha256(data).hexdigest(), "bytes": len(data)}


def main():
    inputs = []
    for rel, extent, role in INPUTS:
        r = rec(rel)
        r["read_extent"] = extent
        r["role"] = role
        inputs.append(r)
    doc = {
        "review": "staircase-contribution-factory-r1",
        "date": "2026-10-14",
        "role": "independent contribution gate; no proof verdict, no acceptance, no count, no subagents",
        "verdict": "SUBSTANTIAL (narrow), conditional on proof PASS and on Bryant-Kovacs attribution",
        "pinned_upstream": {"repository": "https://github.com/openai/math",
                            "commit": "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb"},
        "expected": {
            "candidate.md": "6b2e14d58ef3e132a666e3cdc6dbb3a2caa53a514301dc30323b6b7cf652c179",
            "output-manifest.json": "79b0fcddd7d33b980d07a951b5152ecc6a1c19e5fe8d5f3bb5e7464562f4dec9",
            "proof review.md": "85cdaff75e27300815f81a28fc709a5714b16fa1941d023f44238b302e549e80",
            "proof output-manifest.json": "192f9baa0e389f2f994da0213cee2436d09904b3539a9bef04ba9bc13dfbbba5",
        },
        "external_urls": {
            "bryant-kovacs-1972.pdf": "https://archives.maths.anu.edu.au/people/Kovacs/K033.pdf",
        },
        "inputs": inputs,
    }
    exp = doc["expected"]
    got = {os.path.basename(r["path"]) if "staircase-proof-r1" not in r["path"] else "proof " + os.path.basename(r["path"]): r["sha256"] for r in inputs}
    for k, v in exp.items():
        assert got[k] == v, (k, got.get(k), v)
    with open(os.path.join(ROOT, HERE, "input-hashes.json"), "w") as fh:
        json.dump(doc, fh, indent=1)
        fh.write("\n")
    out = {"review": "staircase-contribution-factory-r1",
           "verdict": doc["verdict"],
           "primary_candidate_sha256": exp["candidate.md"],
           "files": [rec(HERE + "/" + n) for n in OUTPUTS],
           "note": "outputs.json does not list itself; external/ holds third-party inputs, listed in input-hashes.json"}
    with open(os.path.join(ROOT, HERE, "outputs.json"), "w") as fh:
        json.dump(out, fh, indent=1)
        fh.write("\n")


if __name__ == "__main__":
    main()
