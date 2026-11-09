"""Temporary git repository shaped like dlp-research, for tests only."""

from __future__ import annotations

import os
import subprocess
import tempfile

STATE = """# Research checkpoint

Status: active, fixture phase after toy milestone
(2026-10-07). Complete solver costs remain unproved.
No faster ECDLP algorithm or cryptographic break has been discovered.

## Current live work

- Writer A owns Research/Toy.lean; no query code.
- Reviewer B checks W001.

## Established milestones

- `abc1234`, W001: toy baseline.

## Current validation and remaining assumptions

Current `./scripts/check.sh` passed: 3 named theorem audits and smoke output.
Open prerequisites: everything end-to-end is blocked on cost accounting.

## Next distinct step

Write W002.
"""

AUDIT = """import Research

#print axioms Research.Baseline.scan_comparisons_le
#print axioms Research.Toy.correct
#print axioms Research.million_gpu_week_below_reference
"""

SECP = """namespace Research.Secp256k1
def n : Nat := 0xFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141
end Research.Secp256k1
"""

W001 = """# W001: toy baseline

Date: 2026-10-07. Status: independently reviewed finite experiment; no speedup.

## Hypothesis and scope

H1: the toy solver works on every scalar.

Body with <script>alert(1)</script> and [link](javascript:alert(1)).
"""

W001_JSON = '{"scope": "toy only", "rows": [{"curve": {"q": 7}, "secrets_tested": 7, "exhaustive": {"adds": 6, "max_sort_plus_lookup": 7}, "linear_bsgs": {"adds": 5, "max_sort_plus_lookup": 7}, "ordered_bsgs": {"adds": 5, "max_sort_plus_lookup": 13}}]}'

README = "# Fixture\n\nproved to return every scalar\n  d with exactly d+1 equality tests (at most q).\n"

MANIFEST = {
    "schema": 1,
    "reviewed_findings_through": "W001",
    "problem": {"name": "toy", "order_source": "Research/Secp256k1.lean", "order_symbol": "n"},
    "classical_references": [
        {"id": "rho", "method": "rho", "formula": "0.886 sqrt", "log2_from_order": {"kind": "sqrt", "coefficient": 0.886}},
        {"id": "ex", "method": "exhaustive", "formula": "n", "log2_from_order": {"kind": "linear", "coefficient": 1.0}},
    ],
    "rounded_reference_log2": 128,
    "repo_results": [
        {"id": "good", "title": "ok", "category": "proved",
         "evidence": {"source": "README.md", "quote": "proved to return every scalar d with exactly d+1 equality tests (at most q)",
                      "findings": ["W001"], "theorems": ["Research.Baseline.scan_comparisons_le"]}},
        {"id": "stale", "title": "stale", "category": "proved",
         "evidence": {"source": "README.md", "quote": "this sentence is not in the readme",
                      "findings": ["W999"], "theorems": ["Research.Nope.missing"]}},
    ],
    "estimator": {"default_log2_work": 128},
}


def git(repo: str, *args: str) -> str:
    env = {**os.environ, "GIT_AUTHOR_NAME": "Fixture", "GIT_AUTHOR_EMAIL": "f@example.invalid",
           "GIT_COMMITTER_NAME": "Fixture", "GIT_COMMITTER_EMAIL": "f@example.invalid"}
    return subprocess.run(["git", "-C", repo, *args], check=True, capture_output=True, text=True, env=env).stdout


def write(path: str, text: str) -> None:
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "w", encoding="utf-8") as fh:
        fh.write(text)


class Fixture:
    def __init__(self):
        import json
        self.tmp = tempfile.TemporaryDirectory(prefix="rm-fixture-")
        self.repo = self.tmp.name
        self.research = os.path.join(self.repo, "dlp-research")
        r = self.research
        write(os.path.join(r, "research/STATE.md"), STATE)
        write(os.path.join(r, "Audit.lean"), AUDIT)
        write(os.path.join(r, "README.md"), README)
        write(os.path.join(r, "Research/Secp256k1.lean"), SECP)
        write(os.path.join(r, "research/findings/W001-toy.md"), W001)
        write(os.path.join(r, "research/findings/W001-results.json"), W001_JSON)
        write(os.path.join(self.repo, "secret.txt"), "TOP SECRET")
        self.manifest = os.path.join(self.repo, "manifest.json")
        write(self.manifest, json.dumps(MANIFEST))
        git(self.repo, "init", "-q", "-b", "main")
        git(self.repo, "add", "-A")
        git(self.repo, "commit", "-q", "-m", "research: establish toy baseline")

    def path(self, rel: str) -> str:
        return os.path.join(self.research, rel)

    def commit(self, message: str) -> None:
        git(self.repo, "add", "-A")
        git(self.repo, "commit", "-q", "-m", message)

    def close(self) -> None:
        self.tmp.cleanup()
