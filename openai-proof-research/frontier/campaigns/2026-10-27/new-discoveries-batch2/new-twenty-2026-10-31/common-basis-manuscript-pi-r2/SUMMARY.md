# common-basis-manuscript-pi-r2 — DRAFT manuscript and dossier for MathDB 332371

Status: **DRAFT, zero credit.** The independent source/mathematics/significance review
(common-basis-source-review-r1) returned a qualified PASS with explicit limits and was
adopted by the root (common-basis-parent-source-integration-r1.json) with no acceptance.
A separate strict Lean-fidelity audit was RUNNING in common-basis-fidelity-pi-r2 at
authoring time and was not polled or copied. The root manuscript review, the final
extracted replay, and acceptance all remain pending. Nothing here upgrades the author
replay to independent evidence.

## Deliverables

- `paper.pdf` — 6-page draft manuscript (rendered and visually inspected page by page; QA in `qa/`).
- `paper-src/build_paper.py` — the generator; every number is derived from the frozen certificate.
- `source-only-proof.zip` — portable source package: the 12 immutable Lean modules
  (byte-identical to `expanded-corpus-r250/lean-source-manifest.json`, verified), the
  machine-checkable certificate, the ordinary checker, and a sanitized-environment
  `replay.sh` driven by user-supplied `LEAN_BIN`/`LEAN_PACKAGES`. No oleans, no caches, no symlinks.
- `full-dossier.zip` — everything: the source package, paper and source, the exact raw MathDB
  record, author evidence (results/ARTIFACTS/replay-result/lean-status), the independent review
  with its limits, the root integration record, primary sources with HTTP receipts.
- `archive-manifests.json` — SHA-256 of every file inside both archives, plus `MANIFEST.sha256.json`
  and `hashes.txt` for the top-level deliverables.
- `results.json` — structured record (credit 0, pending items explicit).
- `REPRODUCE.md` — what was run here, what was not, and how to rerun.
- `receipts/frozen-before.json`, `receipts/frozen-after.json` — all 998 bound files verified
  byte-identical before and after the work.

## Mathematical content (all rederived in this lane from the frozen certificate)

Rank-4 matroid on E={0..8} with columns 9,6,4,11,6,14,5,1,12 (4-bit); 76 of the 126 four-subsets
are bases; 12,736 exchange obligations all pass; 23 circuits, loopless, connected, parallel pair
{1,4}. x=1, y=6. E\{1} = {0,2,3,5} ⊔ {4,6,7,8}; E\{6} = {0,1,2,7} ⊔ {3,4,5,8}. The bases
extendible to a partition of E\{1} number 32; for E\{6}, 24; the lists are disjoint, giving the
complete common-base obstruction, not merely a failure of the displayed partitions. The paper
states the exact negation of Conjecture 2.5 of Lasoń (Selecta Math. 27, art. 18, 2021 =
Conjecture 13, arXiv v2/v3) for k=2, r=4 and no more.

## Explicit non-claims

No acceptance; no minimality (neither 9 elements nor rank 4); no new-underlying-matroid,
simple-matroid, or infinite-family claim; no worldwide priority; no refutation of any White
conjecture (the source implications are one-way); no established reduction from Larson's
arXiv:2607.02208 (rank-9, 18 elements, different theorem) — its relationship is described,
not adjudicated. The 12-module Lean replay was NOT rerun in this lane; the independent strict
audit was running separately. Any replay numbers cited in the paper are flagged author-supplied.
