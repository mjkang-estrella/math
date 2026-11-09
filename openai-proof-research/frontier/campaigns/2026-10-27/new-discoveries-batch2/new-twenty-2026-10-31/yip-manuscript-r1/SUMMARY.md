# DRAFT — MathDB 355956 manuscript and reproduction dossier

This is a draft ready for the root's manuscript review and final replay. It carries **zero accepted credit**: the root alone accepts, and the campaign count stays at **5/20 beyond 39**. MathDB 355701, which shares the author packet, is on root HOLD; it is not presented as a result, and no 355701 material is bundled.

## Claim

For q = 5^8 and d = 3, the only admissible r is 1. In every field with 5^8 elements, F_5 is a clique of GP(5^8, 3) but not a maximal clique. The vertex x = 2θ + 4θ^2 + θ^3, with f(θ) = 0 for f = X^8 + X^7 + 2X^6 + 2, extends it.

This refutes Yip's conjecture, stated as:
- J. Algebraic Combin. 56 (2022), arXiv:2101.09652, Conjecture 1.4;
- Algebr. Comb. 6(4) (2023), arXiv:2209.00864, Conjecture 1.1.

Theorem 1.2 of the ALCO paper still stands: its hypothesis fails here, since 5 ≤ 49. The case also lies outside Yip's computer checks (n ≤ 5, and n = 6 with q ≤ 17).

## Deliverables

**Paper.** `paper.pdf` is a 6-page draft built from `write_paper.py` (ReportLab; no LaTeX engine is available here). It contains:
- definitions and the exact conjecture with its quantifiers;
- a hand-checkable proof: the Frobenius matrix and chain tables, the irreducibility argument via the Frobenius orbit, the cube and inverse certificate table, why −1 is a cube, and the extension argument;
- a formal correspondence table covering every definition and key lemma;
- a three-way separation into Lean-certified content, ordinary-proof-only content and computation-only diagnostics;
- trust and novelty limits, AI-assistance disclosure, and seven references drawn only from sources actually read.

There is no human author or affiliation. All six pages were rendered and inspected one by one; the images and receipt are in `qa/`. Problems found during QA were fixed and are logged there.

**Ordinary proof.** `PROOF.md`.

**Archives.**
- `source-only-proof.zip` (21 members) contains:
  - the literal module `proof/Yip355956.lean`, byte-identical to the author's (sha256 0ccf6655…ee9d7be);
  - the labelled reviewer supplements `ReviewAudit.lean` and `ReviewSanity.lean`;
  - the raw MathDB line and the primary TeX and e-print copies, with `sources/RECEIPTS.json`;
  - `pins.json`, the portable `replay.py` (LEAN_BIN and LEAN_PACKAGES), `safe_extract.py`, `diagnostic.py`, `REPRODUCE.md`, `PROOF.md` and `source-manifest.json`.
- `full-dossier.zip` adds the paper and QA, the fresh replay receipts, the frozen bindings, verbatim copies of 355956-only evidence, and labelled extracts of the joint review and adjudication files. The hashes of both archives are in `archive-hashes.json`.

## Verification

All of the following ran on a new safe extraction of `source-only-proof.zip` (in `fresh-extraction/`), and the replay passed:
- **Build and kernel check.** A strict `lean -j1 -DwarningAsError=true` build produced an empty log, and `leanchecker` passed.
- **Declaration audit.** All **40** constants in the module data were audited, including generated ones, and the set is identical to the technical review's 40 names. Each was checked for origin, full `pp.all` type, `value? true` body, safe and non-partial status, and transitive axioms. The only axioms that appear are **propext, Classical.choice and Quot.sound**.
- **Endpoints.** Sanity re-statements of both endpoints passed, as did a non-vacuity check (`GaloisField 5 8` has cardinality 5^8).
- **Negative controls.** All five were rejected as expected: wrong certificate (`ring failed`), wrong endpoint, `sorry`, forbidden axiom, and malformed olean (which tests the header only). A positive twin, the verbatim certificate, was accepted.
- **Token scan.** No forbidden tokens were found.
- **Exact diagnostic.** The standard-library diagnostic passed. It confirmed r = [1], that the Lean Frobenius chain and all 10 certificates are correct, that f is irreducible, the 25-clique, that θ is primitive, and that F_25 and F_625 are not cliques. It also found **960** extension vertices, none in F_625. These diagnostics corroborate the result but are not premises.

Receipts: `fresh-extraction/replay-receipts/` and `receipts/replay-crosscheck.json`.

**Frozen inputs.** I bound **516** frozen input files before and after: the author lane, the technical review, the root adjudication and the source review r2. **All 516 are unchanged** (`receipts/frozen-comparison.json`). Copy identities are in `receipts/copied-evidence-identity.json`.

**Post-packaging checks** (lane files outside the ZIPs, since they verify the ZIPs themselves):
- `full-dossier-verification.json`: a fresh safe extraction of `full-dossier.zip` matched all manifest hashes with no unlisted files, and the embedded source ZIP matched. No content file carries 355701 material; `frozen-*.json` list held-lane path names and hashes only.
- `frozen-final-check.json`: all 516 bindings are still unchanged after packaging.
- `receipts/development-log.md`: records the scratch trials, including the RSS-guard kill and the audit speed fix.

## Resources (flag for root)

Every call used at most 2 CPUs, CPU 120 s, wall 140 s, AS 64 GiB and MALLOC_ARENA_MAX=2, and ran inside a systemd scope with MemoryMax=6G, MemorySwapMax=0 and CPUQuota=200%. The longest call took 9.1 s, and the whole replay driver took 35 s.

**Deviation to confirm.** `import Mathlib` maps about 6–7 GB of clean, read-only `.olean` pages, and total VmRSS counts them. Total VmRSS therefore peaked at **7.45 GB**, above the 6 GiB figure. Private RSS (RssAnon + RssShmem) peaked at **0.85 GB**. I applied the 6 GiB sampled guard to private RSS and report both quantities. My first build attempt, with the guard on total VmRSS, was killed at Mathlib import before elaboration started. Please confirm that this reading of "sampled RSS 6 GiB" is acceptable.

## Limits

**Trust.**
- The Lean kernel and compiler, and the prebuilt Mathlib oleans, are trusted. Nothing upstream was rebuilt.
- `leanchecker` comes from the same installation as `lean`.
- Statement fidelity rests on human reading; the independent technical review agrees with it.

**Novelty.** No claim of worldwide priority is made. The following were not read: Yip's thesis, three OpenAlex-listed citers of the JACO paper, and the MathDB/Palomar state (HTTP 403). The source review's bounded limits are preserved. The author lane's sweep (q ≤ 5·10^6, only this failure) is reported but was not re-run.

## Conduct

- No child agents, git, publication, uploads, external messages, browser use or new HTTP retrievals.
- No edits outside this lane.
- No jobs remain running.
