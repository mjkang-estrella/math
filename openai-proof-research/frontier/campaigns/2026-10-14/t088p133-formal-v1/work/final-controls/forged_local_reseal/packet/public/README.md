# T088P133 — Proposition B deterministic algebra, implementation round 1

This is scoped Lean support, submitted for independent parent review. It proves the universal rational-mixture step of the **original** Proposition B and its one-sided deterministic bounds. It neither formalizes the full frozen theorem nor supplies an independent formal-review verdict, acceptance, contribution assessment, or campaign-count change. Publication/uploads/submissions/contacts/browser work remain STOPPED; campaign context remains 18/20.

For **all real** α, β, p, q, d, P, N satisfying

    α > 0, β > 0, α + β = 2,
    0 < p < 1, q = 1 - p, d ≥ 0, P > 0, N > 0,
    2*d*p^2 < P, 2*d*q^2 ≤ N,

`T088P133.rational_mixture_lt_one` proves

    (1+d)*(p*α/(α+P/p) + q*β/(β+N/q)) < 1.

`rational_mixture_le_one` changes the first moment inequality to ≤ and the conclusion to ≤. No unexplained slack or bracket-sign hypothesis is assumed. `conditional_means` proves q>0, P/p>0, N/q>0 and p(P/p)=P, q(N/q)=N; `moment_lt_iff` and `moment_le_iff` prove the exact moment conversions. The definitions `firstBracket`, `secondBracket`, `mixture` and their identities/sign lemmas are all audited declarations.

With A=P/p, B=N/q the cleared slack is

    F + G,
    F = p*A*β + q*B*α - d*α*β
      = p*β*(A-2*d*p) + q*α*(B-2*d*q) + d*(2*p-α)^2,
    G = A*B - d*(p*α*B + q*β*A)
      = [α*B*(A-2*d*p) + β*A*(B-2*d*q)]/2.

F≥0 and G>0 follow from the actual moment bounds; the strict factor is A−2dp>0 and its multiplier αB>0. Dividing by the positive (α+A)(β+B) proves the result. This is a polynomial alternative to the original square-root/Cauchy–Schwarz proof of F≥0. It does not change the author's proof bytes. There is **no division by d**. Both strict and non-strict support cover d=0.

For p=1, `p_one_bound` proves `(1+d)/(1+P/α)<1` from α,β>0, α+β=2, P>0, 2d≤P. For p=0, `p_zero_bound` proves `(1+d)/(1+N/β)<1` from the symmetric hypotheses. `positive_sum_two_bounds` derives α<2, β<2. The more general `one_sided_lt_one` does not need d≥0; this is an exposed weakening, not an omitted obligation. These endpoint theorems are the reduced rational expressions used in the proof, not probabilistic case assertions.

[COVERAGE.md](COVERAGE.md) maps **every** support declaration and all controls to the use site. The following remain entirely unformalized here: actual-facet geometry; mixed volumes, attainment, coarea, Gamma–Dirichlet; distributions, log-concavity and HNBUE; the exact ten-pattern coefficient certificate and its probabilistic interpretation; continuity, zero/repeated-knot assembly; simplex equality; and the final projection-body theorem. No best auxiliary constant, all-dimensional threshold, or extension of the frozen scope is asserted.

## Validation

The successful source build compiles `T088P133.lean`, `Controls.lean`, and generated `Checks.lean` from fresh local outputs. All 21 support declarations (3 definitions, 18 theorems) and 20 control theorems have elaborated types and `#print axioms` output in `validation/types-axioms.log`. All 41 report only `propext`, `Classical.choice`, `Quot.sound`. There are no warnings, proof placeholders, custom axioms, unsafe declarations, or native computation proof shortcuts in the advertised sources. The scanner and axiom audit are in `rebuild.py`.

The mixed rational example (α,β,p,q,d,P,N)=(2/3,4/3,1/3,2/3,3/2,1/2,4/3) has value **12/13**, with only its first moment strict. The d=0 example has value **1/3**. Non-strict moments can give exactly **1**, so they cannot guarantee strictness. Reason-checked countermodels in Lean retain all other hypotheses and show that deleting either moment bound, α or β positivity, α+β=2, q=1−p, or p<1 can break the bound. Endpoint controls cover d=0, the a=2 equality boundary, zero moment, and a missing moment bound. They are real arithmetic examples, not instances of random variables or polytopes. They do not assert independence/necessity of every listed assumption: e.g. P>0 follows from the strict moment when d≥0; some hypotheses can be weakened.

## Reproduce without network or shared writes

Requirements: Python 3 standard library; Lean **4.34.1**, commit `5045d0056413266e57c625dcd7c365b10e377c52`; trusted, already-built mathlib **d13f23b723b8a846827a245b89c10fc7d3f11612** and the eight pinned auxiliary packages in `lake-manifest.json`. This is a fresh build of **our source files**, not a clean-source rebuild or independent authentication of mathlib binaries. The compiler executable hash and read-only dependency HEAD pins are recorded in the build receipt. The script reads Git metadata directly and never invokes git, Lake, package downloads, or a dependency build. It does not assert tracked-cache cleanliness merely from HEAD.

From the package root (the directory containing FINAL.json):

```sh
python3 -B packet/public/rebuild.py --output "$PWD/work/rebuild-fresh" \
  --lean /home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean \
  --cache /home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages
```

Use a new output path for each invocation. All generated source copies, compiled products, temporary files and logs are constrained to this package's `work/`. `lean-toolchain` and `lake-manifest.json` are pin records; direct Lean invocation is the tested route. A copied/extracted package can be built in its own `work/` with the same external cache. A portable recipient must supply compatible trusted dependencies; no compiled dependencies are bundled.

Run a **trusted copy** of `verify.py` against a candidate package and supply the FINAL, MANIFEST and outsideREPORT SHA256 anchors obtained independently of that candidate (e.g. the implementation handoff). Local hash files alone are not independent anchors:

```sh
python3 -B packet/public/verify.py --root "$PWD" \
  --final-sha256 EXTERNALLY_SUPPLIED_FINAL_SHA256 \
  --manifest-sha256 EXTERNALLY_SUPPLIED_MANIFEST_SHA256 \
  --report-sha256 EXTERNALLY_SUPPLIED_REPORT_SHA256
```

Optionally append `--originals /home/mj-kang/Documents/Dev/math/openai-proof-research` to check all 940 recorded original entries, including exact author/reviewer root layouts, file bytes/modes/link counts and used parent/context files. This option is read-only and is not required to compile portable algebra sources. The verifier itself writes nothing. `integrity_controls.py` accepts the same three anchors and `--output "$PWD/work/copied-controls-new"`; it mutates only copies and checks the precise rejection reason for each case. Artifact checks do not prove mathematics or acceptance.

## Sealing scope

`packet/MANIFEST.json` seals the exact packet path set, file hashes/sizes/modes/link counts, directory modes/link counts, and all public source/reproducibility evidence, excluding the manifest itself. FINAL.json binds that manifest and the outside REPORT.md; **all three hashes must be independently supplied**. FINAL, manifest and outside report must be ordinary mode-0644 single-link files. `work/` is explicitly excluded: it contains development attempts, build products, copied controls, final verification results, and the local portable archive/extraction. No build caches or private copied source/history bodies are portable payloads. No private bodies were copied into this implementation package. Hash-only original inventories are included. The local archive contains only FINAL.json, REPORT.md and packet/.

Copyright 2026 Myeongjin Kang (no affiliation). New original code/Lean MIT; original prose CC BY 4.0. Adapted rebuild code retains attribution in its header and [PROVENANCE.md](PROVENANCE.md). All upstream rights remain unchanged.
