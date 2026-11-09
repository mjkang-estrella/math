# Expanded corpus r120 handback

One complete mathematical and Lean counterexample candidate is ready for root review: **355525**, the nonexistence conjecture for binary quasi-group codes with permutation automorphism group C2. The explicit length-12 code has dimension 6; its full coordinate-permutation automorphism group is exactly the identity and the fixed-point-free swap of all six coordinate pairs. It contradicts the intended source Conjecture 4.9, not a weakened paraphrase. No acceptance or discovery credit is asserted. Campaign counts and shared files were not changed.

Read `355525-proof.md` for the matrix, complete ordinary proof, source scope, semantic correspondence and bounded prior-art limits. `lean/Code.lean` contains the literal endpoint `CodeCounterexample.source_conjecture_refuted`. It uses an actual binary submodule, its actual permutation stabilizer subgroup, a multiplicative group isomorphism with C2, and a nontrivial freely acting subgroup. The code enumeration, invariant-signature argument, exhaustiveness of the pair-swap classification, and all semantic bridges are proved. Kernel `decide` is the only computational proof method.

## Verification and packet

- Source-only archive: `355525-lean-source.zip`; exact archive/source hashes and fresh extraction location are in `outputs/package.json`.
- `fresh-packet/` was created empty and received only the two sanitized Lean files from the archive.
- `logs/fresh-build.receipt.json`: strict `-DwarningAsError=true` extracted build passes.
- `logs/fresh-leanchecker2.receipt.json`: leanchecker passes. The first leanchecker attempt failed because PATH lacked lean; the corrected script and successful rerun are retained.
- `logs/fresh-audit.log`: all 81 local declarations, including generated declarations, audited; zero declarations with nonallowed axioms. The endpoint depends only on propext, Classical.choice, Quot.sound.
- Lean 4.34.1; pinned read-only mathlib cache d13f23b723b8a846827a245b89c10fc7d3f11612. No full dependency rebuild is claimed.

All process logs, including unsuccessful development attempts, are retained. Initial broad Mathlib import exceeded the monitored RSS cap and was stopped; targeted imports reduced successful replay peaks to about 2.8 GiB. Numerical and Lean processes used affinity at most 2 CPUs, CPU 120 s, wall 140 s, monitored process-group RSS 6 GiB, MALLOC_ARENA_MAX=2. Lean uses -M3500; the final replay also uses -j1. There are no background jobs left by this lane. The wrapper samples RSS; it is not a cgroup/transient-peak guarantee.

## Material acceptance gaps

The journal version of the source (DOI 10.1142/S0219498825501373) returned 403 and was not retried or bypassed. Its full body has not been reconciled with the accessible arXiv version. Classical realization papers by Phelps (1985) and Knapp–Schmid (1980) have unread original bodies; abstract group realization does not by itself certify a free coordinate action, but their constructions need independent subsumption review. These are unresolved novelty/source gaps. The formal and mathematical candidate must not be self-accepted. Independent adversarial review, significance judgment and root acceptance remain separate.

## Other reserved targets

`results.json` has exactly 20 ID-keyed entries, each retaining the literal corpus statement, chunk path and one-based line, chunk/raw/statement hashes, primary-source hashes/receipts, actual review depth, attempt, precise finite coverage or an explicit coverage gap, and remaining lemmas.

- **354565** is already resolved by Adenbaum's Theorem 4, arXiv:2308.08757, published EJC 2025. The final proof body was read.
- **356015** follows from the published Diskin–Samotij regular-product inequality in arXiv:2407.02058, Section 3.3. The theorem/proof and specialization were read.
- **354011** has a short inverse-matrix route from its source's Gaussian-period autocorrelation identities; not proposed for discovery credit.
- **381794** has a short affine product description as a permutahedron times a cube. An exact m=6 vertex-set check covered 46080 vertices. No Lean endpoint or discovery credit is proposed for this routine product route.
- **356253** received a sustained exact coefficient sweep: 1872 parameter triples a/b=1..24,1<=N<=M<=12, all coefficients through degree 2500. No failure. The 2026 successor's diagonal reduction and signed-block obstruction were read; the general middle-range positivity gap remains.
- **355824** received 500 exact noncommutative matrix-label trials for each p=4..10 over M2(F1009), beyond the source's reported p=3 computation. Every defined iteration satisfied the conjecture; undefined inversion cases are recorded separately.
- **354983** received exact minimax on the grids listed in results.json, including every 4xm,m=4..10,5x7 and 6x6. Every tested initial position satisfies the strict first-player inequalities. No general strategy was found.
- **355377** received exhaustive multiset upper-bound checks at ten (q,t) pairs, including all 4495 length-28 multisets for (q,t)=(4,16). All passed. Some are source-proved instances and have no discovery value.

The remaining analytic/asymptotic and complexity targets have source-backed parked dispositions. In particular, 356828 is a maximum-independent-domination question in the intended source; the paraphrase's maximal-versus-maximum wording is not a qualifying refutation. No exact norm optimization was implemented for 355040, no certified digamma-order sweep for 355348, and no beyond n=5 generic CE face-lattice enumeration for 356261. These finite-search gaps are explicit; this is not a claim of exhaustive technical coverage.

## Provenance and prior art

Raw lines including newline are in `raw/`; extraction and historical prose/result screens are reproducible. Historical substring hits include hash/numeral coincidences and assignment metadata; no old exclusion matching a reserved ID/title was found in that bounded screen. This does not establish global nonreview.

Live registry HTTP receipts record OpenAI/math HEAD 4eaee87548250b2682affda7d05d947c05554bae and Omega HEAD 17eb8a60418c6729f0dc56d3688039b2a8b6a093. Complete nontruncated Omega D5 and Problems trees were fetched at the latter head. Keyword/ID path screens are retained and explicitly are not a review of all registry proof bodies. Primary source bodies and dated web-search results are in `sources/` and `outputs/web-*.json`. No 403/429 route was retried. No browser tabs, uploads, messages, git operations or child agents were used.

To reproduce the formal replay, run each stage through `scripts/limited.py`: `scripts/replay.py build`, then `check`, then `audit`. Numerical searches are `code_search.py`, `code_verify.py`, `positivity.py`, `delta.py p`, `influence.py n m`, `egz.py` and `wachs.py`, always with python3 -I under the same wrapper. Mathematical diagnostics are not substituted for the Lean theorem.
