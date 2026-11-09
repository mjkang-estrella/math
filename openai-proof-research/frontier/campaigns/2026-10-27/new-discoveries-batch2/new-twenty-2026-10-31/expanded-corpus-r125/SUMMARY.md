# expanded-corpus-r125: summary (Claude investigator lane; no Lean, lake or SAT/ILP run)

Reserved IDs: 20, between 342735 and 344302 (`reservation.json`). Exact literal records are in `raw/<id>.jsonl`. Provenance (chunk path, 1-based line, chunk, raw and statement SHA-256) is in `extracted.json` and in every `results.json` entry.

The prior-campaign history scan (`history-matches.txt`) found only hash-substring noise and root's launch note; no earlier exclusions apply. Nothing here is self-accepted.

## Candidates for root

### 1. 344002 (Graham, arXiv:1910.00924, Conjecture 3.3: all extreme n-subsets of Z_p are equivalent): exact counterexample candidate with prior-art risk

- **Counterexample.** Z_71 has at least three affinely inequivalent 25-element extreme sets. They are the supports of ±1 sequences with autocorrelation 25δ₀, i.e. circulant weighing matrices CW(71, 25).
- **Extremality.** Checked directly from Graham's Definition 1.1: |μ̂| ≡ 5, ‖μ‖ = 25, # supp μ = 25.
- **Inequivalence.** The affine invariant #{(x, y) ∈ E²: 2y − x ∈ E} is 225 for one set and 205 for another. Exhaustive affine canonical forms confirm the three classes are pairwise distinct.
- **Files.** Proof: `proof-344002.md`. Certificate: `scripts/cert344002.py` with output `outputs/cert344002.json`. UNCOMPILED Lean draft: `lean-draft-344002/Graham344002.lean` (literal definitions; finite facts by `decide`).
- **Risk.** Strassler (J. Statist. Plann. Inference 73, 1998) reports four inequivalent CW(71, 25). I could not read the body because ScienceDirect was not accessed. If its printed rows have inequivalent supports, the contradicting objects are published, which is the 355525 explicit-example pattern. The CW(31, 16) pair from Adin, Epstein and Strassler has equivalent supports (checked).
- **Smaller primes.** A numerical scan of all affine classes for p ≤ 17 found no counterexample; this is a diagnostic only.

### 2. 344302 (Zhu, arXiv:1910.12818, down-up-down-up conjecture for dd({i}; n)): full ordinary proof candidate, no Lean

- **Method.** An exact convolution identity (proved by Möbius inversion over decreasing-run compositions) gives a bivariate generating function A(x)A(y)T(x, y) with A = 1/f. Here f(z) = (2/√3)e^{−z/2} sin(π/3 − √3z/2) has only real simple poles x₀(1 + 3k).
- **Main term.** (3/2)τ(−1/2)^p[1 + 2(−1/2)^{q−p}] with τ ≈ 0.0324958 > 0. The bracket vanishes exactly at the even-n middle, as the symmetry requires.
- **Error bounds.** Interval-certified (`scripts/dd_rigorous.py`, `outputs/dd-rigorous-output.txt`). They close every n > 200: Case B covers p ≥ 20, and Case A covers p ≤ 40 using exact U_p values.
- **Finite range.** Exact DP verifies every 4 ≤ n ≤ 200.
- **Prior state.** Hänni (arXiv:2011.14360) proved only the first three inequalities, and only for large n.
- **Files.** `proof-344302.md`.
- **Lean.** Not attempted: it needs Cauchy estimates and certified transcendental bounds. Significance is modest (a PRIMES paper conjecture); root decides.

## Sustained route without a candidate

**343628 (Bujtás–Iršič–Klavžar: minimally γ_g-imperfect graphs).**

- **Search.** I ran a twin-aware exhaustive search built on the source's polynomial recognizer, which was validated against brute-force game values. It reproduces the source Table exactly for n ≤ 9.
- **Beyond the source.** It extends the verified range to n = 10 and n = 11: there are 98,319 γ_g-perfect graphs on 10 vertices, and the only minimally imperfect graphs on 10 and 11 vertices are the antiholes. See `outputs/gg-summary.json` and `logs/gg-*.log`.
- **Reformulation.** In complement form, the conjecture says the minimal induced members of {graphs with no false twins, min degree ≥ 2, and two vertices with disjoint neighbourhoods} are exactly C_n (n ≥ 5), the house, the domino and the six F̄ᵢ. For n ≥ 7 a non-cycle such graph is HHD-free (house-, hole- and domino-free) and weakly chordal.
- **Status.** No proof was completed; parked.

## Other dispositions (see `results.json`)

**Published, registry or source resolutions:**

- 342735: Omega registry proved, `SilverSlopeAbelianPeriods` at HEAD bbd7a670.
- 342741: arXiv:2307.12401.
- 342757: disproved by arXiv:2609.23544.
- 342972: false by its own source, via an equivalence theorem plus the source's counterexample to Raspaud's conjecture.
- 342976: arXiv:1911.00230.
- 343489: Janzer, arXiv:1911.03421.
- 343506: Marsh, arXiv:2608.12526.

**Excluded as withdrawn or ill-posed:**

- 343244: the integral conjecture is commented out in v4.
- 344004: qualitative, not well posed.

**Parked:**

- 342782: probabilistic.
- 343124: famous Bang-Jensen–Thomassé conjecture.
- 343210: asks for infinitely many primes.
- 343471: 3-adic α-tree stays consistent for n ≤ 2200, with α ≡ 116 (mod 3⁵) forced.
- 343472: open; the source covers only a special case.
- 343646: analytic.
- 343796: polyhedral computation too heavy for the caps.
- 344003: no certifiable mechanism.

## Registries, sources and receipts

- **arXiv.** Abstract pages for all sources, with every version checked, are in `sources/abs`; hashes are in `sources/abs-sha256.txt`. E-prints, including multiple versions where they exist, are in `sources/eprint`; hashes are in `sources/eprint-sha256.txt`.
- **Omega.** Live HEAD was bbd7a670 (2026-11-03 09:20Z), changed from root's b576c901. The compare (`sources/registries/omega-compare-…json`) shows 25 unrelated files. The complete cached D5/Problems trees at b576c901 were path-screened by keyword and author. The live tree listing is truncated, so it is a partial screen only.
- **OpenAI/math.** HEAD 4eaee875 is unchanged; the cached complete preprint listing was screened.
- **Access limits.** The EMIS univie mirror returned 503 and was not retried; the TCD mirror served Arasu–Ma. ScienceDirect was not accessed.

## Resources and process notes

- **Caps.** Every computation ran sequentially under `scripts/limited.py`: 2 CPUs, CPU 120 s, wall 140 s, sampled RSS 6 GiB, MALLOC_ARENA_MAX=2. Receipts are in `logs/*.receipt.json`.
- **Exceptions.** One run (`ext-17`, p = 17 for n ≥ 11) hit the CPU cap and was rerun as `ext-17b`. Two runs were briefly backgrounded by the harness while still capped, and no other process ran concurrently with them. No background job remains.
- **Python.** numpy, scipy and mpmath came from the existing user site-packages (path appended explicitly under `-I`); nothing was installed.
- **Write discipline.** One small JSON helper was written to the session scratchpad (outside the repo), not to the lane. No git operations, uploads, messages or browser tabs.
