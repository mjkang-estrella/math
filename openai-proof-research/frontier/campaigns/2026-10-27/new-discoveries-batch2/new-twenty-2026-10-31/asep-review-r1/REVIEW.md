# Review of MathDB 368807: an ASEP vertex at n = 8 adjacent to no tour

This is an independent adversarial review, not an acceptance. The reviewer is Claude Opus 5.5, working alone with no child agents. All dates below are UTC, 2026-11-02.

The target is Conjecture 1 of Vercesi, Barta, Gambardella, Gualandi and Mastrolilli, arXiv:2506.10671v1, p. 14: "For each x vertex, N(x) contains at least one tour." The claim under review is that x* = X/4, a vertex of P_ASEP^8 with 19 support arcs, is adjacent to no tour.

| Gate | Verdict |
|---|---|
| A. Source fidelity | **PASS** (two minor source-side notes) |
| B. Ordinary mathematics, with my own code | **PASS** |
| C. Lean technical audit | **PASS** (stated trust limits) |
| D. Prior art | **PASS, bounded**; the Deza–Indik precedent must be cited |
| E. Significance | **QUALIFIED_PASS** |

**Recommendation.** The claim is eligible for root acceptance, subject to three things:
- root's own judgment on significance;
- a manuscript that cites Laurent–Poljak and Deza–Indik;
- root's extracted replay.

**Input binding.** All 137 input files hash identically before and after the review (`receipts/inputs-before.json`, `receipts/inputs-after.json`). The raw MathDB line hash c215c90f… matches `results.json`, and the source PDF hash is a4c72db9….

## A. Source fidelity: PASS

**The polytope.** I read formulas (2)–(4) and (6) in the PDF:
- P = {x ∈ R^m : (2)–(4), x ≥ 0}, with m = n(n−1) and arcs i ≠ j;
- in-degree and out-degree are 1 at every node;
- x(δ(S)) ≥ 1 for every S with 2 ≤ |S| ≤ n−2, where δ(S) = {(i,j) : i ∈ S, j ∉ S}.

`ASEP.arcPolytope` states exactly this on the arc space. `ASEP.polytope` is the zero-diagonal matrix form that the source itself uses in Section 3. My own `RV.P` uses a different encoding, and I proved it equal to `arcPolytope n` for every n.

**Neighbourhoods.**
- Definition 3 sets N(x) to be the set of all vertices adjacent to x.
- The proof of Lemma 7 spells adjacency out as sharing r(n)−1 linearly independent tight constraints, which is ordinary edge adjacency.
- Section 5.2 calls the resulting graph the "polyhedral graph". Its Definition 8 makes that the graph of vertices and edges of the polyhedron.

**Alternative readings.** None of them rescues the conjecture.
- *Pivot reading.* Pivoting(x, T) is explicitly a subset N′(x) ⊆ N(x). Every nondegenerate pivot moves along an edge, and every edge at x can be reached from some feasible basis of x. So even at a degenerate vertex the pivot neighbourhood equals the ordinary one and can never be larger.
- *Orbit-representative reading.* Lemma 7 makes N equivariant under relabelling, and the tours form a single orbit (Lemma 4). Working with representatives therefore changes nothing.

**The source's own data, reproduced with ordinary adjacency.** I recomputed it exactly (`outputs/rv-n4.json`, `rv-n5-table2.json`, `rv-n5-combinatorial.json`, `rv-small-claims.json`).
- *n = 4.* There are 12 vertices. Each tour is adjacent to every vertex but one, and the Example 1 vertex is adjacent to 5 of the 6 tours.
- *n = 5, orbits.* There are 384 vertices in 5 orbits of sizes 60, 120, 60, 120 and 24. The tight-set counts are 6, 4, 4, 4 and 10.
- *n = 5, neighbourhood sizes.* I get |N| = 28 for (a), 23 for (d) and 148 for the tours (e). These agree with Table 2.
- *n = 5, qualitative claims.* Every vertex has a neighbour in every other orbit, and only (d) and (e) have neighbours in their own orbit, exactly as Section 5.2 states.

**n range.** Conjecture 1 states no n. It follows the tests at n = 4, 5, 6 and is motivated by obtaining the V-description of the polytope in general. The Lean form quantifies over every n ≥ 4, which is faithful. Any reading whose n-range contains 8 is refuted. The MathDB raw statement matches.

**Objection A-1 (minor; inside the source).** Table 2 gives |N| = 20 for orbit (b) (entries 1/3 and 2/3) and |N| = 28 for orbit (c) (entries 1/2, with 4 tight sets).
- Exact ordinary adjacency gives 11 and 20, from two methods that agree: a rank test and a rank-free test of which vertices lie in the minimal face.
- A double count of the edges between tours and fractional vertices is consistent: 3000 = 24 × 125.
- The other three cells and all the qualitative statements match.

So this looks like a table error: the printed values look shifted by one row. It does not look like a broader notion of neighbourhood, and the source defines none. The manuscript should report it neutrally.

**Objection A-2 (chronology only).** Optimization Online shows the paper as "Published 2024/03/28, Updated 2025/06/15". The 2024 file (`main-1.pdf`) now returns 404. I therefore could not tell whether Conjecture 1 was already stated in 2024; MathDB gives the year as 2025.

## B. Ordinary mathematics: PASS

All of this used my own stdlib code and exact arithmetic; none of the author's scripts were reused.

**`scripts/rv_asep.py`** uses fraction-free integer elimination.
- **Vertex.** x* is feasible and has 19 support arcs. Its smallest positive entry is 1/4. Exactly the 8 claimed cuts are tight, and the smallest value of any non-tight cut is 5/4. The tight system has rank 56 = m, so x* is a vertex.
- **All 5040 tours** (cyclic orders 0, p1, …, p7). The common tight system has rank at most 54 for every tour, so no tour is adjacent. The rank histogram is {44:213, 45:590, 46:913, 47:958, 48:846, 49:626, 50:430, 51:232, 52:123, 53:82, 54:27}, identical to the author's.

**`scripts/rv_perturb.py`** is structurally different.
- **Method.** It computes an exact rational Gauss–Jordan nullspace, and the smallest nullity over all tours is 2. The rank modulo 1000003 equals the rational rank for every tour.
- **Witnesses.** For every tour T it builds an explicit direction v, not parallel to x* − T. It then checks exactly that z ± εv is feasible against all 310 constraints, where z = (x* + T)/2.
- **Result.** Non-faces are witnessed for 5040 of 5040 tours, in 79 s CPU.

**The perturbation argument** in the writeup, which is also `not_extreme_of_dir` in Lean, is correct.
- At z, every non-tight constraint has slack at least 1/8. This is because entries of x* are 0 or ≥ 1/4, cut values are 1 or ≥ 5/4, and T is 0/1 with integer cut crossings ≥ 1.
- Since Σ|v| ≤ 64, the perturbation v/512 changes any constraint value by at most 1/8.
- Tight constraints are preserved because v satisfies them.
- If the segment [x*, T] were extreme, v would have to be parallel to x* − T, which the 2×2 minor rules out.

**Controls and probe.**
- The n = 4 control (source Example 1) behaves exactly as the source says.
- The n = 7 probe is optional and not exhaustive (`outputs/rv-n7-probe.json`). Collapsing either tight 2-set of x* gives a feasible point that is not a vertex (rank 41 < 42). The 21 random fractional vertices I tested each have at least 4 adjacent tours.
- So minimality of n = 8 is open, and nothing in the claim depends on it.

## C. Lean technical audit: PASS

**Build.** I made a fresh, byte-identical copy of the 21 proof modules plus `PermOrder` in `lean-build/src` and built them one at a time in dependency order.
- Toolchain: Lean 4.34.1 (commit 5045d005) with `-j1 -DwarningAsError=true`, against the pinned prebuilt mathlib d13f23b7.
- Environment: `env -i`, with a `LEAN_PATH` holding only the pinned packages and the review build directory.
- Caps: each call ran in a systemd scope with MemoryMax=6G, under my own private-RSS watchdog.
- Result: every module returned 0. Peak private RSS was 4917 MiB (ASEPCover), and no build used more than 20.4 s of CPU (`outputs/lean-runs-summary.json`).

**leanchecker.**
- The non-fresh run passed on all 21 proof modules.
- The `--fresh` run passed on ASEPData, ASEPCheck and ASEPDefs.

**Full declaration audit** (`lean-review/RVAudit.lean` → `outputs/lean-decl-audit.jsonl`). The file records, for each declaration, its module, full type, kind, safety flag, body presence, axioms and attributes.
- There are 300 local constants: 187 theorems, 110 defs, and one structure with its constructor and recursor.
- Every def and theorem has `value?` = true.
- There are no axioms, no opaque declarations, and no `implemented_by` or `extern` attributes.
- `collectAxioms` returns a subset of {propext, Classical.choice, Quot.sound} for every constant.
- In this Lean version `collectAxioms` uses axiom data cached in the oleans. I therefore also walked the bodies of the whole transitive closure myself (12354 constants) without the cache. The walk reaches only those three axioms and finds no missing constants.
- The only flagged items are two compiler-generated partial auxiliaries, `ASEP.digs._unsafe_rec` and `ASEP.triples._unsafe_rec`. They appear in no endpoint closure, and the kernel would not let a safe declaration use them anyway.

**Endpoint closures** (`lean-review/RVClosure.lean`). I checked the six author endpoints and my two restatement theorems.
- None of the closures contains `sorryAx`, `ofReduceBool`, `ofReduceNat`, `trustCompiler`, or any unsafe or partial constant.
- Each closure reaches all 48 `chunkK_ok` theorems and `certs_cover`.
- A text scan of the sources is clean.

**Hunting for hidden weakening.** I found none.
- *Arc embedding.* `emb`/`res` is a bijection onto zero-diagonal matrices that preserves membership, segments and extreme sets.
- *Adjacency.* The endpoints refute it through the stronger statement ¬`IsExtreme`.
- *Vertices.* `IsVertex` is `Set.extremePoints`.
- *`IsExtreme`.* Mathlib's version here requires only the left endpoint to lie in the set; by symmetry of open segments this is the classical definition.
- *Tours.* `IsTour` is the tour matrix of an n-cycle with full support, which is exactly the set of directed Hamiltonian cycles.
- *Coverage.* The kernel `decide` proof `certs_cover` shows the certificates' cyclic orders are exactly `permutations' [1..7]`. `exists_cert` then turns the orbit of node 0 under any 8-cycle into such a cyclic order.
- *Checker soundness.* It relies on `XN_tight`, a kernel `decide` proof that every tight cut in range is one of the 8 listed cuts.

**My own restatement** (`lean-review/RVRestate.lean`), written from the source text:
- `RV.P` sums indicator weights over all arcs and writes the cut range as |S| + 2 ≤ n, avoiding natural subtraction.
- `RV.IsFace` is a textbook face: the intersection of P with the hyperplane of a valid inequality.
- `RV.Tour` is a cyclic listing f 0 → … → f (n−1) → f 0, built with `finRotate`.
- `RV.Conjecture1` quantifies over every n ≥ 4.

I proved the following. All of it builds strictly and depends only on the three standard axioms.
- `RV.P n = ASEP.arcPolytope n` for every n.
- Textbook faces are extreme subsets.
- Every `RV.Tour` is an `ASEP.IsArcTour`, and tours exist.
- `RV.conjecture1_false : ¬ RV.Conjecture1`.
- `RV.counterexample`.

**Negative controls.**
- `RVNegOk` compiles, as it should. The kernel shows `chk = false` for three digit mutations of a stored certificate and for a certificate paired with another tour's order. Dropping one tight cut breaks the coverage fact. As a positive control, the unmutated certificate gives `chk = true`.
- `RVNegFail` fails to compile, as it should, with "decide proved that the proposition … is false".

**Trust limits (C-1).** The pinned mathlib oleans are prebuilt and were not rebuilt. `--fresh` was not run on the endpoint modules: their closure includes all 48 kernel `decide` chunks plus mathlib analysis, which exceeds the 120 s CPU cap.

**Cosmetic (C-2).** There are 21 proof modules plus `PermOrder`, which is unused by the proof and whose `#eval` writes a file to the current directory.

## D. Prior art: PASS, bounded

I found no refutation, discussion or follow-up of Conjecture 1, and arXiv still shows only v1.

**The authors' later work.** I read the full text of four documents. None mentions Conjecture 1 or tour neighbourhoods.
- arXiv:2511.05045 (Sosso, Bernardelli and Gualandi).
- arXiv:2507.07003 (Villa, Vercesi, Barta and Mastrolilli).
- The 2026 Optimization Online paper "An Asymptotic Framework for the Integrality Gap of the TSP" (Barta, Mastrolilli, Vercesi and Villa).
- Vercesi's doctoral dissertation.

**Direct precedent: this must be cited.** Laurent and Poljak (1992) conjectured that every fractional vertex of the metric polytope is adjacent to an integral vertex (a cut). Deza and Indik refuted this "dominating set conjecture" with a vertex of met_9 whose neighbours are all fractional (arXiv:math/0512493, Optim. Lett. 2007; I read the arXiv body). The ASEP result is the same phenomenon in a different polytope: new as a statement, but not new in kind.

**Other literature.** I found no known subtour-relaxation vertex that is adjacent to no tour. The Padberg–Rao diameter results and Trubin's quasi-integrality concern edges between integral vertices, and they imply nothing either way here.

**Not read, recorded.**
- The Laurent–Poljak 1992 original, and the published version of Deza–Indik.
- Elliott-Magwood's thesis and the Boyd–Elliott-Magwood papers.
- Padberg–Rao 1974 and Trubin 1969, which are paywalled.
- Citation indices: Semantic Scholar and Crossref return 429 and were not retried; Google Scholar was not tried.
- The 2024 Optimization Online file, which returns 404.

## E. Significance: QUALIFIED_PASS

**For.**
- This is a first refutation of a conjecture stated verbatim in the source, exactly verified and kernel-checked. It is not a wording, domain or endpoint correction, and not a routine corollary.
- It defeats the source's stated motivation for the conjecture. By Lemmas 4 and 7, the orbit of x* is missing from every tour's neighbourhood, so "solely pivoting on an integer vertex" cannot yield the V-description of P_ASEP^8.

**Against.**
- The conjecture is a side remark drawn from preliminary tests in a computational OR paper. Those tests were exhaustive only for n = 4 and 5, and partial for n = 6.
- The failure appears at n = 8, and the author's heuristic walk found such vertices quickly.
- The vertex graph is connected regardless, so only the one-step strategy fails.
- The Laurent–Poljak → Deza–Indik precedent makes the outcome unsurprising in kind.

**Net.** It meets the campaign's floor, but its significance is modest. I would not oppose a HOLD on significance alone.

## Resource incidents in the author lane

The author lane logged two incidents in `logs/resource-incident-ghv.txt`:
- A GHV batch for MathDB 376197, unrelated to this claim, ran as four concurrent capped processes, which broke the 2-CPU cap.
- An early compile of ASEPCheck ran with no memory cap, reached 26.4 GB and was killed.

**No 368807 artifact depends on an uncapped run.**
- The uncapped compile was killed before it produced an olean, and the packet was then split into chunks.
- I rebuilt and rechecked every module from source under MemoryMax=6G plus the watchdog, with a peak of 4917 MiB. I never used the author's build directory.
- The GHV outputs are not used by this claim.

## My own compliance

- **Deviation.** I ran one read-only `git rev-parse HEAD` inside the pinned mathlib package directory to confirm the revision; it printed d13f23b7, matching the manifest.
- **Python without `-I`.** The n = 5 and n = 7 probe scripts ran without `-I` because they need user-site numpy and scipy. They read only files I generated, and scipy only proposes points, which are then certified exactly. All other Python ran with `-I -B`.
- **Caps.** Every process ran under the systemd scope plus the watchdog, with 2 CPUs, a CPU cap of 120 s, a wall cap of 140 s and MALLOC_ARENA_MAX=2, and only one heavy process ran at a time.
- **Downloads.** Each URL was fetched once into `downloads/`, with a receipt in `receipts/`; no denied route was hit or retried.
- **No leftovers.** No background jobs remain, and nothing was written outside this directory.

## Files

**Scripts** (`scripts/`):
- `hashbind.py`: input hash binding.
- `watch.py`, `cap.sh`: the RSS watchdog and the capped runner.
- `rv_asep.py`, `rv_perturb.py`: the exact n = 8 checks.
- `rv_n5_table2.py`, `rv_n5_combinatorial.py`, `rv_small_claims.py`, `rv_n7_probe.py`: the controls and the probe.
- `build.sh`, `check.sh`: the Lean builds and leanchecker runs.
- `summarise_lean.py`: collects the run receipts.
- `fetch.sh`: one-shot downloads with receipts.

**Lean** (`lean-review/`): `RVRestate.lean`, `RVAudit.lean`, `RVClosure.lean`, `RVNegOk.lean`, `RVNegFail.lean`. The build tree is in `lean-build/`, with every `.watch.json`, stdout and stderr under `lean-build/logs/`.

**Outputs** (`outputs/`): `rv-n8.json`, `rv-perturb-n8.json`, the n = 4/5/7 files, `lean-decl-audit.jsonl` and `lean-runs-summary.json`. The capped-run receipts for the Python scripts are in `logs/`.

**Receipts and downloads** (`receipts/`, `downloads/`): the arXiv abstract pages for 2506.10671 and math/0512493, the arXiv PDFs of math/0512493 and 2507.07003, the Optimization Online landing page and PDFs, and the Pavia dissertation.
