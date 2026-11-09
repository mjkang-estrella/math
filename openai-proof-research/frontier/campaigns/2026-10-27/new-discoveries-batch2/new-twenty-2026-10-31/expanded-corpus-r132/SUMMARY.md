# expanded-corpus-r132 — summary

**Bottom line: none of the 20 reserved IDs yields a candidate.** Four IDs are excluded: three are already resolved in the literature and one is contradicted by its own source. The other sixteen are parked.

The deepest work went into three IDs:

- **376143** (off-diagonal Hales–Jewett number HJ(k,2) = k): the main route, with five construction approaches.
- **338530** (star-Kayles periodicity): search extended well beyond the authors' range.
- **346730** (diameter-two conjecture): the exclusion was checked by independent recomputation.

There is no Lean packet, because no endpoint survived. No credit is claimed and none of this is self-accepted.

Lane: Claude Opus 5.5, 2026-11-03. Exactly 20 entries are in `results.json`, keyed by ID. Each entry has its raw line, chunk, line and statement hashes, arXiv abs/e-print receipts, the arXiv versions listed, review depth and outcome.

## Registries

- **OpenAI/math:** HEAD `4eaee87548250b2682affda7d05d947c05554bae`, unchanged.
- **Omega:** HEAD `2c2975d15e6ae9f3d323b75e96ebbcdcab498b6d` (2026-11-03T13:58:55Z). This is newer than the root's b576c901.
- **Omega tree screen:** one `git/trees` request (tree `6b835720…`, 56,479 entries). GitHub truncated the tree, so this was only a path screen on a truncated listing, not a proof reading. No Hales–Jewett, Kayles, ELW, OLA or eta paths appeared.
- **Receipts:** `sources/`.

## Dispositions

| ID | Outcome | What was done |
|---|---|---|
| 376143 HJ(k,2)=k | parked; sustained route | Full source read and five construction approaches (below). |
| 346730 diameter-two | **excluded: contradicted by the source's own data** | The source's Table 1 complement at n=7 has diameter 3; recomputed independently. |
| 344301 double descents | excluded: known | Hänni, arXiv:2011.14360, resolves Zhu's Conjecture 6.1. |
| 346797 Turán-good | excluded: known | Morrison–Nir–Norin–Rzążewski–Wesolek, arXiv:2208.08499. |
| 344598 power of one | excluded: known | Sah–Sawhney, arXiv:2105.13301. |
| 338530 star-Kayles | parked | Exact Grundy values for k ≤ 61 and leg length ≤ 3000: all have minimal period 12. |
| 364104 ELW | parked | Circulants up to n=30, perturbations of the equality cases, annealing: no violation. |
| 367510 OLA/SPR | parked | Exact expectations over all SPR moves for balanced trees up to 128 leaves: ratio to height ≤ 0.67. |
| 358046 Painlevé coefficients | parked | High routine risk (the source names its own proof method) and an expensive Lean endpoint. |
| 359283, 359284 grid covering | parked | Hard asymptotic integer lower bounds. |
| 345015, 354645, 354927, 343980 | parked | Hard asymptotic statements. |
| 351267, 368883, 343978 | parked | Famous open problems. |
| 347718, 340510 | parked | Analytic statements. |

## 376143 — the main route

**Source and scope.** The source is arXiv:2607.18111v1, Definition 11. Here HJ(k,2) is the *off-diagonal* number: the least n such that every red/blue colouring of [k]^n has a red full combinatorial line or a blue 2-line. A blue 2-line means two points w(a), w(a+1) on consecutive letters.

- The source proves k/2 ≤ HJ(k,2) ≤ k, and equality for prime k.
- Its SAT computations reach k ≤ 7.
- Question D notes that if HJ(k,2) ≤ G(k,2) held, Conjecture A would fail at k = 8.
- The MathDB paraphrase ("monochromatic combinatorial line") is defective. The diagonal reading is false at k=3, because HJ(3;2) = 4 and the source itself says so. The source's scope governs.

**Approaches tried.** All scripts are in `scripts/`; full logs and capped-run receipts are in `logs/`.

1. **Count-vector reduction** (`hj_counts.py`).
   - **The reduction.** Consider colourings that depend only on how many times each letter appears. A colouring of [k]^(k-1) of that kind is valid exactly when the blue count vectors B meet two conditions:
     - B meets every "star" {c + d·e_j : j}, where |c| = k-1-d and d ≥ 1.
     - B has at most one vector on each "transfer line" (vectors that agree except on two adjacent letters a, a+1).
   - **Results.**
     - k = 3, 4, 5, 6 solved exactly; k = 4 has exactly 8 such solutions.
     - k = 7 solved by local search.
     - **k = 8 is unresolved.** The instance has 3,432 vectors and was attacked with exact search, restart search, WalkSAT (with and without letter-reversal symmetry) and WalkSAT seeded from sum ≡ 0 mod 8. The best run left 94 clauses unsatisfied.
   - **Solver limits.** The lane's pure-Python CDCL solver (`cdcl.py`) could not even solve the easy k = 7 instance in 60 s. So nothing can be inferred about infeasibility at k = 8.
2. **Latin-fibre form** (`hj_latin.py`), where the last coordinate is a function of the counts of the others. These colourings provably do not exist for k = 4 and k = 6 (exhaustive search); they do exist for k = 3, 5, 7.
3. **Separable potentials** φ(N) = Σ_j g_j(N_j) mod k with bijective star differences (`hj_sep.py`): exhaustively impossible for k = 4 and k = 6.
4. **Dilation-invariant tilings** T ⊕ dA = Z_M for d = 1…k−1 (`hj_factor.py`): none for k = 4 with M ≤ 40.
5. **Position-dependent additive colourings** (`hj_possum.py`): none for k = 4 in the abelian groups of order ≤ 16 tested. One case, Z₂×Z₂×Z₄ with |T| = 4, hit its time limit, so that case is not exhaustive.

**Why linear constructions cannot work for composite k.** Through the van der Waerden sum map, a blue set T ⊆ Z must have gaps of at least k (no blue 2-line) and meet every k-term progression of step 1 (no red line). Together these force gaps of exactly k, so T = r + kZ. That set then misses progressions of step d whenever gcd(d, k) > 1. A modular weighted sum fails the same way.

**What would settle it.**
- A *proof* needs a uniform construction for composite k; none was found.
- A *refutation* at k = 8 needs unsatisfiability of a roughly 2.1-million-variable instance on [8]^7. That is infeasible in this lane and in the Lean kernel.
- **Suggestion for root.** A real SAT solver run on the 3,432-variable count-based instance (encoder `scripts/hj_counts.py`, k = 8) is cheap. A satisfying assignment would give the new value HJ(8,2) = 8 and answer Question D negatively. That is only one parameter value, though, not a resolution.

## 346730 — excluded

The hypothesis "η(G) + η(Ḡ) is maximal" is symmetric under taking complements. So if G is maximal, Ḡ is too, and the conjecture would force *both* to have diameter 2.

In the source's own Table 1 at n = 7 (unique maximal pair, arXiv:2006.01187v2), the drawn complement Ḡ has diameter 3:

- N(t6) = {t3, t4} and N(t7) = {t1, t2, t5} are disjoint, and t6t7 is not an edge of Ḡ, so d(t6, t7) = 3.
- Independent recomputation (`eta_table1_check.py`): η(G) = 91, η(Ḡ) = 86, diam G = 2, diam Ḡ = 3.
- The identity η(G) + η(Ḡ) = 2^n + n − 1 + X(G) checks out with X = 43, where X(G) counts the vertex sets that induce a graph which is connected and whose complement is also connected.

Refuting a printed statement that conflicts with the source's own data earns zero credit, so this is excluded.

For the record, hill-climbing (not exhaustive) at n = 8 and n = 9 finds maximisers where both G and Ḡ have diameter 2.

## 338530 — extended computation

The game positions are "spiders" S(j, l): a centre with j pendant edges and one leg of l edges, with Kayles = S(0, ·). Results:

- Two independent implementations (pure Python and vectorised) agree.
- Every j ≤ 60 is eventually periodic with **minimal period exactly 12** and pre-period ≤ 344, checked for leg length l ≤ 3000. That is far more than twice the pre-period, which the standard threshold argument needs.
- This covers k ≤ 61 under either reading of the source's indexing.
- The periodic tails do not differ from the Kayles tail by a constant XOR, so no structure uniform in k appeared.
- Note that "a period that is a multiple of 12" is automatic once a sequence is periodic; the real claim is periodicity for every k.

## Process notes

- **Resource caps.** Every numerical run used `scripts/limited.py`: 2 CPUs, CPU 120 s, wall 140 s, sampled RSS capped at 1.8 GiB, address space 4 GiB, MALLOC_ARENA_MAX=2. All 58 capped runs finished without hitting a cap. The largest sampled RSS peak was 524 MB (`ola-rand`), under the 1.8 GiB limit.
- **Concurrency deviation.** One deviation from "one process at a time": the k=8 WalkSAT run `hjw-8-s2` was still running when the 3.5-second star-Kayles run `sk-12-1000` started, so they overlapped for about 3.5 s. All later runs were strictly sequential.
- **Uncapped steps.** `extract.py`, `fetch.py` and `eprint.py` are I/O and network only and ran without the wrapper.
- **Python flags.** Scripts that need numpy (user site-packages) ran as `python3 -P -E`. They read no downloaded files. Everything that touches downloads ran with `-I`.
- **Downloads.** All are in `downloads/<id>/` and treated as untrusted; only .tex/.bbl/.bib files were extracted.
- **Prohibited steps.** No Lean, lake, SAT or ILP binaries, no git, no child agents, and nothing written outside this lane.
