# Lane 1 — new-twenty-2026-10-31 (resumes `claude-mathdb-primary-qualified-breadth-r628`)

Investigator: Claude Opus 5.5 (research sub-agent). Dates: 2026-10-31/11-01 UTC. No git operations, posts, browser work or delegation.
**Outcome: no viable full-scope candidate. 0 results proposed for credit.** Machine-readable per-ID dispositions are in `results.json` (50/50 reserved IDs).

## Inputs read

- Scoped `AGENTS.md`, `ledger.json`, `reservation.json`; parent `new-discoveries-batch2/AGENTS.md`; root intake `lanes/root-mathdb-breadth-intake-r729` (listing only).
- User steering (2026-10-31): credit requires a complete kernel-checked Lean formalization of the exact statement, so I scored formalization feasibility during selection.
- Previous lane r628, read-only. It had bound the 50 literal records and run exploratory Rippon (7.54) numerics: exact up to degree 600 and n ≤ 60, float up to degree 4000 and n ≤ 400. It recorded no dispositions or candidates. I reference its immutable files by hash instead of copying them:
  - `literal-records.json` sha256 `4eba068b…80ca5`, the source of the record identities and statement hashes in `results.json`.
  - `runs/rippon-float-D4000-N400.txt` sha256 `8bdfa098…a71f`.
  - `runs/rippon-win-D600-N60.txt` sha256 `f366faae…571f`.

## Primary sources (URL, access date, hash)

| Source | Used for | Access | sha256 |
|---|---|---|---|
| Hayman–Lingham, *Research Problems in Function Theory*, arXiv:1809.07200v2 (21 Sep 2018), problem and **Update** text | 30 Hayman IDs | cached by lane r576 on 2026-10-31T15:32:45Z (`lanes/sol-mathdb-primary-qualified-breadth-r576/1809.07200.txt`); abs page re-fetched 2026-11-01T03:24:12Z | txt `451cd756…a50d26`; abs `f01b33be…`
| Egres Open pages (8 problems) | 388036–388113 | live `oldlemon.cs.elte.hu`/`lemon.cs.elte.hu` timed out (curl 000) on 2026-11-01; **Wayback snapshots** from 2020-02 to 2024-12 in `sources/egres/` | `sources/egres/SHA256SUMS`
| Cooper, *Combinatorial Problems I Like* | 388119–388180 | fetched 2026-11-01T03:25:25Z | `ba547f05…`
| arXiv:2608.04540 (Guo–Xiao, 5 Aug 2026) | 387880 | 2026-11-01T03:24:03Z | `d13c52d1…`
| arXiv:1911.12255 (Cheriha–Gati–Kostov, 2019) | 387469 | 2026-11-01T03:24:10Z | `acbf436c…`
| erdosproblems.com/987, /519 | 387873, 387858 | 2026-11-01T03:24:05Z and 03:24:07Z | `bee2f033…`, `debb48c9…`

Full hashes are in `sources/*/SHA256SUMS` and `sources/prior/fetch-log.txt`.

## Disposition overview (all 50 inspected against a primary body; none metadata-only)

- **Publicly resolved or answered (15):**
  - From the book's own updates: 387479 (Drasin), 387486 (Kotman), 387528 (Kjellberg refuted 1/4), 387535 (sin z²), 387607 (Dahlberg), 387675 (fragment of 5.14; ≡5.13, solved), 387726 (Stephenson), 387741 (de Branges), 387754 (Hummel), 387774 (de Branges sharp bounds), 387898 (Fuchs).
  - Beyond the 2018 book: 387469 (refuted, arXiv:1911.12255), 387649 (yes: Kashin/Konyagin), 387873 (= Erdős #987, o(l) achieved), 387880 (yes: arXiv:2608.04540, Aug 2026).
- **Open-ended or non-exact (10):** 387693, 387734, 387744, 387771, 387787, 387820, 387943, 388146, 388171 (exact supremum R), 388180.
- **Open and hard, no tractable full route (22):** 387586, 387641, 387731, 387776, 387781, 387858, 387920, 388057, 388059, 388072, 388087, 388097, 388113, 388119, 388126, 388134, 388158, 388164, 388166, 388168, 388172, 388175. Most are named conjectures with decades of literature: Thomassen, Itai–Zehavi, independent trees, Aharoni–Berger, 1/3–2/3, (3/2)ⁿ, Erdős–Turán, no-three-in-line, Rado, among others.
- **Investigated in depth (3):** 388092, 387906, 388036. Details below.

Statement-fidelity notes:
- 387873 is phrased with |z_k|=1; this matches Erdős #987 via z_k = e(x_k).
- 387858's record says Atkinson's constant is 1/3; erdosproblems.com/519 gives 1/6 (the book text says 1/3).
- 387675's MathDB statement omits the actual question (normality).

## Candidate selection

From the exact, still-open statements I chose the three where both a full-scope answer and a Lean certificate looked conceivable:
1. **388092 (Correa–Goemans):** if false, a finite counterexample is decidable in Lean by exhaustive case analysis.
2. **388036 (k = l = 2 capacitated arborescences):** if false, a finite counterexample works the same way.
3. **387906 (Rippon):** concrete coefficient statement, with prior-lane numerics to build on.

### 1. MathDB 388092 — proportional factors of bipartite graphs

Exact statement (Egres; Feige–Singh, ESA 2008, Conjecture 1.4): for a bipartite G and positive reals c₁..c_k summing to 1, E can be partitioned into E₁..E_k with ⌊c_i d(v)⌋ ≤ d_{E_i}(v) ≤ ⌈c_i d(v)⌉ for all v and i.

Known results:
- ±2 relaxation (Correa–Goemans); ±1 for one-sided bounds (Feige–Singh).
- c_i = 1/k (de Werra); k = 2 (orientation with degree bounds); G regular.
- A web search on 2026-11-01 found no resolution after 2008.

Proof routes attempted (all failed; recorded so they are not repeated):
- **Binary splitting tree with k = 2 steps.** This works when the intervals nest; I checked it for c = (1/2, 1/4, 1/4). In general the induced interval for a group can contain no integer whose hull contains the proportional value, so the recursion breaks.
- **Total unimodularity.** Prefix-chain and laminar-per-side vertex constraints are TU. But the per-edge row Σ_i x_{e,i} = 1 makes the system the planar 3-index transportation polytope, which is not TU, so integrality cannot come from TU alone.
- **Universal circle labelling.** Assign each edge θ_e ∈ ℝ/ℤ so that the labels at v form a coset of (1/d(v))ℤ. Arcs of length c_i would then give the result for all c at once, by the balanced-word property. Refuted computationally: it fails for 204 of 2,576 random small graphs, e.g. K_{2,3} minus an edge (`scripts/circlelabel.js`). Only this strengthening is dead; the conjecture itself is not affected.
- **König colouring plus Tijdeman chairman sequence.** This would work if every vertex saw the colour prefix {1..d(v)}. That is impossible: two degree-1 neighbours of one vertex would both need colour 1.

Numerical diagnostics only, not proof. No counterexample in any of:
- Random DFS search (`scripts/propfactor.js`, seeds 21–24): 3,294,823 instances decided by DFS. These cover 6×6 simple (N ≤ 40), 8×8 simple (N ≤ 60), 6×6 with multiplicity ≤3 and 10×10 with multiplicity ≤2, k ∈ {3,4,5}. The remaining 35,539 hit the DFS budget and were re-decided exactly by HiGHS MILP (`scripts/propfactor_milp.py`): all 35,539 feasible and combinatorially re-verified (`runs/propfactor-milp-s*.txt`).
- Targeted tight instances (`scripts/propfactor_tight_milp.py`): small-denominator c and degrees mixing multiples of N, decided by MILP. 52,779 multigraph and 59,985 simple instances; 7,236 generated instances were skipped (empty or >90 edges). All were feasible, and each returned partition was re-verified.
- Exhaustive small sizes (`scripts/propfactor_exhaustive.js`): every graph of the given sizes (isolated vertices allowed) against every distinct floor/ceil pattern of c on a grid G that is a multiple of 10·lcm(1..Dmax). 611,294,019 instances in total, none unsolvable, no timeouts:
  - 3×3, multiplicity ≤2, k=3: 613 patterns, 12,065,066 instances.
  - 3×3, multiplicity ≤2, k=4: 5,639 patterns, 110,986,798 instances.
  - 4×4 simple, k=3: 127 patterns, 8,322,945 instances.
  - 4×4 simple, k=4: 491 patterns, 32,177,685 instances.
  - 4×5 simple, k=3: 427 patterns, 447,741,525 instances.

Remaining gap: a proof would need a genuinely new rounding argument for the planar 3-index structure. No route survived. A counterexample, if one exists, is beyond the sizes searched.

### 2. MathDB 387906 — Rippon (Hayman Problem 7.54)

Statement: with φ_t(z) = e^{tz} − 1 and a_n(t) = φ_t^n(−1) = Σ_k c_{n,k} t^k, is |c_{n,k}| ≤ 1 for all n, k? Update 7.54 (2018): no progress. Bounded search on 2026-11-01 found no later resolution. (The book prints t/2! where t²/2! is meant.)

Proved here (elementary; used only as structure):
- **(L1) Combinatorial formula.** k!·c_{n,k} is an integer, equal to Σ (−1)^{#leaves} over labelled forests on [k] whose leaves all sit at depth n−1. Equivalently, c_{n,k} = Σ_{1≤m₁≤…≤m_n, Σm_i=k} ((−1)^{m_n}/m_n!) ∏_{i<n} S(m_{i+1}, m_i), with S the Stirling numbers of the second kind. Proof: the exponential formula applied to a_{n+1} = exp(t·a_n) − 1, where multiplying by t in the EGF adds a root.
- **(L2) Stabilization.** a_n = O(tⁿ), so a_{n+1} = t·a_n + O(t^{2n+2}). Hence c_{n+1,n+1+j} = c_{n,n+j} for j ≤ n, and s_j := c_{n,n+j} (any n ≥ j) is well defined. Exact values: s = (−1, 1/2, 1/3, 1/24, 7/60, …).
- **(L3) Dynamical meaning (proof sketch, standard).** φ_t has no critical points and its only asymptotic value is −1. By Fatou, −1 lies in the immediate basin of the attracting fixed point 0 for 0 < |t| < 1. So S(t) := Σ s_j t^j = lim t^{−n} a_n(t) = K_t(−1), the Koenigs linearizer at the singular value. This is a Yoccoz-type function and is holomorphic in the unit disc. The inverse ψ_t is univalent on D(0, |K_t(−1)|) and omits −1, so Koebe's 1/4 theorem gives |S| ≤ 4 and hence |s_j| ≤ 4.

Why this does not close the problem: S(0) = −1 and s₁ = 1/2. So sup|S| > 1 and Σ|s_j|² ≥ 5/4, and no sup-norm or H² argument can give the sharp constant 1. The higher windows k ≥ 2n behave like a Schröder expansion Σ_m β_m(t)(tⁿS)^m, whose coefficients β_m have poles at roots of unity. Bounding them uniformly by 1 needs parabolic and Siegel asymptotics as t approaches the unit circle, which would be a long analytic programme. A Lean formalization of Koenigs/Fatou/Koebe machinery is far outside what Mathlib currently supports.

Diagnostics (prior lane, by hash above): over n ≤ 400 and degree ≤ 4000, the maximum non-leading |c| is 0.5944 at (n, k) = (6, 13), and window maxima scale like 1/j. A counterexample now looks implausible, and a proof looks deep. Parked.

### 3. MathDB 388036 — capacitated packing of k-arborescences

Statement as on Egres. The undirected version follows from matroid union; Egres says even k = l = 2 is open.

Reduction for k = l = 2: c(a) ∈ {0,1,2}, and WLOG each c=2 arc goes to both sides. The question becomes whether, when c is rooted 4-arc-connected, the c=1 arcs can be 2-split so that both sides are rooted 2-arc-connected (Edmonds).

Diagnostics only (`scripts/karb.js`), no counterexample:
- n = 4 exhaustive: 810 rooted-4-connected configurations.
- n = 5 exhaustive: 3¹⁶ = 43,046,721 configurations, 5,185,608 of them rooted-4-connected.
- n = 6 random: 3M samples, 812,787 rooted-4-connected.

Simple digraphs only (no parallel arcs). No proof route; parked.

## Adversarial self-checks

- **Run truncation.** An early run piped through `tail -4` would have hidden non-final lines. It was stopped and preserved as `runs/propfactor-js.attempt1-truncated-by-tail.txt`, and all counts above come from fully logged reruns. A stray shell from that run was also killed.
- **Silent skips.** The MILP search skipped instances with more than 90 edges or no edges. These are counted separately (`runs/propfactor-tight-milp-skipcount.txt`), not reported as decided.
- **Feasibility verification.** Every MILP "feasible" answer was checked combinatorially from the rounded solution. Infeasibility claims would need an independent certificate; none arose.
- **Grid adequacy.** Each exhaustive run uses a grid that is a multiple of 10·lcm(1..Dmax). Every open Farey cell of order Dmax therefore contains grid points, but sum-to-1 realizability near cell boundaries is argued, not proved.
- **Novelty evidence.** A fresh open label was never used as novelty evidence. Three records the 2018 book lists as open (387649, 387873, 387880) turned out to be resolved elsewhere.
- **Lean feasibility.** I found no Lean toolchain or C compiler on PATH in this environment, and attempted no formal work. Nothing here is a Lean endpoint.

## Access and dependency gaps (actionable)

1. Live Egres Open was unreachable on 2026-11-01, and the Wayback snapshots date from 2020–2024. Re-check the live pages for 388036–388113 before any future investment.
2. The Lütolf–Margot catalogue of minimally nonideal matrices was not accessed. It is needed to test Király's conjecture (388087) on non-cyclic cores; Pap already covers cyclic cores, and I checked J_t by hand.
3. Primary bodies of Kashin (1987), Konyagin (1994), Kotman, Fuchs and Stephenson were not read. Those dispositions rest on the book updates and on secondary or abstract-level sources.
4. 388126 (tetrahedra) and 388171 (sum-free reciprocals): a current literature check is limited to search snippets.

## Run ledger (all outputs in `runs/`, generators in `scripts/`)

| Run | Result |
|---|---|
| `propfactor-js-s21..s24.txt` + `propfactor-milp-s21..s24.txt` | 3,294,823 DFS-decided + 35,539 MILP-decided; 0 infeasible |
| `propfactor-tight-milp-{multi-s2,simple-s3}.txt` + `…-skipcount.txt` | 112,764 MILP-decided, 7,236 skipped; 0 infeasible |
| `exh-*.txt` (5 runs) | 611,294,019 graph×pattern instances; 0 infeasible, 0 timeouts |
| `karb-n5-exhaustive.txt`, `karb-n6-random.txt` | 388036 k=l=2: 0 counterexamples (5,185,608 and 812,787 rooted-4 instances) |
| `rippon-lemmas-check.txt` | L1 (closed formula), L2 (stabilization) and integrality verified exactly for n ≤ 7, k ≤ 22 |
| `propfactor-js.attempt1-truncated-by-tail.txt`, `propfactor2.txt` (empty, killed) | discarded attempts, preserved for audit |
| `circlelabel-s1.txt` | universal labelling fails on 204/2,576 small graphs |
