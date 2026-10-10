> Archived exploratory draft. Some claims were corrected, rejected, or left unreviewed. Use [the final index](../README.md) and [screening decisions](../SCREENING.md) for accepted results.

# Independent novelty scout — 2026-10-08

All upstream assertions are assumed true. Revision: `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. This report validates downstream deductions, not upstream arguments. No claim below is established as new to the literature. The most promising contribution is the **quartic, unique-fiber, infinite-zero-set normal form** for reciprocal-sum complexity.

## Ranking

| Rank | Proposed downstream result | Proof status | Novelty assessment |
|---|---|---|---|
| 1 | Reciprocal-sum convergence is Σ₂⁰-complete in a fixed family of nonnegative quartics, each with infinitely many natural zeros and at most one witness per distinguished coordinate | Complete below | Not stated in the single-fold manuscript; promising project result, literature priority unproved |
| 2 | A fixed nonnegative quartic has a finite reciprocal sum over all its natural zeros which is transcendental and has Turing degree 0′ | Complete below | Classical noncomputable-real mechanism; new normal form relative to the accepted single-fold theorem |
| 3 | Explicit natural density `½ log²(1/t)` for a curved region of consecutive largest-prime-factor statistics, `½ ≤ t ≤ 1` | Complete below | Easy but nonrectangular consequence; old logarithmic-density analogues follow from older joint laws |
| 4 | Rational-phase sine sums, including cosine sums, have exact convergence region `a > max(1,b)` | Complete below | Not the explicit unshifted corollary; low novelty confidence because rational inhomogeneous approximation is classical |

## Exact source ledger and retrieval

All links below use the pinned revision; the actual `.tex` files, including the companion/consequence sections, were downloaded to `sources/cache/independent_scout/`.

* **S1:** [Single-fold Diophantine representations, build/main.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Single-fold-Diophantine-representations-September-24-2026/build/main.tex), Theorem **1.1**, label `thm:main`: every r.e. relation on natural tuples has an integer-polynomial representation with exactly one complete auxiliary tuple per member. Naturals include zero. Read also [build/consequences.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Single-fold-Diophantine-representations-September-24-2026/build/consequences.tex): its explicit consequence is at-most-one-solution solvability undecidability, not reciprocal summation.
* **S2:** [Joint Dickman law, introduction.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/build/sections/introduction.tex), Theorem **1.1**, `thm:main`: the pair `log P⁺(n)/log n`, `log P⁺(n+1)/log n` converges in ordinary empirical distribution to independent variables with CDF `F(x)=ρ(1/x)`. Read [distribution.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-joint-Dickman-law-for-consecutive-integers-September-24-2026/build/sections/distribution.tex), including its explicit ordering and upper-tail consequences.
* **S3:** [Irrationality exponent of π, main.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/build/main.tex), Theorem **1.1**, `thm:main`: `μ(π)=2`. Read [series.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-irrationality-exponent-of-pi-is-2-September-24-2026/build/sections/series.tex), particularly `series:generalized`, which **already proves** the full unshifted criterion.
* Duplicate check: [H10 over Q, October 6 consequence section](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Hilberts-tenth-problem-over-the-rational-numbers-October-6-2026/build/sections/07-consequences.tex), `thm:degree-normal-form`, already contains rational quartic and sum-of-quadratic-squares normal forms. Those are rejected as proposals.

The supplied `tree.json` has `truncated=true` and 58,727 entries, ending inside `lean/`; it does not list all manuscript paths. Retrieval therefore used the pinned root's `preprints` subtree and the relevant manuscript subtrees. Catalogue and overview were consulted to scout across the families, with close reading concentrated on S1–S3 and H10(Q).

## 1. Σ₂⁰-complete convergence with infinitely many unique-fiber zeros

**Statement.** There exist a fixed integer `m` and a fixed polynomial `Q(E,N,Z₁,…,Z_m)` of total degree at most four, presented as a sum of squares of integral polynomials of degree at most two, such that for every `e∈N`:

1. for each `n`, at most one `z∈N^m` solves `Q(e,n,z)=0`, and no solution has `n=0`;
2. there are infinitely many pairs `(n,z)` solving it;
3. the index set
   `C={e : Σ_{(n,z): Q(e,n,z)=0} 1/n < ∞}`
   is Σ₂⁰-complete under computable many-one reductions.

In particular neither convergence nor divergence is semidecidable on this fixed, entirely promised family. Summation is over **all zero tuples**, without existential projection or deduplication; uniqueness makes it equal to the sum over allowed `n`.

**Proof.** Let `W_e` be a standard uniformly c.e. family, and define the uniformly c.e. relation

`A_e = {2^k : k≥0} ∪ ⋃_{0≤j<|W_e|} [4^j, 2·4^j−1]`.

The interpretation is: enumerate block `j` once `j+1` distinct members have appeared in `W_e`. The relation `(e,n): n∈A_e` is c.e., even though its cardinality condition is not generally decidable. All `A_e` are infinite and exclude zero.

If `W_e` is finite, only finitely many blocks are added, and the powers of two contribute `Σ_k 2^{-k}=2`; hence `Σ_{n∈A_e}1/n` converges. If `W_e` is infinite, every block occurs. Blocks are pairwise disjoint and each has `4^j` terms, all at most `2·4^j`, so each contributes at least `1/2`. Hence the sum diverges. Overlaps with the powers of two cause no trouble: the disjoint blocks alone supply the divergent lower bound.

S1 gives a fixed polynomial `P(e,n,w)` whose entire natural witness tuple is unique exactly for this relation. Convert it to quartic degree while retaining uniqueness: write `P=P₊−P₋` with both parts having nonnegative integer coefficients. Evaluate each part by a fixed acyclic addition/multiplication circuit. Introduce a natural variable for every gate, enforce `u=c`, `u=v+w`, or `u=vw`, and equate the two output gates. For fixed inputs `(e,n,w)`, induction through the circuit gives one and only one natural assignment to its gate variables. Squaring and adding every gate residual and the output equality yields `Q`; each residual has degree at most two, and the complete zero tuple consists of `w` and every gate. This proves all structural assertions. Splitting signed coefficients is necessary: direct evaluation of a signed circuit could force a negative natural gate.

For the upper complexity bound, enumerate all zero tuples in expanding finite boxes. Their finite partial reciprocal sums `s(e,t)` are uniformly computable rationals, monotone in `t`, with supremum equal to the full sum. Thus convergence is precisely `∃B∈N ∀t [s(e,t)≤B]`, a Σ₂⁰ predicate. For hardness, `e∈C` iff `W_e` is finite. Here is a direct proof that FIN is Σ₂⁰-complete: given any predicate `∃b∀t R(e,b,t)` with computable `R`, at stage `s` let `b_s` be the least `b≤s` satisfying all tests `t≤s`, or `s+1` if none; enumerate the initial segment `{0,…,b_s}`. A true witness makes `b_s` eventually bounded, producing a finite set. Without a witness, every fixed candidate is eventually excluded, so `b_s→∞`, producing an infinite set. This construction is uniform in `e`, completing the reduction. ∎

**Effectivity boundary.** S1 supplies existence, not numerical coefficients or an algorithm choosing its arithmetic constants. After choosing one fixed `P`, its finite code can be hard-coded, and all specializations are computable. Accordingly the theorem is existential about a fixed family; this session does not produce a usable explicit universal quartic. Fixed dimension, fixed degree, and fixed number of summands are justified, but their numerical values are not.

## 2. A convergent quartic reciprocal sum of degree 0′

**Statement.** There exists a fixed quartic `R(N,Z)` of the same nonnegative sum-of-squares form, with at most one natural witness per `n`, no zero at `n=0`, and infinitely many zeros, for which

`θ = Σ_{(n,z):R(n,z)=0}1/n`

is finite, left-c.e., transcendental, and has Turing degree exactly `0′`.

**Proof.** Let `K` be an infinite c.e. halting set of degree `0′`, and apply S1 to
`A={4^{e+1}: e∈K}`. Apply exactly the uniqueness-preserving circuit conversion above. Then

`θ=Σ_{e∈K}4^{-e-1} ≤ 1/3`.

Enumerating zero tuples gives an increasing computable rational approximation, so `θ` is left-c.e. A `K` oracle computes the first `L` membership bits; the omitted tail is at most `4^{-L}/3`, so `θ≤_T K`.

Conversely recover membership inductively. Having subtracted all recovered earlier digits, set `w=4^{-e-1}`. If `e∉K`, the residual is at most `w/3`; if `e∈K`, it is at least `w`. Approximation with error below `w/12` distinguishes these cases by the threshold `2w/3`. Thus `K≤_T θ`. This separated-digit argument avoids binary carry ambiguity. Therefore `θ` is noncomputable. Every real algebraic number is computable, by isolating its root with rational intervals and effective bisection, so `θ` is transcendental. ∎

This also excludes a computable modulus of convergence for any computable monotone zero-tuple enumeration of this sum: such a modulus would compute `θ`. The elementary geometric tail in the **digit index** is not a modulus in zero-tuple enumeration order; discovering the corresponding witnesses requires halting information.

**Novelty caution.** Noncomputable sums and arithmetic encodings of halting information are classical. [Chaitin, *Incompleteness theorems for random reals* (1987)](https://doi.org/10.1016/0196-8858(87)90010-8) uses exponential Diophantine solution-count encodings. [Ord–Kieu (2003)](https://arxiv.org/abs/math/0301274) gives further Ω encodings involving exponential equations and polynomial value sets. The feature here is direct, multiplicity-free summation over zeros of one ordinary nonnegative quartic. No randomness claim is made for `θ`; degree `0′` does not imply Martin-Löf randomness.

## 3. Explicit curved-region density

**Statement.** For every fixed real `t∈[1/2,1]`,

`lim_{X→∞} X⁻¹ #{2≤n≤X : log P⁺(n) · log P⁺(n+1) > t(log n)²}`

`= ½[log(1/t)]²`.

**Proof.** By S2 the empirical pair `(U_n,V_n)` converges weakly to independent `(U,V)` with marginal CDF `F(x)=ρ(1/x)`. On `[1/2,1]` the Dickman differential equation gives `ρ(u)=1−log u` for `1≤u≤2`, hence `F(x)=1+log x` and density `f(x)=1/x`. The event `UV>t` forces `U>t` and `V>t`, so only this elementary part of the density is needed. The boundary `UV=t` has zero product measure, including `t=1`; continuity-set convergence gives the desired natural density. For `t≤1`, compute

`Pr(UV>t)=∫_t^1 (dx/x) ∫_{t/x}^1(dy/y)`

`=∫_t^1 log(x/t) dx/x = ½log²(1/t)`.

The finite-sample value `V_n` can slightly exceed one because its denominator is `log n`, but S2's weak limit is supported on `[0,1]²`; this does not invalidate the boundary argument. ∎

[Teräväinen, *On binary correlations of multiplicative functions*](https://arxiv.org/abs/1710.01195) establishes the older logarithmic joint law; [Tao–Teräväinen, almost-all-scales correlations](https://arxiv.org/abs/1809.02518) supplies earlier ordinary laws outside exceptional scales. The curved-event formula is an elementary integration once independence is available. Claim only a checked downstream corollary, not a new probabilistic principle or proven publication priority.

## 4. Rational phases, including cosine

**Statement.** For every rational `r` and real `a,b>0`,

`Σ_{n≥1} n^{-a}|sin(n+πr)|^{-b}`

converges iff `a>max(1,b)`. In particular this holds with `cos n` in place of `sin n` (`r=1/2`). No denominator vanishes, since `n/π+r` cannot be an integer.

**Proof.** Write `r=h/d`, `d≥1`, and `α=1/π`. S3 implies `μ(α)=2` by inverting rational approximants. Explicitly, a sufficiently good approximation `p/q≈α` has `p` comparable to `q`, and `q/p≈π` with error bounded by a constant times `|p/q−α|`; thus for every `ε>0`, `||kα||≥c_ε k^{-1−ε}` after absorbing finitely many exceptions. Since

`||dnα|| ≤ d||nα+r||`,

all shifted distances on `[N,2N)` are at least a constant times `N^{-1−ε}`. Differences of two circle points satisfy the same lower bound without the shift. Ordered distances on each half-circle are therefore at least constant multiples of `jN^{-1−ε}`. Since `|sin πx|≥2||x||`, the dyadic block sum is bounded by

`O(N^{b(1+ε)−a} Σ_{j≤N}j^{-b})`.

For `b<1`, `b=1`, and `b>1`, respectively, this is `O(N^{1+bε−a})`, `O(N^{1+ε−a}log(2N))`, and `O(N^{b+bε−a})`. Choose `ε` small to make the power negative when `a>max(1,b)` and sum the dyadic bounds.

If `a≤1`, comparison with `Σn^{-a}` proves divergence. For `1<a≤b`, let `p_k/q_k` be convergents to `α`. The matrix with columns `(q_k,p_k)` and `(q_{k−1},p_{k−1})` has determinant ±1, hence is invertible modulo `d`. Choose residues `A₀,B∈{0,…,d−1}` so that

`N=Aq_k+Bq_{k−1} ≡0 (mod d)`,
`M=Ap_k+Bp_{k−1} ≡h (mod d)`,

where `A=A₀+d`. Then `dq_k≤N≤3dq_k` and `|Nα−M|≤3d/q_k`, by the convergent error bounds. Put `n=N/d` and `m=(M−h)/d`. This yields `|nα−m−r|≤3/q_k=O(1/n)`. Applying the construction to `−r` gives infinitely many unbounded `n` with `||nα+r||=O(1/n)`. Their summands are bounded below by a positive constant times `n^{b−a}`, so they fail to tend to zero, including the boundary `a=b`. ∎

[Meiburg, *Bounds on Irrationality Measures and the Flint-Hills Series*](https://arxiv.org/abs/2208.13356) treats generalized unshifted sine-like sums. A rational-phase version may already be recorded in approximation literature; the bounded-residue convergent construction is classical. Priority remains open. **Arbitrary real phases are not covered:** homogeneous irrationality exponent alone does not control every inhomogeneous target.

## Validation and rejected alternatives

Run `python experiments/independent_scout.py`. Exact rational checks verified block mass ≥1/2, base-four tail gaps, and a small nonnegative circuit example. These check arithmetic mechanisms, not the existence of the S1 polynomial.

Sieve sanity checks for proposal 3:

| N | t=0.5 observed | t=0.6 observed | t=0.8 observed |
|---|---:|---:|---:|
| 10,000 | .305031 | .178918 | .041704 |
| 100,000 | .299563 | .173922 | .041100 |
| 1,000,000 | .293368 | .169095 | .039431 |
| predicted limit | .240227 | .130471 | .024897 |

Finite-size bias is substantial. The data move in the predicted direction but do not establish an error term or convergence rate; the proof uses the accepted S2 theorem.

Rejected alternatives:

* Unshifted generalized Flint–Hills threshold: exact duplicate of `series:generalized`.
* Rational solvability restricted to quartics or sums of quadratic squares: exact duplicate of H10(Q)'s `thm:degree-normal-form`.
* Weighted Seymour second-neighborhood transfer and LP dual distributions: literature search identifies the classical weighted equivalence and Farkas/duality arguments, including [Seacrest's arc-weighted paper](https://citeseerx.ist.psu.edu/document?doi=88d703c92f5cedec352284ddd01f89d9069e4c39&repid=rep1&type=pdf). Graph structural/algorithmic transfers of this kind have poor novelty yield here; no new graph theorem is asserted.
* Gaussian-prime component finiteness implies terminating connectivity BFS: accessible, but essentially a standard restatement of component finiteness, with no new uniform effective size bound.
* Dickman rectangular upper-tail densities and the 1/2 ordering density: explicitly included upstream.
* Unique-witness undecidability over `Z` or `Q`: S1 is about `N`; four-square and sign encodings can introduce multiplicities. No such extension is claimed.
* A harmonic sum weighted by total witness height rather than distinguished coordinate: witness sizes are uncontrolled; none of the reciprocal proofs establishes it.

## Explicit remaining gaps

1. Numerical universal quartics, dimensions, and coefficient bounds are absent; S1's fixed constants are existential. This limits executability, not the deductions.
2. Literature novelty is not settled. Searches targeted Diophantine reciprocal sums/noncomputable reals, Chaitin/Ord–Kieu encodings, generalized and shifted Flint–Hills sums, and consecutive Dickman laws. No matching complete quartic reciprocal-sum formulation was located, but search absence is not a priority proof.
3. Full manuscript duplicate checks were concentrated on the directly used families, not all 719 manuscripts. No claim of exhaustive catalogue exclusion is made.
4. There is no error term in proposal 3, no irrational-phase extension in proposal 4, and no computable witness-height bound in proposals 1–2.
