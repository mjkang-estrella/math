# Review r1 — `proposals/independent_scout.md` §§1–2 (Diophantine reciprocal sums)

Reviewer scope: sections 1 and 2 only. Upstream theorems at revision `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are accepted as true, as the user instructed; only the new deductions were audited. First round; there are no earlier findings.

## Sources checked

* S1 `Single-fold-Diophantine-representations-September-24-2026/build/main.tex`, `thm:main` (lines 56–64 of the cached copy). The text is: for every `n≥1` and every r.e. `S⊆ℕⁿ` there are `m≥1` and `P∈ℤ[A,W]` with `#{w∈ℕ^m : P(a,w)=0} = 1` if `a∈S` and `0` otherwise. Line 43 defines `ℕ={0,1,2,…}`. Lines 116–120 state that the constants are existential: no coefficients are displayed and no procedure for choosing them is given. The proposal's summary of S1 and its effectivity boundary is accurate.
* S1 `build/consequences.tex`: the only consequence is `cor:unique-h10`, undecidability under the at-most-one promise. It has no reciprocal sums, degree-four normal form, or Turing-degree-of-real statement. The proposal's claim that the result is "not stated in the single-fold manuscript" checks out.
* H10(ℚ) Oct-6 `07-consequences.tex`, lines 55–95: the same gate-variable circuit with unique extension, credited to Davis 1973, Thm 7.5, over ℚ. So the degree-reduction step is classical (Skolem/Davis) and already used upstream. Only its pairing with S1 over ℕ is new here.

## Theorem 1 (Σ₂⁰-complete convergence, fixed quartic family): **ACCEPT with minor corrections**

I checked each step independently.

1. **S1 application.** `S={(e,n): n∈A_e}` is r.e. Membership `n∈A_e` holds iff `n` is a power of 2, or `∃j,s` with `4^j ≤ n ≤ 2·4^j−1` and `|W_{e,s}| ≥ j+1`. Apply S1 with arity 2. `A_e` is a **set**, so an `n` reached both as a power of two and through a block still has exactly one witness. The overlap remark is therefore correct and complete.
2. **Zeros / n=0 / infinitude.** `0∉A_e`, so S1 gives zero witnesses at `n=0`, which makes `1/n` well defined. Powers of 2 give infinitely many zeros for every `e`. ✔
3. **Convergence dichotomy.** For finite `W_e` there are finitely many blocks, so the sum is at most a finite sum plus 2 (powers of two, duplicates counted once). For infinite `W_e` every block is present. Block `j` is `[4^j, 2·4^j−1]` and `2·4^j−1 < 4^{j+1}`, so the blocks are disjoint. Each block contributes `> 4^j/(2·4^j) = 1/2`, so the sum diverges. ✔
4. **Uniqueness-preserving quartic conversion.** Split `P=P₊−P₋` with both parts having coefficients in ℕ. Gates are `u=c` (with `c∈ℕ`), `u=v+w`, `u=vw`, and the inputs `E,N,W` are leaves. Over ℕ, nonnegative coefficients force every gate value to be a natural number, determined uniquely by induction. The signed split is genuinely needed: a signed circuit can force a negative intermediate value, and then no natural assignment exists. The output equation `u₊=u₋` has degree 1, and every other residual has degree ≤2. `Q=Σ residual²` is integral, has degree ≤4 and is ≥0 on ℝ. Its ℕ-zeros are exactly `(w,gates)` with `P(e,n,w)=0` and the gates evaluated correctly. Hence there is at most one `z` per `(e,n)`. If `P₋=0`, use a constant-0 gate. ✔
5. **Upper bound.** `Q=0` is decidable on natural tuples and every zero has `n≥1`. So the box partial sums `s(e,t)` are uniformly computable rationals, nondecreasing in `t`, with supremum equal to the full sum (positive terms, and every zero eventually lies in a box). Convergence holds iff `∃B∀t s(e,t)≤B`, which is Σ₂⁰. ✔
6. **Hardness.** `e∈C ⇔ W_e finite`. The proposal's direct FIN proof is correct. If witnesses exist, `b_s ≤ b_min` for all `s ≥ b_min`, so the set is a finite union of finite segments. If none exist, each `b≤M` fails at some finite `t`, so `b_s→∞`. The uniform index needs s‑m‑n; this is implicit in the proposal and should be stated. The family is indexed by the `W`-index itself, so the reduction does not depend on the unknown `P` at all, which strengthens the effectivity point. ✔
7. **Corollary.** Σ₂-complete sets are neither Σ₁ nor Π₁. So neither convergence nor divergence is semidecidable. ✔
8. **Quantifiers.** "There exist `m`, `Q`, such that for every `e`" is the right order: one polynomial with `E` as a variable, existential coefficients. ✔

**Required corrections (wording only):**
* (1a) Cite the gate trick as classical (Skolem; Davis 1973 Thm 7.5), noting that H10(ℚ) `thm:degree-normal-form` already uses it with unique extensions. Present only the ℕ signed-split pairing with S1 as the project step.
* (1b) Mention s‑m‑n explicitly for the computable map `e ↦ index of ⋃_s{0,…,b_s}`.
* (1c) Novelty framing. Σ₂-completeness of `Σ_{n∈W}1/n < ∞` over c.e. sets is folklore. The deduplicated version over Diophantine value sets follows classically from DPRM. The only new content is that the summation runs over **all complete zero tuples** with no multiplicity. That follows from S1 in a few lines, so call it a "routine but apparently unrecorded corollary of S1", not a substantive new theorem. The current "promising project result, literature priority unproved" is acceptable, but "routine" should be added.

## Theorem 2 (a fixed quartic with a finite reciprocal sum of degree 0′): **ACCEPT with minor corrections**

1. `A={4^{e+1}: e∈K}` is r.e. and infinite and excludes 0. S1 is applied with arity 1, followed by the same conversion. This gives one witness per member and infinitely many zeros, so `θ=Σ_{e∈K}4^{-e-1} ≤ Σ_{e≥0}4^{-e-1} = 1/3`. ✔
2. **Left-c.e.:** monotone enumeration of zero tuples. ✔ **θ ≤_T K:** the tail beyond `L` is `≤ Σ_{e≥L}4^{-e-1} = 4^{-L}/3`. ✔
3. **K ≤_T θ:** let `w=4^{-e-1}`. If `e∉K` the residual is `≤ Σ_{d>e}4^{-d-1} = w/3`; if `e∈K` it is `≥ w`. With error `< w/12`, the observed value is `≤ 5w/12` in the first case and `≥ 11w/12` in the second, so the threshold `2w/3` separates them. ✔ (Simpler still: the base‑4 expansion of `θ` is exactly `χ_K`, with digits in {0,1}, so no expansion ending in repeated 3s can arise.)
4. **Transcendence:** algebraic reals are computable and `θ` is not. ✔ **Modulus remark:** a computable modulus for a computable monotone enumeration would compute `θ`. ✔
5. **Multiplicity:** the sum runs over all zero tuples, and S1 plus the gate determinacy give exactly one tuple per `4^{e+1}`. ✔

**Required corrections:**
* (2a) Fix the convention for the Turing degree of a real: Dedekind cut, or equivalently a binary/base‑4 expansion. Note that `θ` is irrational, being noncomputable, so all the conventions agree. Approximations with a known error bound then give the expansion.
* (2b) Novelty. The real `Σ_{e∈K}4^{-e-1}` is a classical Specker-type left‑c.e. noncomputable real (Specker 1949) and should be cited as the closest prior object. Chaitin 1987 and Ord–Kieu are correctly cited for the Diophantine encodings. State plainly that the only new feature is the multiplicity-free summation over the zero set of one ordinary nonnegative quartic, which follows immediately from S1. Ranking it "substantive" would overclaim; "normal-form corollary" is accurate. The no-randomness caveat is correct and should stay.
* (2c) Optional: note that Theorem 2 is the single-index analogue of Theorem 1's construction, so they can share one conversion lemma.

## Failure boundaries confirmed

* Over ℤ or ℚ the zero-count uniqueness fails (sign and four-square multiplicities). The proposal correctly restricts to ℕ. Gate variables must also range over ℕ; `Q`'s zeros over ℤ are not controlled.
* Effectivity: everything is existential in `P`. No explicit `m`, degree bound for `P`, or coefficients are given; the bound for `Q` is just ≤4. The reductions themselves are explicit.
* No witness-height bound or convergence rate is given. For Theorem 2, none can be computable.

## Overall verdict

**§1: accept with corrections (1a–1c). §2: accept with corrections (2a–2c).** Both proofs are complete and correct given S1, and I found no mathematical gap. The changes are attribution and novelty calibration: describe both results as short corollaries of S1 combined with classical tools (Skolem/Davis circuits, FIN completeness, Specker reals), not as substantive new theorems.
