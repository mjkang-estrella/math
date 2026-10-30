# Final independent adversarial review — Lachaume quartic candidate (commit bd81899bc6)

Reviewer: pi (final review subagent, independent; no children; no git operations; no shared-index/candidate edits; wrote only this lane). Date 2026-10-26.

Scope: all five gates — source fidelity, mathematics, formal replay, bounded serious novelty, manuscript — for the candidate at `candidates/lachaume-quartic`, bytes bound by `final-review-hashes.json`. I did **not** rubber-stamp the preliminary PASS: every load-bearing claim below was re-derived or re-inspected by me from primary material.

**Gate summary: Source PASS. Mathematics PASS. Formal PASS. Novelty PASS (bounded). Manuscript PASS. No decisive blocking objections. Overall: PASS** (credit 0; one prospective Conjecture-1 outcome; no acceptance counted by this review).

---

## 0. Byte binding

My copy `replay/candidate/` hashes match `final-review-hashes.json` exactly (not `frozen-parent-hashes.json`):
`Quartic.lean 02f94881…`, `Diagonal.lean 3fc1a7d5…`, `Symmetric.lean d02feca6…`, `main.tex 87492ff4…`, `paper.pdf 368bf051…`, `build/verified/audit.json` = `verification/parent-audit.json` = 954775bb…, `verification/parent-checks.log` c0233ba2…. Recorded in `commands/candidate-copy-hashes.txt`.

## 1. Source fidelity — PASS

- **Primary paper**: I downloaded arXiv:1712.10327v1 fresh; SHA-256 `7b27f885…` matches the parent and preliminary freezes byte-for-byte. Submission history: v1 only. I rendered **p.3 and p.5 to PNG and read them myself** (`sources/myp3-03.png`, `sources/myp5-05.png`).
  - p.3: definitions f_a = a₀+a₁σ₁+…+a_pσ_p, f̄_a(X)=Σ a_k C(n,k)X^k, sets 𝒦, 𝒳, Ξ; **Conjecture 1** literally: f_a is 1/p-concave on Γ_n ⟺ 1/p-concave on Δ ⟺ f̄_a is 1/p-concave on ℝ*₊, for a⃗ ∈ (ℝ₊)^{p+1}. The candidate's reading (n=p=4, strictly positive coefficients a=(1,2,1,2,1), diagonal fourth-root concavity vs global failure at strictly positive inputs) refutes the literal ⟸ direction. Note Γ_n vs (ℝ₊*)ⁿ does not matter here: the witness points lie in the positive orthant, which is contained in Γ_n under every reading.
  - p.5: **Conjecture 3** literally: P ∈ ℝ₊[X], deg P = n, "P real-rooted ⟸ PP″+(1/n−1)P′² ≤ 0 **on ℝ**". The formal endpoint proves the inequality on **all** real arguments — no positive-half-axis weakening. Def 2.1 (P1)(P2)(P3) and Prop 2.2/Thm 2.4 confirmed as the preliminary described.
- **MathDB 338076**: fresh pull `sources/fresh-338076.json` is **byte-identical** (`5d578ab7…`) to the parent snapshot: status open, `solutions/comments/model_attempts/human_solves/replies` all empty, `progress: null`. Statement matches Conjecture 1. 338077–79 are Conjectures 2/4/5, distinct.
- **MathOverflow 248816**: fresh official-API pulls (`fresh-mo-248816-question.json`, `fresh-mo-248816-answers.json`; content-identical to parent snapshots, hashes differ only from JSON serialization): question by **LacXav** (Lachaume), answers **248836 Zaimi** (P=x⁴−1 with PP″+(1/4−1)P′²=−12x²≤0, imaginary roots; also x⁵−x) and **248822 Petrov** (root family i,−i,1^m,0^m). The nonnegative-coefficient addendum has no answer.
- **Translation-invariance correction independently verified (decisive check)**: I computed (x+2)⁴−1 = x⁴+8x³+24x²+32x+15, all coefficients strictly positive, 4RR″−3(R′)² = −48(x+2)² ≤ 0 on ℝ, and nonreal roots −2±i (resultant against x²+4x+5 is 0). The preliminary review's claim that the condition is *not* translation invariant is **false**, exactly as the parent addendum says; hence **Conjecture 3 is already implied by the known 2016 example plus translation and gets no credit**. I also verified the polarization ∏(xᵢ+2)−1 is covered by Andrica–Rădulescu Thm 4.17 (see below), so the shifted example cannot produce the candidate's midpoint failure.
- **Andrica–Rădulescu 2019 (Springer chapter)**: parent PDF hash `eb6e5cde…` matches `current-provenance.json`. I read the actual body myself: Section 5 "Convexity of Symmetric Functions" — **Thm 5.3 (Lachaume quadratic), 5.4 (adjacent two-term), 5.10 (powers generalizing 5.4)**; the remaining 5.x are products/powers/ratios of individual σ_k (Marcus–Lopes-based). **Theorem 4.17** proves concavity of (u₁…u_n − v^n)^{1/n} for concave uᵢ and convex v — this covers the shifted-Zaimi polarization, not the candidate's five-term inhomogeneous sum. No diagonal-concavity criterion for general sums, no counterexample, no five-term quartic. The stale "paywall-only" claim from the preliminary is superseded; my inspection confirms the addendum's reading.
- **2018 arXiv:1712.04528v2 (JMP 59, 072501)**: hash `99373959…` matches. **Theorem 2.7(d)** read in the actual text: real-rooted f̄_a ⟹ (a₀,…,a_p) ∈ K_n^p — a *sufficient* criterion, distinct from Conjecture 1; not refuted by the candidate (whose diagonal P is not real-rooted). The author's thesis conclusion (pp 180–181) restates Conjectures 1/3 as open; its printed implication chain is not used as a premise here (verified by grep over the preliminary's thesis text: no contre-exemple).
- **Carptopus**: fresh GitHub README and tex are **byte-identical** to the parent freeze (`101538e3…`, `50a0b634…`); line 209: "These implications do not address Lachaume's Conjectures 1 or 3." It proves Conjectures 4/5 and credits Thm 2.7(d). Zenodo DOI check: **10.5281/zenodo.22299983 is the correct record DOI** (v0.1-beta, 4 Sep 2026; concept record 22299982). The manuscript's citation is right; it explicitly excludes 1/3 and proves the known neighbor 4/5 — not conflated.

## 2. Mathematics — PASS (independent rederivation, third distinct code path)

My own script `replay/final-math-verify.py` (sympy Poly/expand exact arithmetic — distinct from the parent's pure-fractions lists and the preliminary's script), output `commands/final-math-verify.json`:

1. Diagonal: f_(1,2,1,2,1)(t,t,t,t) = t⁴+8t³+6t²+8t+1 exactly.
2. 4PP″−3(P′)² = −144(t²−1)² exactly; source form PP″+(1/4−1)P′² = −36(t²−1)² ≤ 0 on **all** ℝ.
3. h″ formula: 16·P^{7/4}·(P^{1/4})″ = 4PP″−3P′² exactly ⇒ P^{1/4} concave on all of x>0.
4. P = (x²+(4−2√3)x+1)(x²+(4+2√3)x+1); z=√3−2+i√(4√3−6) is an exact root (real and imaginary parts of the quadratic at z vanish; √3>3/2 ⇒ imag>0); numeric roots −7.3277, −0.1365, −0.2679±0.9634i.
5. Slice: g(t)=f(2,t,t,t)=5+12t+15t²+4t³; f(A)=2819/500, f(C)=3177/500, f(B)=7151/1000 exact at t=1/20,1/10,3/20.
6. Rational witness: (15409/10000)⁴<2819/500; 3177/500<(15877/10000)⁴; (16352/10000)⁴<7151/1000; 15877/10000 < (15409/10000+16352/10000)/2, gap exactly 7/20000; plus a 60-digit mpmath confirmation of the strict midpoint violation. All inputs and all five coefficients strictly positive — no domain or normalization loophole.
7. Slice-curvature consistency: 4gg″−3g′² = 168−240t−612t²−240t³−48t⁴ (intuition only, unused).
8. Positivity-set check: P's real roots are −2±√3±√(6+4√3) ≈ −7.3277, −0.1365; P(−100)=92059201>0, P(−1)=−8, P(0)=1. The preliminary's "P>0 exactly above its largest real root" is **false** (P>0 on the union of both exterior intervals); the addendum's correction is right. **Neither the Lean nor the paper uses any such statement** (checked both), so this is a historical note only.

## 3. Formal — PASS (fresh isolated strict replay on my copy)

- Ran the root `verify_candidate.py` (new-discoveries root, root `pins.json`) against **my copy only**, with the pinned binary `/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean` and packages `…/2026-10-14/formal/.lake/packages`. Compiler version and every dependency revision verified against pins. Output: `commands/replay-stdout.log`; artifacts in `replay/candidate/build/verified/` (my copy; the candidate directory was never touched).
- **PASS: 61/61 declarations compiled with `-DwarningAsError=true`; `#check`/`#print axioms` on all 61; only `propext`, `Classical.choice`, `Quot.sound`**. My `audit.json` is identical to the parent's (same module hashes, same inventory, same main theorems).
- I personally read the 61 types/axiom reports (`Checks.log`), including the endpoints: `source_diagonal_concavity_counterexample` is a closed 5-fold conjunction — all coefficients strictly positive, f>0 on the positive orthant, **ContDiffOn ℝ 2 (fun v => f v^(1/4)) positiveOrthant** (actual C² fourth root), **ConcaveOn ℝ (Ioi 0) diagonal root**, **¬ConcaveOn ℝ positiveOrthant root** — with **no residual hypotheses**. `strict_midpoint_violation`, `diagonal_concave`, `elementary_eq_mathlib` (literal subset-sum ↔ Mathlib `MvPolynomial.esymm` bridge), `source_nonreal_root_counterexample` all as claimed. No `sorry`/`axiom`/`native_decide` tokens (script-enforced), no new axioms, no holes.
- The formal ancillary Conjecture-3 endpoint (`source_nonreal_root_counterexample`) is correctly labeled uncredited.

## 4. Novelty — PASS (serious bounded check, Conjecture-1 focused)

- **Citation graph**: Semantic Scholar API and OpenAlex API each show **exactly 2 citing works** of 1712.10327 — the author's own JMP 2018 paper (read: sufficient criteria only, incl. Thm 2.7(d)) and Andrica–Rădulescu 2019 (full relevant body read by me, §5 + Thm 4.17: no resolution of Conjecture 1). Zenodo/Carptopus explicitly excludes 1/3. MathDB 338076 open with all arrays empty.
- **Subsuming-result search**: targeted queries for Lorentzian-polynomial/Gårding-cone/symmetric-quartic concavity classifications (Błasiak–Huh etc.), 1/p-concavity counterexamples, σ_k-Yamabe concavity results — all are *sufficient* concavity criteria (σ_k^{1/k}, real-rooted-coefficient families, Hessian operators) or unrelated; none subsumes the converse for inhomogeneous five-term sums, and none contains a diagonal-concavity counterexample. The candidate's diagonal P is not real-rooted, so it lies outside every known sufficient class.
- **Nearest-prior checks**: MO 248816 (Conj. 3 question, answered 2016); the translation-invariance fact means even the ℝ₊[X] Conjecture-3 variant is known — correctly **uncounted**. Conjecture 1 itself: no prior refutation found in this bounded screen (citing graph, full bodies of both citers, Carptopus, MathDB, web searches for the explicit quartic/mechanism).
- **Access limits (candid)**: typeset JMP 2018 body not separately read (arXiv v2 only, cannot be claimed as published body); no MathSciNet/zbMATH/Google-Scholar sweep; INSPIRE JS-rendered (search-snippet level); possible non-indexed 2026 preprints only partially covered. Bounded screen, not a priority guarantee — consistent with the manuscript's own disclaimer.

## 5. Manuscript — PASS

- `main.tex` `87492ff4…` and `paper.pdf` `368bf051…` match `final-review-hashes.json`. PDF is 2 pages; I rendered and **visually inspected both pages** (`sources/mypage-1.png`, `mypage-2.png`).
- All mathematics on the page matches my independent recomputation: P′, P″, identity (1), h″ formula, g(t) (2), the three f-values, the three rational bounds, the chain with gap 7/20000. Theorem 1 is exactly the rescoped claim (1: P^{1/4} concave on (0,∞); 2: f^{1/4} positive C² on Γ₄, not concave). No claim about P's positivity set appears anywhere.
- Scope/attribution: abstract and §4 attribute the real-rootedness converse failure to Zaimi's x⁴−1 + translation as **prior work, not a new contribution**; cite Thm 2.7(d) as the distinct sufficient criterion; cite Carptopus for Conjectures 4/5 with the explicit 1/3 exclusion (Zenodo DOI verified correct); compare Andrica §5/Thm 4.17; assert no priority and no complete census. Consistent with `candidate.json` (credit 0, one Conjecture-1 basis, 61 declarations).

## 6. Gate decisions

| Gate | Decision |
|---|---|
| Source fidelity | **PASS** |
| Mathematics | **PASS** |
| Formal (fresh strict replay, my copy) | **PASS** |
| Bounded serious novelty (Conjecture-1 focus) | **PASS** |
| Manuscript | **PASS** |

**Overall: PASS.** No decisive objections. Notes (non-blocking): (a) Conjecture-3 credit stays 0 — translation invariance of the normalized Laguerre condition is real and I verified it myself; (b) the preliminary's positivity-set refinement is historically false but unused anywhere; (c) novelty is bounded-screen, not a priority guarantee. Packet/extracted final replay remains the parent's responsibility.

## 7. Artifacts in this lane

- `review.md` (this file), `provenance.json`.
- `replay/candidate/` — my byte-bound copy; `replay/candidate/build/verified/` — my own strict replay artifacts (audit.json, Checks.log, logs).
- `replay/final-math-verify.py`, `commands/final-math-verify.json` — independent math rederivation.
- `commands/replay-stdout.log`, `commands/replay-stderr.log`, `commands/candidate-copy-hashes.txt`.
- `sources/` — fresh primary pulls: `fresh-1712.10327v1.pdf` (+ rendered `myp3-03.png`, `myp5-05.png`, page texts), `fresh-338076.json`, `fresh-mo-248816-*.json`, `fresh-walsh-main.tex`, `fresh-walsh-readme.md`, manuscript page renders `mypage-1/2.png`.
