# Adversarial FINAL review — parent-repeated-integrals @ 7da5ba3717

Review lane: `pi-repeated-integrals-final-review`. Solo reviewer (pi), no children, no
external posts, no git operations, no edits outside this lane. Accepted tally unchanged
(18/30); candidate credit 0. I authored none of this candidate or its manuscript
(implementation lane is `pi-repeated-moment-openness-formal`, a different completed lane);
no conflict of interest.

Candidate frozen at commit 7da5ba3717 (unchanged under current b75381797c — verified via
`git diff 7da5ba3717 b75381797c -- <lane>`: empty). All 42 `final-review-hashes.json`
files copied byte-identically into this lane and re-hashed (`hash-verification.json`,
`all_match: true`). `candidate.json` blob hash 956f60b3… matches both the working tree
and the frozen commit. The retained early `provenance.json`/`PROOF.md`/`FORMAL-PROGRESS.md`
partial statuses were treated as historical; the current closed proof is
REPRESENTATION-PROOF.md + the 18 frozen Lean modules. The preliminary review and parent
correction addendum were read but **not** adopted: every claim below was re-derived.

**VERDICT: PASS on all five gates.** One prospective result: Burke–Haris–Madhavendra
all-order Conjecture 1.2 ((P_n) for every n ≥ 0, MathDB 371768, arXiv:2512.02151v1 p. 2).
No decisive objections. Detailed gates follow.

---

## Gate 1 SOURCE — PASS

- **Version history.** arXiv 2512.02151 submission history (fetched 2026-10-27): v1 only
  (Mon, 1 Dec 2025); no later revision. 2411.03145: v2 latest (30 Nov 2024). 2512.23949:
  v1 only. Fresh PDFs downloaded from `arxiv.org/pdf/<id>` are **byte-identical** to the
  frozen copies (914981e1…, 99f8bf6c…, 6b15667f…).
- **Page 2 read visually from the fresh PDF** (rendered at 130 dpi,
  `sources/fresh/page2-02-fresh.png`), verbatim: W_n = {b ∈ R^{n+1} : ∃ f ∈ C^n[0,1]
  with D^n f increasing (footnote: non-strict sense) and nonconstant, D^j f(0) = 0,
  D^j f(1) = b_j, j = 0..n}; "(P_n) is the statement that W_n is open in R^{n+1} and
  that for each b ∈ W_n we may choose the witnessing function f to be C^∞ and so that
  D^{n+1}f(x) > 0 for all x ∈ (0,1), D^{n+1}f(0) = D^{n+1}f(1) = 1 and
  D^j f(0) = D^j f(1) = 0 for j > n+1"; **Conjecture 1.2** "(P_n) is true for all
  nonnegative integers n"; **Theorem A (Thm 8.2)** (P_n) for n = 0,1,2,3 with explicit
  W_0 = {a>0}, W_1 = {0<a<b}, W_2 = {0<2a<b, b²<2ac},
  W_3 = {0<c<d, 2b²<3ac, 6ad+4b²+c² < 6ac+2bc+2bd}. This matches the frozen
  `conjecture-page2.png` and the candidate scope **including n = 0**.
- One-sided endpoint derivative convention confirmed (source §2, l. 144–147).
- **Proposition 4.4** verified in text (l. 658–666): the source itself uses the
  repeated-integral formulation W_n = {b : ∃ g ∈ F_0, g(0)=0, I^j g(1) = b_{n−j}}; the
  candidate's kernel identity is its Stieltjes form. The source contains no
  measure/moment-cone machinery.
- **MathDB 371768 live complete record** (fetched 2026-10-27,
  `sources/fresh/mathdb-371768-fresh.json`): status **open**; ALL arrays inspected —
  comments 0, solutions 0, model_attempts 0, human_solves 0, formulations 0, replies 0,
  attachments 0, collections 0; progress null; lean_formalization_count 0; edited_at
  null; statement identical to the frozen record (f23a140f…, hash-verified).
- **Sequel 2512.23949v1 Theorem 4.2 body read** (l. 276–292): begins "**Assume (Qn).**";
  (Q_n) is the renamed (P_n) (l. 273: "In [3] it was called (P_n), but we call it
  (Q_n) here"). Scope unchanged; the sequel remains conditional on the all-n statement
  and applies it only for n ≤ 3. No changed boundary conventions.

## Gate 2 MATH — PASS

I re-derived the complete final route (REPRESENTATION-PROOF.md + manuscript + actual
Lean sources, which I read in full) independently; no step was accepted on trust.

(a) **Atomless nonzero supported Stieltjes measure, including endpoint atoms.** For
b ∈ W_n, g = D^n f is continuous on [0,1] (one-sided convention) — the single place the
source's C^n hypothesis enters. `intervalExtension` clamps g constantly outside [0,1];
`intervalStieltjes_noAtoms` proves μ({x}) = 0 for **every** x (via continuity +
`leftLim_eq`), so there are no atoms at 0 or 1 either; mass = g(1) − g(0) > 0 by
monotone + nonconstant + g(0)=0 (`monotone_nonconstant_terminal_pos`); support ⊆ [0,1]
(`intervalStieltjes_compl`). An atom would put the moment vector on the cone boundary;
the candidate needs and uses only sufficiency of atomlessness.

(b) **Exact factorial/binomial kernel.** `source_jet_integral`: Taylor's integral
remainder (`taylor_integral_remainder`) with zero initial jets gives
b_j = ∫₀¹ (1−t)^{k}/k! · g(t) dt, k = n−j−1 (genuine within-derivative argument; no
extra derivative of g assumed). `intervalStieltjes_kernel` (genuine Fubini swap,
`intervalIntegral_integral_swap`, integrand bounded by cutKernel_norm_le) gives
∫₀¹ (1−x)^k g(x) dx = ∫ (1−t)^{k+1} dμ/(k+1). Combined with the j = n case
(b_n = g(1) = μ(ℝ)): b_j = (n−j)!⁻¹ ∫ (1−t)^{n−j} dμ for all j — matching the paper's
eq. (4) and the source's I^{n−j}-formulation.

(c) **Endpoint map.** `kernelMomentMatrix` is lower triangular (choose = 0 above
diagonal) with diagonal (−1)^r/r! (choose(r,r)=1); det = ∏_r (−1)^r/r! ≠ 0
(`kernelMomentMatrix_det_ne_zero`); composed with the output index reversal
(`Fin.revPerm`), `endpointMomentTransform_apply` gives exactly the paper's (5);
`finite_binomial_kernel` (binomial theorem + zero tails) yields
`endpointMomentTransform_density`/`_measure`. Parameter ordering checked: row index
j.rev = n − j.

(d) **Endpoint-one smooth density image is convex and open, for ALL n (incl. n = 0).**
Read `MomentOpen.lean` (426 lines) line by line. Fixed bump χ = ContDiffBump(1/2) with
rIn = 1/8, rOut = 1/4: 0 ≤ χ ≤ 1, χ = 1 near 1/2, supported in (1/4, 3/4), so χ = 0
near both endpoints. `gramMatrix n` (G_ij = ∫₀¹ t^{i+j} χ dt) is symmetric and
positive definite: xᵀGx = ∫ χ·(Σ x_i t^i)² > 0 because a nonzero polynomial has
finitely many roots (`Polynomial.finite_setOfPred_isRoot`) while ball(1/2, 1/4) is
infinite, and χ > 0 on that ball — real integrals, no abstraction shortcut; valid for
n = 0 (1×1 case, ∫χ > 0). Hence G invertible; the **explicit realized sup-norm ball**
radius r = ε/B with ε = m₀/(2(n+1)), B = 1 + Σ|G⁻¹_{ij}| realizes every y with
‖y − m(ρ₀)‖_∞ < r as m(ρ₀ + χ·Σ c_i t^i), c = G⁻¹(y − m(ρ₀)), since Σ|c_j| ≤ (n+1)ε =
m₀/2 and |Σ c_j t^j| ≤ Σ|c_j| on [0,1] keep the perturbed density ≥ m₀/2 > 0
(`goodDensity_perturb`) while the endpoint germs are preserved (χ = 0 near 0 and 1).
Convexity is direct (`smoothMomentSet_convex`). No residual premises.

(e) **Zero in closure, strict dual positivity, separation sign.**
`endpointBaseline δ = δ + (1−δ)(bump₀ + bump₁)` is a good density of mass ≤ 5δ with all
moments in [0, 5δ]; δ = min(ε/10, 1/2) puts 0 ∈ closure A (`zero_mem_closure`).
Separation is pinned Mathlib's `geometric_hahn_banach_open_point`
(Mathlib/Analysis/LocallyConvex/Separation.lean:125) — verified at its source. If
L(m(μ)) > L(z) on A: `zero_le_bound_of_smooth_functional` gives 0 ≤ L(m(μ));
`bounded_functional_nonpos` (via the explicit test bump `exists_positive_test_bump`,
whose integral positivity is *proved*, and the family 1 + cψ) gives L(p(t)) ≤ 0 on
[0,1]; L ≠ 0 (else (3) contradicts nonemptiness), so q = −coeffs ≥ 0, q ≠ 0 has finite
zero set, and `atomless_moment_strict_positive` gives ∫ q dμ > 0, i.e.
L(m(μ)) < 0 — contradiction. Sign conventions verified.

(f) **Primitive endpoint jets.** `repeatedPrimitive_terminal` gives exactly the
terminal jets D^j F(1) = T_n(m(ρ))_j; `repeatedPrimitive_initial` the zero initial
jets; D^{n+1}F = ρ > 0 on (0,1); D^{n+1}F(0)=D^{n+1}F(1)=1 and all higher endpoint
jets 0 from the germ ρ = 1 near both endpoints (`goodDensity_higher_endpoint`,
via `EventuallyEq.iteratedDeriv_eq`); strict monotonicity of D^n F by
`strictMonoOn_of_deriv_pos`. `goodWitness_mem_sourceW` closes the loop both ways;
`SourceAssembly` composes W_n = T_n(A_n) from the two explicit premises
`smoothMomentSet_convex`/`smoothMomentSet_isOpen`, both discharged from MomentOpen.

(g) **No reliance on the older argument.** The closed-cone/dense-A/int(cl A) = A route
of PROOF.md is NOT load-bearing anywhere in the formal chain; the parent addendum's
corrections (R1 justification, complete W_2 list, atomlessness-sufficiency) are
exposition-only and none is used. Degenerate cases: n = 0 traced through every module
(SourceW 0, j = n mass case, 1×1 Gram and transform, baseline, dual, primitives).
No generic abstract surrogate is used anywhere: every object is concrete.

## Gate 3 FORMAL — PASS

- All 42 frozen files copied into this lane; all sha256 values re-verified and the
  copies byte-checked (`hash-verification.json`).
- **Fresh isolated replay** with my own copy of `verification/verify_candidate.py`,
  explicit binary `/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean`
  and packages `.../2026-10-14/formal/.lake/packages`: **PASS — 129 declarations /
  18 modules**; compiler 4.34.1 verified; pins verified: mathlib d13f23b723b8a846827a245b89c10fc7d3f11612
  + all 8 dependencies at pinned revisions, all clean (`git status` empty). Receipt:
  `build/verified/audit.json`. Log: `replay-stdout.log`.
- `-DwarningAsError=true` (module logs all empty — warnings would have failed the
  build); forbidden-token scan (sorry/admit/axiom/unsafe/native_decide) = **0** in all
  18 sources; no new axioms: I read all **129/129** actual `#print axioms` reports from
  my own replay — only `propext`, `Classical.choice`, `Quot.sound`; all 129 `#check`
  types inventoried and inspected.
- **Closed endpoints read from my replay's Checks.log:**
  `RepeatedIntegrals.source_conjecture_371768 : RepeatedIntegrals.SourceConjecture371768`
  (no arguments, no residual premises); `RepeatedIntegrals.source_moment_image (n : ℕ) :
  SourceW n = ⇑(endpointMomentTransform n) '' smoothMomentSet n` (no premises).
  `source_measure_exists` takes **only** `hb : b ∈ SourceW n` — no hidden smoothness,
  moment, atomlessness, openness, or rank premises at source level. `SourceW`/`GoodWitness`
  match the literal statement: `ContDiffOn ℝ n f (Icc 0 1)`, `MonotoneOn` (non-strict) +
  nonconstant, initial zeros, terminal values b_j; witness: `ContDiff ℝ ∞`, 0 < D^{n+1}f
  on (0,1), D^{n+1}f(0)=D^{n+1}f(1)=1, all higher endpoint jets 0. `NullSingletonClass`
  is discharged by a real instance from continuity — no impossible typeclass. The only
  non-lane lemma used, `geometric_hahn_banach_open_point`, is verified in pinned Mathlib.
- Implementation provenance: `formal/MomentOpen.lean` equals the completed implementation
  lane's file byte-for-byte (interface hash 8127777a… = MomentDefs interface, per
  CURRENT-PROVENANCE.json and the 42-file verification); the implementer is a different
  lane and did not review. The parent's receipt hash 0d0a272f… matches
  `final-review-hashes.json` → `verification/full129-audit.json` (frozen) and my fresh
  replay produced the same declaration/axiom structure.

## Gate 4 NOVELTY / ELIGIBILITY — PASS (bounded screen)

Theorem **bodies** read, not abstracts:

- **di Dio arXiv:2411.03145v2, pp. 5–6**: Theorem 2.5 (= [dD19, Thm 17]) represents an
  *interior* moment functional by finitely many scaled Dirac-approximants; Corollary 2.7:
  if the Dirac-approximating family has L¹/C^∞/C_c^∞ densities, so does the representing
  measure. Section 3 (Thm 3.2, Ex 3.3/3.4) characterizes piecewise-continuous densities
  on [0,1]. **Published DOI 10.1007/s00013-025-02175-1, full HTML read**: Theorem 2.5
  (same), Corollary 2.6 (L¹ characterization; its proof already builds a C_c^∞ density
  ρ = Σ g_{ε_i,x_i}), **Corollary 3.1** (= arXiv Cor 2.7). **None of these mentions
  W_n, endpoint germs ρ = 1, positivity of a density on all of [0,1], or any next-
  derivative/endpoint-jet condition.** Applied naively they say nothing about (P_n).
- **Predecessor arXiv:1804.07058v2 (PAMS 147 (2019) 3021–3038), Theorem 17 body read**
  from fresh full HTML: T_A is a full-dimensional convex cone, int T_A = int S_A, and
  (under extra hypotheses) T_A = int S_A ∪ {0}. No W_n, no germs, no smooth witnesses.
- **Search:** targeted queries for any resolution of (P_n)/W_n openness; 2512.02151
  shows **0 citations**; the only known successor is the author's own conditional
  sequel. MathDB record open with zero activity (Gate 1). No direct or subsuming
  prior all-order endpoint theorem found.
- **My independent eligibility decision (not adopting the preliminary PASS):** the
  distance from known theorems to (P_n) is real — the atomless-Stieltjes bridge from
  the literal C^n hypothesis, the exact kernel, the endpoint-one germ density class
  with its convexity/openness, and the all-order jet assembly appear in no prior work
  read. This is a substantive explicit source-conjecture resolution assembled from
  standard (correctly combined) truncated-moment tools — not an uncounted immediate
  corollary, and not a posted or equivalent-known result. No global priority claim;
  limits: no MathSciNet/zbMATH access; 2026 preprint/seminar sweep bounded; empty
  records are not novelty proof.

## Gate 5 MANUSCRIPT — PASS

- `paper.pdf` sha256 40643de697d38d1673329bbf8f56c5e7ffbd97296b94990b4392aa93158f263f ✓
  and `main.tex` sha256 18e55578058c05f503b1b40875f4f7f91ea63e2b57e0434462324a305f1414ac ✓
  (both inside the 42-file verification). 3 pages, rendered at 120 dpi and **all read
  visually** (`sources/fresh/paper-{1,2,3}.png`).
- Every assertion compared to actual Lean scope: Theorem 1 ↔ `SourceConjecture371768`
  (incl. the "F^{(n+1)} identically one near both endpoints" strengthening ↔ GoodDensity
  germs); A_n (2) ↔ `smoothMomentSet`; Lemma 2 ↔ nonempty/convex/open + 0 ∈ closure
  (β_δ, mass ≤ 5δ); Gram matrix argument as in MomentOpen; Lemma 3 ↔
  `atomless_measure_mem_smoothMomentSet`; §3 kernel (4) and T_n (5) ↔
  SourceMeasure/KernelBridge/MomentTransform; F (6) ↔ `repeatedPrimitive`;
  W_n = T_n(A_n) ↔ `sourceW_eq_smoothMomentImage`. "including n = 0" stated and true.
- Attribution clean: conjecture credited to Burke–Haris–Madhavendra [1] with Theorem A
  (n ≤ 3) explicitly *not* claimed; sequel's conditional status stated; di Dio [3]
  credited (Theorem 2.5, Cor 2.7 arXiv = Cor 3.1 published, both cited) as "an earlier
  moment-theoretic framework, not new machinery here"; no absolute priority claim.
  Credit-0 / "final independent review and packet acceptance pending" language present
  as intended. Formal-status paragraph matches my fresh replay exactly (129/18, pinned
  Lean 4.34.1/mathlib d13f23b7, warnings-as-errors, three standard axioms). Layout
  clean; references correct (versions and DOI). No overclaim or conflation.

---

## Verdict

| Gate | Verdict |
|---|---|
| 1 SOURCE | **PASS** |
| 2 MATH | **PASS** |
| 3 FORMAL | **PASS** (fresh isolated 129/18 strict replay in this lane) |
| 4 NOVELTY/ELIGIBILITY | **PASS** (bounded; limits stated) |
| 5 MANUSCRIPT | **PASS** |

The candidate is a correct, formalized, manuscripted resolution of the full all-order
Burke–Haris–Madhavendra Conjecture 1.2. No decisive objections; no fixes required.
Minor notes (non-blocking, for the parent's packet): (i) `geometric_hahn_banach_open_point`
is Mathlib's — record it in the packet's dependency list; (ii) the fresh MathDB JSON
hash differs from frozen only by volatile fields (view_count/timestamps) — content
identical; (iii) eligibility framing should remain "resolution of an explicit open
conjecture using standard moment tools; no new machinery; no priority claim".
Per instructions: no candidate/shared/ledger edits, no acceptance count, no staging.
