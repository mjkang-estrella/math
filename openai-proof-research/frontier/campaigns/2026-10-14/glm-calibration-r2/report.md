# GLM calibration r2 — repaired exact finite-algebra reproduction of the R019 matrix certificate

**Campaign:** 2026-10-14 (calibration repair round 2). **Task:** repair the two
required defects found by the independent review of the original GLM
calibration (`../glm-calibration-review/review.md`), rerun the full battery
under corrected code, and hand the repairs to the parent for independent
verification. This is still the **old accepted result R019**
(`frontier/findings/R019-entangled-complete-crouzeix-equality.md`) and earns
**no new-result credit**.

**Status: complete, exit code 0.** All 24 base-case certificates pass in exact
arithmetic (the original 21 plus four new r2 certificates, with
`Tensor_convention` rewritten); all four mutation tests satisfy the
dependency-derived expectations, with every expected failure an ordinary
comparison mismatch and none an execution exception. The original
`glm-calibration` and `glm-calibration-review` directories were not modified;
only this `glm-calibration-r2` directory was written.

## Artifacts

| File | Content |
|---|---|
| `check.py` | Repaired self-contained exact certificate battery + mutation tests; writes `results.json`. Repairs D1, D2 and safeguards S1, S2 are marked in place. |
| `results.json` | Machine-readable: repair record, sha256 provenance of all inputs, per-check status/detail/**structured data**/duration, mutation tables with per-certificate **dependency reasons**, explicit limitations. |
| `run.stdout.txt` | Full stdout of the recorded final run. |
| `report.md` | This report. |

## Repairs made (and where)

**D1 — tensor-order negative control (`build_PN_fiberfirst`,
`cert_Tensor_convention`).** The original used stride 2 (`2*j + i`) for a
six-dimensional base, producing a malformed matrix (20 entries differ from the
true fiber-first assembly; its last four rows/columns are unused). Repaired:

* `build_PN_fiberfirst` now assembles the true fiber-first
  `sum_k C_k (x) N^k` with stride 6 (index `6*j + i`).
* `cert_Tensor_convention` now verifies, exactly: (a) agreement with an
  independent `sympy.kronecker_product` assembly; (b) the flip identity
  `F = J P[N] J*` with `J[6j+i, 2i+j] = 1`; (c) permuted attainment
  `F(Jx) = 2(Jy)`; (d) the intended negative control — a **nonzero exact
  residual** `F x != 2 y` when the unpermuted base-first coordinate vectors
  are used (measured residual norm² `2099/512 − 129·sqrt(14)/256`, matching
  the review's `targeted-results.json`); (e) `F != P[N]`.
* Both conventions describe the same operator under the correct basis
  permutation. Neither is intrinsically wrong; only their inconsistent mix
  is. The report language is corrected accordingly.

**D2 — rank computations under mutations (`words_upto`, `cert_Cyclic_rank`).**
The original `words_upto(L)` built and cached the baseline `N` internally, so
mutated rank claims were never recomputed (a zero matrix reported cyclic ranks
`1,2,3,5,6,6` and `dim6 = 36`). Repaired:

* `words_upto(N, L)` is parameterized by the actual matrix argument; the
  cache is removed entirely.
* `cyclic_profile(N)` returns cyclicity (rank sequence and minimal full-rank
  length) and the unital \*-algebra word-space dimension as **separate
  structured fields**; the aggregate certificate requires both, and the
  claimed vector identities are checked against the actual `N`.
* `Control_zero_matrix`: the zero matrix now yields cyclic ranks all 1 and
  unital-algebra dimension 1, and the aggregate certificate rejects it.
* `Control_reducible`: a reducible nonzero matrix (`(0,1)=1`, `(2,3)=2`) with
  the exactly-verified commuting projection `diag(1,1,1,1,0,0)` yields cyclic
  ranks `{1,2,2,2,2,2}` (a priori ≤ 2 via the exactly verified invariant
  `span{e1, e2}`) and unital-algebra dimension 9 (a priori < 36 via the
  commutant bound). Baseline reuse is now immediately visible.
* `Irreducibility_rationalized` (new): with
  `D = diag(1,1,1,sqrt(14),sqrt(14),sqrt(7))`, both `D⁻¹ND` and `D⁻¹N*D` are
  rational; exact word-space dimensions through length 6 are
  `1, 3, 7, 15, 26, 34, 36`, and an explicit 36-word rref basis has
  flattened determinant `2733816767052433962421431 / 576460752303423488 ≠ 0`
  (the review's `audit.py` method, reproduced on the actual argument).
  This independently certifies the baseline span-36 / irreducibility claim
  without relying on the repaired rank helper.

**S1 — `psd_hermitian` guard.** The helper now verifies Hermiticity exactly
(`G == G*`) before the principal-minor test and raises on non-Hermitian
input. All current callers form `alpha·I − M*M` and are unaffected.

**S2 — exceptions are not mathematical mismatches.** Each check records
`failed_by` (`comparison_mismatch` vs `exception`). A mutant is marked
inconsistent if any expected-fail certificate fails by exception. (This fired
correctly during development: an early import error made
`Tensor_convention` fail by exception and was flagged as an
exception-failure, not silently accepted.)

## Exact commands run

```sh
# environment reused from the original round; no new dependency install
# (python3 -m venv /tmp/sympy-venv && /tmp/sympy-venv/bin/pip install sympy==1.14.0)

cd openai-proof-research/frontier/campaigns/2026-10-14/glm-calibration-r2
/tmp/sympy-venv/bin/python check.py            # writes results.json here

# recorded final run, stdout preserved:
/tmp/sympy-venv/bin/python check.py > run.stdout.txt 2>&1   # exit code 0
```

Final summary line:
`ALL BASE CHECKS PASS; ALL MUTATION EXPECTATIONS CONFIRMED (repaired tensor
control, parameterized word generation, controls and safeguards in place)`.
Environment: Python 3.14.7, SymPy 1.14.0, Linux; wall ≈ 25 s.

## Method (unchanged in the exact-arithmetic core)

Everything is derived from the definitions displayed in the R019 finding —
N, P(z), C, a, ℓ, x, y, B, h, g — never from cached numeric outputs. All
pass/fail decisions are exact: SymPy rationals and square roots; polynomial
reductions modulo `c²+s²−1` (support pencil) and `zw−1` (boundary identity)
via Gröbner bases; sign decisions on field elements of Q(√2,√7,√14) by
rational-interval bounds from integer `isqrt`; integer-square comparisons for
eigenvalue ordering. **No floating-point pass criterion anywhere.** The
original 21 certificates are byte-for-byte the same computations as before,
except for the repaired pieces above.

## Base-case results (24/24 PASS)

* The original 21 certificates all pass exactly as before: N structure (36
  entries), P coefficients C₀…C₃ with round trip, Re N blocks, `CC* = I −
  aa*`, `‖a‖² = 57/64`, singular values of C `1, 1, √7/8`, the
  θ-independent support-pencil spectrum `(t²−1)²(t²−7/64)` verified
  symbolically, `P[N]x = 2y` with `‖x‖ = ‖y‖ = 1`, ℓ properties
  (`‖ℓ‖=1, Nℓ=0, N*ℓ = (√7/2)e₃ − (3√2/4)e₅`), flat Schmidt coefficients of
  x and y, the (1,3,4,3,1) grading with raise-by-two, the displayed block B,
  `B*B` spectrum (`4, (569±33√113)/512` below `337/128` via
  `33²·113 < 779²`), the full direct 12×12 charpoly
  `t⁷(t−4)(t−337/128)²(t²−569t/256+49/64)`, `N³N*³ = (7/4)e₁e₁*`, the
  boundary identity `P(z)P(z)* = I` mod `zw−1`, and 36/36 exact sampled
  scalar-channel instances of `‖(v*Pu)(N)‖² ≤ 849/256`.
* Repaired `Tensor_convention`: (a)–(e) above all hold; the unpermuted
  residual norm² is exactly `2099/512 − 129·sqrt(14)/256`, identical to the
  review's independent value.
* Repaired `Cyclic_rank`: ranks `1,2,3,5,6,6` (minimal full length 4) and
  unital \*-algebra dimension 36, now computed from the actual argument and
  reported as separate fields.
* New `Irreducibility_rationalized`: rationalization, dimension sequence and
  the nonzero 36-word basis determinant above.
* New controls: zero matrix → dims 1/1 with aggregate rejection; reducible
  matrix → cyclic ranks `{1,2,2,2,2,2}`, algebra dimension 9, within the
  a priori bounds.

## Mutation tests (all four consistent, no exception failures)

Expected sets were re-derived per certificate with recorded dependency
reasons (in `results.json` under `dependency_reasons`), not copied from prior
output. Unpredicted certificates (`Spot_check_scalar_channel`,
`Irreducibility_rationalized` under N-mutants) are reported honestly.

| Mutant | Certificates that must fail — all did, by mismatch | Certificates that must survive — all did |
|---|---|---|
| `mut_N_a` (N₁₂ := 6/5 + 1/20) | N_structure, ReN_blocks, CCstar, SV_C, Pencil_theta, ell_props, PNx_2y, B_block, BBstar, Outer_blocks, Charpoly, Cyclic_rank, Tensor_convention | P_coefficients, Norm_a, Schmidt, Grading, N3Nst3, Boundary_PP, PN_construction, both controls |
| `mut_N_b` (N₅₆ := √2 + 1/10) | N_structure, ReN_blocks, CCstar, SV_C, Pencil_theta, PNx_2y, B_block, BBstar, Outer_blocks, Charpoly, N3Nst3, Cyclic_rank, Tensor_convention | P_coefficients, Norm_a, ell_props, Schmidt, Grading, Boundary_PP, PN_construction, both controls |
| `mut_P_a` (C₂[1,1] := 3/4 + 1/10) | P_coefficients, PNx_2y, B_block, BBstar, Outer_blocks, Charpoly, Boundary_PP, Tensor_convention | all N-side certificates incl. Pencil_theta, N3Nst3, Cyclic_rank, Irreducibility_rationalized, Grading, both controls |
| `mut_P_b` (C₁[2,1] := √7/4 + 1/10) | same set as mut_P_a | same, incl. Grading (support pattern unchanged) |

Honest per-mutant observations outside the predicted sets:

* The rank machinery now genuinely recomputes under mutants: under `mut_N_a`
  the cyclic rank sequence of the mutated N is still `1,2,3,5,6,6` with
  algebra dimension 36 (reported, not predicted); the aggregate
  `Cyclic_rank` fails through the broken identity `N*e1`, exactly as the
  dependency reason states.
* Under `mut_N_a` the mutant N remains irreducible: the rationalized
  certificate passes with dimensions `1,3,7,15,27,35,36` and a nonzero
  determinant. Unpredicted a priori; recorded only.
* Under `mut_N_b` the rationalization itself fails
  (`D⁻¹ND` is no longer rational, so `rationalized = false` with an irrational
  determinant recorded) — the certificate is honestly reported FAIL for that
  input; nothing is claimed about the mutant's irreducibility from it. The
  radical-field path in `Cyclic_rank` still measures dimension 36 there.
* The sampled scalar-channel bound happens to survive all four mutants
  (it is an inequality with slack, so survival is unremarkable).

## What was NOT verified (analytic or out of scope)

Recorded in `results.json` under `not_verified_here_analytic_claims`:

* The maximum-principle step ‖P(z)‖ ≤ 1 on the disk from the boundary
  identity (only the algebraic boundary identity was verified).
* **The universal quantifier** in ‖(v*Pu)(N)‖ ≤ √849/16 for *all* unit u, v.
  **Universal scalar compression is not proved by the 36 exact samples**;
  they are sampled instances only. The universal argument rests on the
  analytic source reasoning (flat Schmidt coefficients giving product
  overlap ≤ 1/2, the exact complementary bound 337/128, output
  contraction); only those finite ingredients were verified here.
* The convexity step from constant support-pencil spectrum to
  W(N) = closed unit disk remains an analytic source argument.
* The I287 equality-case structure claims (rank-four boundary field,
  D inertia (2,2,2), H^{1/2}DH^{1/2} = 0) — different artifact, not read.
* Upstream theorem truth (assumed per campaign rules), novelty, priority.
* **No claim about the general reliability of any model** is made or
  supported by this artifact.

## Candid assessment

* Both required defects are repaired and demonstrated: the tensor negative
  control now distinguishes the conventions exactly (permuted attainment
  holds, unpermuted fails with the review's exact residual), and rank
  claims are recomputed from the actual argument with regression controls
  that would catch any future baseline-reuse regression.
* Three bugs were introduced during this repair round and caught by the
  battery's own base-case failures before the recorded run: (1) a wrong
  import path for `kronecker_product` (SymPy 1.14 exposes it top-level) —
  caught by the new S2 exception accounting; (2) a commuting projection
  misaligned with the nilpotent blocks of the reducible control; (3) a
  wrong 2×2 block in the invariant-subspace verification. All were fixed
  before the final recorded run; the recorded run is the one here.
* `N_structure` remains an input/mutation consistency check (it compares the
  built N against `N_SPEC`), not an independent transcription check; the
  review already compared the six entries and zeros against R019/I287.
* No Lean artifact was requested or produced; no staging, commit, publish,
  shared-index edit, or agent spawn was performed.

## Handoff for the parent's independent verification

The parent can verify the repairs without trusting this report:

1. Hash-bind the inputs: `results.json` → `meta.provenance_sha256` records
   sha256 of the original `check.py`/`report.md`/`results.json`, all four
   review artifacts, the R019 finding, the I287 analysis,
   `TWENTY-FINDINGS.md`, `AGENTS.md`, and this r2 `check.py`. The original
   `check.py` hash matches the review's recorded
   `06795b22d9aff76bb8dd2a5c8563546463750ae3e3713de0675775ace3626910`.
2. Rerun: `cd .../glm-calibration-r2 && /tmp/sympy-venv/bin/python check.py`
   → exit 0 and the summary line above in ≈25 s.
3. Targeted spot checks (all exact): `Tensor_convention.data` in
   `results.json` for the flip identity and the unpermuted residual
   `2099/512 − 129√14/256` (equals the review's value);
   `Cyclic_rank.data.cyclicity` and `.star_algebra` as separate fields;
   `Control_zero_matrix.data` (dims 1/1, aggregate rejects);
   `Control_reducible.data` (ranks `{1,2,2,2,2,2}`, dim 9, exact commuting
   projection and invariant-subspace verifications);
   `Irreducibility_rationalized.data` (determinant
   `2733816767052433962421431/576460752303423488`); and per-mutant
   `exception_failures_on_expected_fail = []` everywhere.
4. Diff `check.py` against `../glm-calibration/check.py` — the only changed
   regions are the four marked repairs (D1, D2, S1, S2), the new
   certificates, the CHECKS list, the annotated MUTANTS metadata, and the
   runner/results plumbing; the exact-arithmetic certificate bodies are
   otherwise untouched.
