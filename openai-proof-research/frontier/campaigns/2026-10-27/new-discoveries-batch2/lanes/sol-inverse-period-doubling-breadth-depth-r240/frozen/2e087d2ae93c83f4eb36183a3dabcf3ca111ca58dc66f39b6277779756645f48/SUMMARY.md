# Completed supporting dependency: primary Theorem 1.4

Status: **COMPLETE**. The literal finite rational sum, its nonvanishing, and its exact valuation are proved internally for every `m : ℕ`, including zero. No convergence, moment, transform, or vanishing hypothesis remains in either endpoint. This is a formalization of a published supporting theorem, with no discovery, acceptance, ledger, or count claim.

The namespace is `JacobiShifted`. Exact endpoint types:

```lean
def binomialOddSum (m : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (m + 1), (m.choose j : ℚ) / (2 * j + 1)

lemma binomialOddSum_ne_zero (m : ℕ) : binomialOddSum m ≠ 0

theorem binomialOddSum_valuation (m : ℕ) :
  padicValRat 2 (binomialOddSum m) =
    (m : ℤ) + (padicValNat 2 (m + 1) : ℤ)
```

A stronger intermediate conversion is also proved:

```lean
lemma binomialOddSum_normalized_norm (m : ℕ) :
  ‖((binomialOddSum m /
      ((2 : ℚ) ^ m * (m + 1 : ℚ)) : ℚ) : ℚ_[2])‖ = 1
```

## Files and integration

- `formal/BinomialMoments.lean`: literal sum and positivity; factorial/odd-product coefficients; convergence and summability; positive-index moment recurrence with its zero boundary proved; moment vanishing; tail identities and estimates.
- `formal/FiniteTransform.lean`: an explicit rational-polynomial linear functional, its algebraic boundary identity, beta recurrence, and binomial expansions.
- `formal/BinomialOddSum.lean`: identification of the beta coefficients, finite rational binomial transform, finite summation by parts, unit proof, and requested valuation endpoint.
- `formal/Audit.lean`: exact type checks and axiom prints for every one of the 57 completed definitions/lemmas/theorems. It also prints the literal `binomialOddSum` definition.
- `logs/axiom-report.log`, `axiom-audit-receipt.json`: successful original audit and machine-checked allowed-axiom inventory.
- `replay/fresh/`: separate byte-identical extracted source copy and successful fresh build logs.
- `replay/fresh-replay-receipt.json`: commands, source hashes, log hashes, exit codes, sampled resource receipts, and before/after hash agreement.
- `dependency-pins.json`: actual package revisions, source/olean hashes for external direct imports and core padic files, manifest hash, and Lean executable hash.
- `provenance.json`: inputs, outputs, proof status, validation, and scope record.

To consume this packet in place, run from this lane's root and import `formal.BinomialOddSum`. For integration elsewhere, copy all three proof modules together and adjust their two local imports to the chosen module prefix. No root live source definitions or Jacobi implementation module is used.

## Internal proof

Write `c_k = k! / ∏_{j≤k}(2j+1)`. Odd denominators have norm one, so `‖c_k‖₂ = ‖k!‖₂ ≤ (1/2)^(k/2)`. This proves convergence and summability of every bounded integral weight, including the binomial weights.

The checked positive-index recurrence is

```lean
lemma binomialMoment_recurrence (i : ℕ) :
  (i + 2 : ℚ_[2]) * binomialMoment (i + 2) =
    (i + 1 : ℚ_[2]) * binomialMoment i
```

This indexes the source recurrence at the positive index `i+1`; it makes no false claim at source index zero. The proof explicitly checks the vanished boundary binomial and all needed summability before shifting/subtracting sums.

For vanishing, the proof slightly shortens the source argument. Every moment has norm at most one. The recurrence proves

`(∏_{t<j}(2t+1)) M₀ = 2^j j! M_{2j}`.

Taking norms gives `‖M₀‖₂ ≤ (1/2)^j` for every `j`, hence `M₀ = 0`. No asymptotic Kummer or digit argument is needed.

The paper cites a hypergeometric transformation for its finite identity. Here it is proved algebraically: define the linear functional `L(X^j)=1/(2j+1)` on `ℚ[X]`. Prove `L(p+2Xp')=p(1)`, the beta recurrence, and `L(((1-X)/2)^k)=c_k`. Expanding `1+X=2(1-(1-X)/2)` gives, internally,

```lean
lemma binomialOddSum_transform (m : ℕ) :
  binomialOddSum m / (2 : ℚ) ^ m =
    ∑ k ∈ Finset.range (m + 1),
      (-1 : ℚ) ^ k * (m.choose k : ℚ) * momentCoeff k
```

The convergent tails satisfy `R₀=0`, `R₁=-1`, `R₂=-4/3`, and `‖R_j/j‖₂≤1/2` for `j≥2`. Finite summation by parts factors the transform as `(m+1)U_m`. Its first summand is one; the remaining finite sum has norm at most one half, so `‖U_m‖₂=1`. Rational casting and `padicValRat.div/mul/pow` then yield the requested exact valuation. Nonvanishing is independently proved by positivity of the literal rational sum.

## Pins, commands, and verification

Lean: `/home/mj-kang/Documents/Dev/math/dlp-research/.tools/lean-4.34.1-linux/bin/lean`, version **4.34.1**, commit **5045d0056413266e57c625dcd7c365b10e377c52**.

Mathlib: `/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-14/formal/.lake/packages/mathlib`, revision **d13f23b723b8a846827a245b89c10fc7d3f11612**. All nine package HEADs match the pinned manifest; eight package Lean library directories exist and are used by the frozen-template runner.

- Lean binary SHA-256: `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.
- Dependency manifest SHA-256: `d00ceb5cba2155c7c9bcc5aba05a755733331b75ded4a7f0f009320e3cde5bb8`.
- `formal/run_lean.py` SHA-256: `6c242b10c855b5daa4cd1fca6fe87e02a966fd285e2da80b76c65109dd453fbd`. This is the frozen template from commit `2ea1fd1858`; no root live formal file was read.

Every proof/audit source sets `warningAsError=true` and `autoImplicit=false`. All Lean builds are sequential, `-j1 -M4096`, under a sampled **3 GiB RSS** guard with no virtual-address-space cap.

Exact build commands, run from the lane root:

```sh
python formal/guard.py python formal/run_lean.py -j1 -M4096 -o formal/BinomialMoments.olean formal/BinomialMoments.lean
python formal/guard.py python formal/run_lean.py -j1 -M4096 -o formal/FiniteTransform.olean formal/FiniteTransform.lean
python formal/guard.py python formal/run_lean.py -j1 -M4096 -o formal/BinomialOddSum.olean formal/BinomialOddSum.lean
python formal/guard.py python formal/run_lean.py -j1 -M4096 formal/Audit.lean
```

Successful original logs: `logs/moments-final3.log`, `logs/finite-final.log`, `logs/endpoint-final2.log`, and `logs/axiom-report.log`. Early elaboration/API/linter failures are retained separately. The first audit attempt had an unsupported display option, `pp.width`; it was removed, and the complete audit was rerun successfully. No failed audit is used as a passing receipt.

The fresh extraction was created with `python replay/fresh_replay.py`, recorded in `logs/fresh-replay-driver.log`. It began without any project `.olean` files and rebuilt all three proof modules followed by the audit. Its runner resolves local modules only in the fresh extraction, plus the pinned external library paths. All four invocations exited zero, with all copied source/runner/guard hashes equal before and after. The maximum sampled combined wrapper/Lean RSS was **2,658,720 KiB**, below **3,145,728 KiB**; no guard fired. The replay is independently extracted and compiled by this same solo implementation agent, not a separate reviewer.

Both successful audit logs have been inspected. All 57 declarations have exactly the allowed axiom set `[propext, Classical.choice, Quot.sound]`. The source scan finds no `sorry`, `admit`, new `axiom`, `unsafe`, `native_decide`, `run_tac`, or `implemented_by`. No numerical experiment is used as proof.

## Source and scope

The supplied completed independent review, Section 4, and the actual cached primary Theorem 1.4 and Section 3 proofs were read. Primary: I. Area, `https://arxiv.org/html/2608.23006v2`, Theorems 1.3/1.4 and Lemmas/Theorems 3.2–3.5. The input paths and byte hashes are recorded in `provenance.json`; no fresh HTTP request was needed.

Gaps for this assigned dependency: **none**. This packet does not formalize the full source Jacobi object or its shifted denominator law. It makes no claim about those other components.

All writes were confined to this assigned lane. Work was solo, without children, coordination, external messages/posts/uploads/accounts, browser/preview tabs, package updates, Lake builds, shared/other-lane edits, or ledger/count changes. The frozen runner was obtained with read-only `git show` at the explicitly supplied commit; no Git mutation, staging, or commit occurred. No active Karp/BBK workers or root live formal sources were read or polled.
