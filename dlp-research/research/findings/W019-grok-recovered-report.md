# W019: recovered Grok report — UNACCEPTED pending independent audit

Date: 2026-10-07 local (2026-10-08 UTC). This is a retained delegate report,
not an accepted mathematical, experimental or performance finding.

The original T3 task still reported running/working with summary null, but its
durable timeline contained this complete assistant result at position 144,
updated 2026-10-07T23:33:48.137Z, item status completed. Coordinator recovered
it with t3_thread_read (read only; no child-thread messaging or new thread).
The read was untruncated. Task ID:
`node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-w1-literature-grok-20261007-r1`.

Primary extracts and an experiment are present under /tmp/ecdlp-lit; presence
alone does not verify their source attribution, formulas or results. Failed
retrievals, narrowed toy samples and hypothesis boundaries must be audited.
No empirical/runtime claim below is adopted merely by retaining the report.

## Run closure and independent audit

After retaining the complete report, coordinator closed the unfinalized owned
run with task_cancel request `ecdloop-w1-literature-close-recovered-20261008-r1`.
A subsequent task_status returned interrupted/result_available, no pending
children, and published the recovered report. No duplicate original research
run was launched. The report itself remains unaccepted pending source audit.

New focused read-only review: Factory claude-fable-5.1, request
`ecdloop-w8-literature-audit-fable-20261008-r1`, task ID
`node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-w8-literature-audit-fable-20261008-r1`.
The brief supplies the objections below, asks primary-source verification and
bounded reproduction of the Smart prototype, and prohibits repair/edits/children.

Original prototype retained verbatim at
research/artifacts/W019-smart-original-unverified.py, SHA256
`b64146e2e18db20303abe28febfaccb4b09de22fa6ad27d0419903589494a542`.
It is unverified historical evidence, not an accepted algorithm or benchmark.

## Recovered report (verbatim)

None of the three directions is an exponent improvement on an ordinary prime-field prime-order curve. The only one that applies to that setting is a constant-factor automorphism reduction, at most √6 on a j=0 curve. Anomalous curves and prime-field summation polynomials are negative controls.

The Lean target in `Research/Goals.lean` asks for one program whose worst-case tape budget `T` satisfies `T(n)^(2k) ≤ C · q(n)^(k−1)`, i.e. `T = O(q^(1/2 − 1/(2k)))`, on every scalar. A constant factor does not meet that. `SolvesWithin` is deterministic and all-input. Pollard rho is an expected-cost Monte Carlo method. `descriptionBits` forbids hiding an inverse table in the program. The scaffold is still a cyclic-orbit interface. `Research/Secp256k1.lean` only checks that `G` lies on `y^2 = x^3 + 7` and that `n < 2^256`. No files were edited.

## 1. Automorphism / endomorphism constant factors

**Claim.** A random walk that is constant on classes of an easily computed automorphism of order `m` collides on about `ℓ/m` classes. For negation, Bernstein–Lange–Schwabe (PKC 2011, IACR archive) prove a branchless algorithm using `(1+o(1)) √(πℓ/4)` iterations as `ℓ → ∞`, under the standard random-walk heuristics, against `√(πℓ/2)` without negation. Each iteration is one batched affine addition: 5 multiplications and 1 squaring mod `p`. Fruitless 2-cycles appear with probability about `1/(2r)` per step and slow the walk by `1 + Θ(1/√r)`. That factor tends to 1 only if the precomputed table size `r → ∞`. For most curves the only easy automorphism is negation. secp256k1 is `j = 0` and `p ≡ 1 (mod 3)`, so `(x, y) ↦ (βx, y)` with `β^3 = 1`, `β ≠ 1`, together with negation, gives a group of order 6. The Duursma–Gaudry–Morain paper usually cited for a general `√m` factor was not retrieved. PKC only says the iteration count drops “accordingly.”

**Proven vs heuristic.** The iteration formula and the `1 + Θ(1/√r)` overhead are proved in PKC 2011 from the birthday model and the cycle calculation. The model itself is heuristic. SafeCurves (2013.10.13) records the historical change as exactly this `√2`, from `√(π/2) ≈ 1.253` to `√(π/4) ≈ 0.886`, and lists secp256k1 at `2^127.8`. That published figure is the negation-only cost. It does not include a further `√3`.

**Generic bound.** Shoup (Eurocrypt 1997), recovered from the PostScript: any generic algorithm that solves the DLP in `Z/n` with high probability makes `Ω(√p)` group-oracle queries, `p` the largest prime factor of `n`. Sutherland’s lecture, a secondary write-up of Shoup, states success probability `< m^2 / (2p)` after about `m` black-box calls. An automorphism walk is still a walk in a generic group of size about `ℓ/m`, so the same bound applies to the classes and caps the gain at `Θ(√m)`. It does not forbid using the coordinate formula for `β`. It does forbid reading `√(ℓ/6)` as an exponent break.

**Costs.** Low memory for rho itself (Pollard; van Oorschot–Wiener distinguished points, as cited by PKC and SafeCurves). Negation needs `r` precomputed points. Success after `m` additions is about `m^2/ℓ` (SafeCurves). GLV uses the same endomorphism to speed scalar multiplication, which is a different problem.

**Toy check.** On `y^2 = x^3 + 1` for `p ≡ 1 (mod 3)`, the number of points divided by the number of orbits under negation rose from 1.50 (`p = 13`, `N = 12`) to 1.93 (`p = 109`, `N = 108`). Under the order-6 map it rose from 3.0 to 5.4. Square roots of those indices: 1.22 → 1.39 toward `√2 ≈ 1.414`, and 1.73 → 2.32 toward `√6 ≈ 2.449`. Fixed points (identity, 2-torsion, `x = 0`) keep the index below 6. Sampled images stayed on the curve (`homo_fail = 0` on up to 90 pairs). That is not an exhaustive homomorphism proof.

A careful negation BSGS on `y^2 = x^3 + x + 7` over `F_83`, order 79 prime, recovered all 9 tested secrets. Mean additions were 18.0 plain and 17.11 with a sign bit stored in the table. Both tables had size 10. The baby window was too short to contain both `P` and `−P`, so the `√2` never appeared. The 0.89-add gap is one boundary secret, `78 = −1`. An earlier version that re-multiplied to recover the sign was slower (mean 23.9). This matches the PKC warning that overhead can erase the factor.

**Apparent-exponent trap.** `T = √(N/6)` has `T/√N = 1/√6 ≈ 0.408` at every size, while `log T / log N` is 0.309 at `N = 108`, 0.435 at `10^6`, 0.490 at `2^128`, and 0.495 at `2^256`. A toy curve that prints “exponent 0.31” is the constant `√6`.

On secp256k1 itself, `p ≡ 1 (mod 3)`, `−3` is a square mod `p` and mod `n`, and

`λ = 0xac9c52b33fa3cf1f5ad9e3fd77ed9ba4a880b9fc8ec739c2e0cfc810b51283ce`

satisfies `λ^2 + λ + 1 ≡ 0 (mod n)`. Direct affine arithmetic gave `[λ]G = φ(G)` on both coordinates. That checks the eigenvalue. It does not compute a discrete log.

## 2. Anomalous curves, as a negative control

**Claim.** Smart, HP Labs HPL-97-128 (1997): if `#E(F_p) = p`, lift `P` and `Q` to `Z/p^2` and read `m` from the ratio of p-adic elliptic logarithms of `[p]P̃` and `[p]Q̃`. Cost is `O(log p)` operations on the lift, once the group order is known. SafeCurves calls the same transfer the Smart–ASS attack (Semaev 1998, Satoh–Araki 1998, Smart 1999) and marks secp256k1 safe against additive transfer because `ℓ ≠ p`, and safe against multiplicative transfer with embedding degree `(ℓ−1)/6`.

**Proven vs heuristic.** The reduction is a proof for trace-one curves, assuming the group order and a lift whose `[p]`-multiple is nonzero in the formal group at order exactly `p`. It is not a heuristic.

**Generic bound.** It does not apply. The algorithm uses the field representation and the formal logarithm, not a group oracle. The hypothesis `#E = p` is false for secp256k1: the run checked `n ≠ p`, and `p^k ≢ 1 (mod n)` for every `k = 1..40`, so the embedding degree is greater than 40. The exact `(n−1)/6` figure is the SafeCurves citation. It was not recomputed here.

**Toy check.** Script `/tmp/ecdlp-lit/exp1_smart.py`, 408 Jacobian additions, 0.003 s.

| Curve | Result |
|---|---|
| HPL example, depressed to short Weierstrass, `p = 43`, claimed `m = 10` | computed `m = 10`, 18 adds, `t_P = 1333`, `t_Q = 387` |
| `y^2 = x^3 + 4x + 2` over `F_43`, order 43 | 6/6 secrets exact, 18 adds each |
| `y^2 = x^3 + 2` over `F_61`, order 61 | 0/6, procedure returned `ok = False` |
| Ordinary controls `F_41`, orders 47 | `[p]G ≠ O`, formal log undefined, correctly refused. True log was 3 |

The `p = 61` miss is real. Every integral lift of the tested point, including all `p` perturbations of `x`, satisfied `[p]P̃ = O` in `E(Z/p^2)`, so the first-order ratio is `0/0`. The formula needs a lift of exact valuation 1. It was not repaired.

## 3. Summation polynomials

**Claim.** Semaev (ePrint 2004/031): `f_2 = X_1 − X_2`, an explicit `f_3`, then resultants. The polynomials are symmetric, absolutely irreducible, and of degree `2^(n−2)` in each variable. If bounded roots of `f_{n+1}(x_1,…,x_n,x) ≡ 0` (coordinates `≲ p^(1/n+δ)`, or rational with numerator and denominator `≲ p^(1/(2n)+δ)`) can be found in `t_{p,n}` operations, then ECDLP costs about `t_{p,n} · p^(1/n+δ) + p^(2/n+2δ)`. For `n ≥ 5` that can beat `O(√p)` for some exponential `t`. Semaev calls existence of such roots “very probably” and leaves the solver open.

Diem, Compositio Math. 147 (2011) 75–104, proves something else: ECDLP in `E(F_{q^n})` in expected time `e^{O(max(log q, n^2))}`, for every curve, with the average only over running time. That is subexponential in `log(q^n)` when `n → ∞` and `n / log q → 0`. The factor base is `{P : φ(P) ∈ P^1(F_q)}`, size `O(q)`, with no smoothness bound. Proposition 2.9 gives decomposition probability at least `q^(−1/2)` only for large `n` and `(2+ε)n^2 ≤ log_2 q`. For small `n` the proof falls back to brute force. Diem states that no efficient bounded-root algorithm is known, so Semaev’s prime-field approach does not currently beat generic algorithms. Gaudry’s `Õ(q^(2−2/n))` for fixed `n ≥ 2` is cited by Diem as heuristic. For `n = 2` that matches generic `√(#E) ≈ q`. Any advantage starts at extension degree `n ≥ 3`.

**Generic bound.** It does not apply, because relation generation uses coordinates. On a prime field the conditional algorithm still does not supply an `ExponentBreakthrough`: the solver is missing, and Diem says the known prime-field route does not beat generic methods. Semaev’s cost also stores about `p^(1/n+δ)` relations and then runs linear algebra, far more memory than rho.

**Toy check.** On `y^2 = x^3 + x + 1` over `F_17`, all 729 triples of x-coordinates: algebraic zeros of `f_3` and geometric sums to the identity agreed exactly (136 zeros, no mismatches). The identity holds.

Exhaustive search for a relation with all x-coordinates inside a box of width about `p^(1/3)` found 0 relations at every tested prime. By `p = 211` the box already cost more than a BSGS proxy (125 evaluations against 16). At `p = 503`, `N = 464`: 343 evaluations, 0 relations, BSGS proxy 22. Allowing the third variable to be free, the fraction of targets that decomposed was 4/52 = 0.077 at `p = 101` and 23/113 = 0.204 at `p = 211`. Semaev’s “very probably,” read at `δ = 0`, is false at these sizes. That does not refute a large-`p` asymptotic. The `n = 5` expression `p^(1/5) + p^(2/5)` was only evaluated, not executed: about 0.70–0.86 times the BSGS proxy at these primes, and it assumes the unproven solver.

## Next candidate, and when to reject it

The tractable next measurement, after Sol’s small ordinary curve exists, is a negation baseline, and separately an order-6 class baseline on a `j = 0` toy curve, against plain BSGS. Count group operations. Treat it as a constant-factor calibration.

**Reject it as progress toward `ExponentBreakthrough` unless both of these hold on a growing family of ordinary prime-order curves, with `ε = 1/20` fixed before the runs:**

- `log T(q) / log q < 1/2 − 1/20` at every larger `q` in the family, and the gap does not shrink toward 0 as `q` grows.
- Equivalently, `T(q)/√q` tends to 0. A pure `√6` stays at 0.408 and is a rejection.

Also reject the run if the measured operation ratio against plain BSGS is larger than `√|Aut|` times the fruitless-cycle factor (`√2 · (1+Θ(1/√r))` for negation). A bigger ratio means the counter is not measuring the orbit reduction. Reject any curve with `#E(F_p) = p` as a benchmark. Reject an unconditional prime-field summation exponent claim unless it comes with a proved bounded-root solver that beats exhaustive search on the same box.

This is not a new attack. Rho’s expected cost still does not discharge `SolvesWithin`.

## Sources actually read, and what failed

Retrieved and used:

- Shoup, https://www.shoup.net/papers/dlbounds1.ps — Theorem 1, `Ω(√p)`. The PDF text layer was glyph garbage. The exact success-probability constant in Shoup’s own text did not extract cleanly.
- Sutherland, secondary: https://math.mit.edu/classes/18.783/2013/LectureNotes11.pdf — Theorem 11.1, probability `< m^2/(2p)`.
- Bernstein–Lange–Schwabe, https://www.iacr.org/archive/pkc2011/65710132/65710132.pdf — `(1+o(1))√(πℓ/4)`, fruitless cycles `1/(2r)`, overhead `1+Θ(1/√r)`.
- Smart, Wayback of http://www.hpl.hp.com/techreports/97/HPL-97-128.pdf — trace-one reduction and the `m = 10` example.
- Semaev, Wayback of https://eprint.iacr.org/2004/031 — conditional cost and the open solver question.
- Diem, https://www.cambridge.org/core/services/aop-cambridge-core/content/view/59B877810708C90F6287972486A5BF0C/S0010437X10005075a.pdf/on_the_discrete_logarithm_problem_in_elliptic_curves.pdf — the extension-field theorem and the statement that prime-field summation does not currently beat generic algorithms.
- SafeCurves, 2013.10.13: https://safecurves.cr.yp.to/rho.html and https://safecurves.cr.yp.to/transfer.html — secp256k1 rho `2^127.8`, additive and multiplicative transfer both safe, embedding degree `(ℓ−1)/6`.

Not retrieved, so not used as evidence: direct ePrint PDFs including 2011/003, 2004/031, 2017/1113, and 2015/1022 (HTTP 403); the cr.yp.to full negation PDF (403); `hpl.hp.com` itself (timeout); Duursma–Gaudry–Morain and Gaudry via HAL/Springer (HTML shells); `arXiv:0908.3086` (that download was Koike on mean curvature, and it was discarded); the Leipzig small-genus PDF (404). The Corrigan-Gibbs–Kogan preprocessing bound was not read and is not stated here.

## Coordinator's initial objections

- `T(q)/sqrt(q) -> 0` is not equivalent to a fixed exponent improvement:
  `sqrt(q)/log(q)` is a counterexample. The project's goal deliberately requires
  the stronger power saving. A finite trend cannot establish either asymptotic.
- `descriptionBits` by itself does not forbid inverse tables or input advice;
  explicit budgets and encoding admissibility are needed (W002/W011/W016).
- Negation/automorphism orbits are not automatically a quotient group with a
  well-defined inherited operation. In Z/5, 1 and -1 share a negation class,
  yet adding 1 gives classes of 2 and 0. Applying an ordinary generic-group
  lower bound to orbit cardinality needs an appropriate model, not that shortcut.
- A heuristic collision factor and an unspecified Theta overhead are not a
  universal numerical upper bound on measured speedups or a valid rejection
  threshold for arbitrary implementations/finite samples.
- The summation-polynomial approach can be formulated for ordinary prime-field
  curves; missing efficient relation/root solving is not the same as inapplicability.
  Testing delta=0 or very small primes does not refute a positive-delta asymptotic.
- The nine-secret BSGS toy sample is not all-input evidence. Source and cost
  scopes, the failed trace-one lift, and all alleged runtimes need reproduction.

These objections are preliminary logical checks, not a replacement for the
forthcoming primary-source/experiment audit. No new attack is accepted.
