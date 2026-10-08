# W019: Factory Fable independent audit — report pending coordinator disposition

Retained verbatim below. This is a reviewer report, not blanket acceptance of
its conclusions. Task ID:
`node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-w8-literature-audit-fable-20261008-r1`.
Author: Factory claude-fable-5.1. Final authoritative state completed, no children.

+# W019 independent evidence audit (read-only; no repo edits, no children)

Scope executed: read README / RESEARCH_LOOP / RESEARCH_TEAM / `research/findings/W019-grok-recovered-report.md` / `Research/Goals.lean` / `Research/Machine.lean` (descriptionBits), read the preserved prototype line by line before running anything, verified the `/tmp/ecdlp-lit` downloads, ran four bounded probes (all < 0.1 s wall, < 11 k instrumented point ops total, well inside 60 s / 1M events). Probe scripts live only in `/tmp/w019-audit/` (outside the repo). Nothing was staged, committed, or repaired.

## 0. Download inventory (what is real evidence and what is not)

| File | Verdict |
|---|---|
| `pkc2011.pdf` (19 pp, pdfTeX) / `pkc.txt` | Genuine Bernstein–Lange–Schwabe PKC 2011 text |
| `smart-wb.pdf` (4 pp, Distiller) / `smart.txt` | Genuine Smart HPL-97-128 |
| `semaev-wb.pdf` (6 pp, dvipdfm 2004) / `semaev.txt` | Genuine Semaev ePrint 2004/031 |
| `shoup.pdf` text layer is glyph garbage; `shoup-collapsed.txt` (from the .ps) | Readable Shoup; Theorem 1 located |
| `diem-comp.txt` | Genuine Diem, Compositio 147 (2011) text |
| `diem.pdf`, `diem.txt` | **Mislabeled: these are Koike, arXiv:0908.3086 (mean curvature flow).** The report says that download "was discarded"; it was not, it sits under the Diem filename. Only `diem-comp.txt` supports Diem citations. |
| `sutherland.pdf/.txt` | Genuine secondary lecture notes |
| `duursma.pdf`, `duursma2.pdf`, `gaudry.pdf`, `duursma-springer.pdf`, `negation.pdf`, `semaev2004.pdf`, `prep.pdf`, `galbraith-survey.pdf` | **Bot-challenge HTML shells (3–13 KB), not papers.** Zero evidentiary value. Matches the report's "not retrieved" list. |
| SafeCurves pages | Not present locally; the `2^127.8`, "additive/multiplicative transfer safe", `(ℓ−1)/6` claims are unverified from local evidence. |
| `exp1_smart.py` | Byte-identical to `research/artifacts/W019-smart-original-unverified.py` (`cmp` passed). |

Scripts for the negation-BSGS toy, the orbit-index toy, the summation-box exhaustion and the λ check are **not on disk**. Those numbers are unreproduced from the report's own code; I re-derived the cheap ones independently (section 3).

## 1. Corrections to the report's logical / model claims

**1a. "Equivalently, T(q)/√q tends to 0" is false as an equivalence.** Parent objection upheld. `T = √q / log q` has `T/√q → 0` but `log T / log q → 1/2`, and it fails `ExponentBreakthrough` (which demands `budget(n)^(2k) ≤ C·q^(k−1)`, a fixed power saving `q^(1/2−1/(2k))`; Goals.lean docstring says explicitly "stronger than merely o(sqrt q)"). The report's first criterion (`log T / log q < 1/2 − 1/20` with non-shrinking gap) is the right shape; the "equivalently" clause must be deleted. Additionally no finite run can establish either asymptotic; it can only falsify a specific constant claim. The report's "apparent-exponent trap" numbers (0.309, 0.435, 0.490, 0.495) are correct (re-derived) and actually make the point against reading finite exponents.

**1b. The quotient-group / lower-bound shortcut is unsupported.** Shoup Theorem 1 (verified in `shoup-collapsed.txt` lines 166–172): a generic algorithm for Z/n making ≤ m oracle queries succeeds with probability `O(m²/p)` over random encoding and random x. Shoup's text has big-O; the `< m²/(2p)` constant is Sutherland's secondary derivation, as the report itself flags. Two corrections:
- Negation (`σ(x ± y)` with a sign bit) *is* a generic oracle operation in Shoup's model, so negation-rho is a generic algorithm already covered by `Ω(√p)` with unspecified constant. No quotient argument is needed for √2.
- The order-3 map β is **not** generic (it reads the encoding). Shoup's theorem says nothing about algorithms with a β oracle. The report's "an automorphism walk is still a walk in a generic group of size about ℓ/m, so the same bound applies to the classes" is not a theorem in any retrieved source. Orbits are not a group: in Z/5 classes `{0},{1,4},{2,3}`, adding 1 to class `{1,4}` lands in `{2,3}` or `{0}`. Parent objection upheld. Correct framing: the √|Aut| gain is a heuristic collision-count statement (BLS: "assuming standard heuristics", "reducing the average number of iterations accordingly"), and whether a generic-plus-automorphism model yields `Ω(√(ℓ/m))` is **not established here**.

**1c. "descriptionBits forbids hiding an inverse table" is overstated.** `Machine.descriptionBits` is the summed per-instruction bit length (Machine.lean 72–81), so it bounds in-program tables **only** in `ConcreteGoal` and **only** relative to the chosen `maxProgramBits`. `ExponentBreakthrough` has **no** descriptionBits clause at all (uniformity comes from one fixed finite program across the family). Neither goal constrains advice in public parameters or the encoding (Goals.lean docstring; README; W002). Parent objection upheld.

**1d. The "√|Aut| × (1+Θ(1/√r))" rejection threshold is invalid as stated.** BLS (pkc.txt 205–222, 291–316, verified) give `(1+o(1))√(πℓ/4)` iterations "assuming standard heuristics", a 2-cycle probability "approximately 1/(2r)" ("one expects"), and overhead `1+Θ(1/√r)` for *their* cycle-check schedule on *r-adding Pollard rho walks*. The report wrote "proved in PKC 2011"; BLS say heuristic. None of this is a numerical upper bound on a measured ratio for BSGS, for arbitrary implementations, or for finite samples (variance alone can exceed it). Also BLS restrict to `y² = x³ − 3x + b`; secp256k1 has a = 0 (affects only doubling counts, but the 5M+1S figure should not be quoted as curve-independent without saying so). Parent objection upheld.

**1e. "Prime-field summation polynomials are negative controls / only the automorphism direction applies"** is too strong. Semaev 2004 is formulated *for* `E(F_p)` (semaev.txt 25–38, 216–250): cost `t_{p,n}·p^(1/n+δ) + p^(2/n+2δ)`, "very probably" bounded solutions exist, solver open. Diem (diem-comp.txt 169–195, verified) says Semaev's approach "does (currently) not lead to an algorithm which is faster than generic algorithms" because "no efficient algorithm for this task is known". That is *conditional inapplicability*, not non-applicability. Diem's theorem (`e^{O(max(log q, n²))}` for `E(F_{q^n})`, Prop 2.9 with `(2+ε)n² ≤ log₂ q`, Gaudry `Õ(q^{2−2/n})` "on a heuristic basis") is quoted accurately by the report. Testing δ = 0 at p ≤ 503 cannot refute a positive-δ asymptotic; box exhaustion for one target is not index calculus (no factor base, no linear algebra, no relation count target `≈ p^(1/n+δ)`). Parent objection upheld.

## 2. Smart prototype audit (`W019-smart-original-unverified.py`)

Reproduction, exact command: `cp <artifact> /tmp/w019-audit/proto.py && /usr/bin/time -f "wall=%es" timeout 60 python3 proto.py` → identical output to the report: ANOM(43,4,2) 6/6 at 18 adds; ANOM(61,0,2) 0/6, `JP=(0,1,0)`; two ordinary controls refused with `tP=None`; HPL example m=10, `tP=1333, tQ=387`; `ops 408 sec 0.003`, wall 0.01 s.

**2a. "408 Jacobian additions" is mislabeled.** `OPS["point_add"]` is incremented by both `jac_*` and `aff_add` (including `None` adds). Instrumented split: the 12 ANOM `smart_dlp` calls use 228 Jacobian ops; the rest of the 408 is affine setup/order checks.

**2b. Ring validity over Z/p².** Jacobian add/double formulas are polynomial and commute with `Z_p → Z/p²`, so results are valid mod-p² images of true Z_p representatives *provided* inputs are genuine lifted points and branch decisions agree with Z_p. On the tested path (`jac_mul(p, affine lift)` on a prime-order anomalous curve) all intermediate operands have unit Z and are pairwise non-congruent mod p, so branches are sound; only the final addition has `H ≡ 0 mod p`, giving `X3 ≡ R²`, `Y3 ≡ −R³` (units) and `Z3 ≡ 0 mod p`. `t = −XZ/Y mod p²` is then well-defined and equals the formal log mod p² (log t = t + (2a/5)t⁵ + …, so correction terms have valuation ≥ 4 for p ≥ 5). Sanity-tested: `t([2]JP) ≡ 2·tP mod p²` and `tQ ≡ 7·tP mod p` for Q = 7G (probe_ring (5)). **No false positive is possible**: `ok=True` requires `v(tP)=1`, which is exactly Smart's hypothesis, under which the ratio is correct.

**2c. Parent suspicion on dividing all three coordinates by p: correct in principle, inert in practice.** Weighted equivalence is `(λ²X, λ³Y, λZ)`; uniform division is not. Counterexample (probe_ring (3), p=43): `(p²x, p³y, p)` satisfies `Y² = X³ + aXZ⁴ + bZ⁶ mod p²` (True); uniformly divided `(px, p²y, 1)` does not (False). However the stripping loop is **unreachable on the tested path** (0 hits, instrumented), and whenever it does fire it can only yield `None` or `t = 0` (because `Z/p ≡ 0 mod p` forces `Z ≡ 0 mod p²` in the reduced representative), i.e. `ok=False`. It cannot produce a wrong m. It is dead-but-wrong code, not the cause of any observed result.

**2d. Parent suspicion on field-branch formulas over the composite ring: confirmed with a concrete counterexample, outside the tested path.** `jac_add` tests `U1 == U2` mod p². For two **distinct E₁ points** (both Z ≡ 0 mod p), `U1 ≡ U2 ≡ 0` and `S1 ≡ S2 ≡ 0 mod p²` are forced, so the code **doubles the first operand**. Reproduced (probe_ring (4), p=43): `tP=860, tQ=473`; `jac_add(JP,JQ)` returns `t=1720 = 2·tP`, whereas the true sum has `t ≡ tP+tQ = 1333 mod p²`. This is an invalid output from the branch structure over Z/p². `smart_dlp` never adds two E₁ points, so its 6/6 results stand, but any extension (checking additivity, computing `[p](Q̃ − mP̃)`) would silently fail.

**2e. The p = 61 failure is misdiagnosed; falsifier found.** Report: "Every integral lift of the tested point, including all p perturbations of x, satisfied [p]P̃ = O … It was not repaired." Facts:
- Point-lift perturbation **cannot** help: lifts of P differ by an E₁ element R, and `[p]R ∈ E₂`, so `[p]P̃ mod E₂` is independent of the point lift. Tested: 0/61 x-shifts succeed (probe_lift A).
- The curve lift is what matters. For `y² = x³ + 2`, every b-lift `b = 2 + 61k` is Z/p²-isomorphic (scale by a unit `u ≡ 1 mod p`, `u⁶` covers all of `1 + pF_p`), so all 61 b-lifts fail (probe_lift B, 0/61). Changing the **a**-coefficient, `a = 61k` with k ≠ 0, succeeds for all 60 values of k on the m = 7 test and **6/6 secrets at a = 61** (probe_lift D, probe_ring (6)).
- Contrast: for (43,4,2), exactly one of 43 b-lifts (k = 33) fails (probe_lift C), the expected 1/p bad-lift event.
- So the prototype's integer lift of the j = 0 curve lands in the unique bad lift class (the "[p] maps into E₂" case). Higher precision (mod p³) would not fix it; the hypothesis `v(ψ([p]P̃)) = 1` fails for that curve lift. Note the retrieved HPL-97-128 text contains **no** such caveat ("Clearly … will solve the discrete logarithm problem in linear time"); the report's hypothesis statement is correct but is the reporter's addition, not from this source.

**2f. Zero formal log / ordinary controls.** The refusal `tP=None` on orders 47 ≠ 41 is correct: `Z` is a unit because `[p]G ≠ O`, so the point is not in E₁ and ψ is undefined. Correctly labeled by the report.

## 3. Independent re-derivations of unreproducible report numbers (scripts not on disk)

Verified by my own code (probe_misc, 0.011 s): Semaev `f₃` identity on `y²=x³+x+1/F₁₇` gives **136 zeros, 0 mismatches** (matches); orbit indices `1.50 → 1.93` (negation) and `3.0 → 5.4` (order 6) for p = 13, 109 (match); secp256k1 `λ²+λ+1 ≡ 0 mod n`, `[λ]G = (βG_x, G_y)`, `β³ = 1`, `n ≠ p`, `p^k ≢ 1 mod n` for k ≤ 40 (all True); `p^((n−1)/6) ≡ 1 mod n` while `(n−1)/12` and `(n−1)/18` do not give 1 (consistent with, not a proof of, embedding degree `(n−1)/6`).

Not reproduced, treated as unsupported: the negation-BSGS "9 secrets, 18.0 vs 17.11 adds, tables of size 10" (no script; and as described, with giant stride not doubled, it is not a negation-BSGS at all, so it is not evidence about √2); the summation box exhaustion counts (343 evals / 0 relations, 4/52, 23/113); all SafeCurves figures.

## 4. Accepted limited directions and the one next experiment

Accepted as limited, correctly scoped results: Smart's trace-one reduction works on the prototype for non-bad lifts (6/6 at p=43, HPL m=10, and now 6/6 at p=61 with `a=61`); it is a negative control for secp256k1 (`n ≠ p`). The automorphism direction is a constant-factor heuristic only. Summation polynomials over prime fields are a conditional (solver-missing) direction, not a refuted one.

Rejected: the three logical shortcuts in 1a–1d, the "proved" label on BLS heuristics, the Jacobian-op count label, and the p=61 diagnosis.

**Next meaningful experiment** (bounded, falsifiable): a *correct* negation BSGS on the small ordinary coordinate curve already in Lean scope: baby table of `⌈√(ℓ/2)⌉` entries keyed on the canonical representative of `{P, −P}`, giant stride `2m+1`, run on **all ℓ scalars** (not nine), counting group ops separately from key/sign work. Prediction to test: total group ops ≈ `(1/√2)·(plain BSGS)` + table-size overhead; any ratio outside `[1/√2 − ε, 1]` across *all* scalars indicates a counting error, with ε fixed before the run. This replaces the invalid BLS-derived threshold with an exact, deterministic, all-input check that fits the project's `SolvesWithin` semantics.

Probe files for the coordinator: `/tmp/w019-audit/{proto.py,probe_lift.py,probe_ring.py,probe_misc.py}`; run each with `timeout 60 python3 <file>`.
