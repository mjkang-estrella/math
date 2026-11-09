# SUMMARY — pi-fibonacci-minima-source-hypothesis-r312

**Hypothesis:** MathDB 371202 — Pudelko Conjecture 8, arXiv:2510.24882 (reported v5) — probability distribution of Fibonacci sequence minima.

**Disposition: RETIRE — resolved (public counterexample + in-house formalized outcome); residual source-law ambiguity closed by this lane.** No new outcome proposed; counts unchanged (9 additional / 39 total).

## 1. Exact source law (established, not assumed)

Source v5, Conjecture 8 + remark (14) (layout text `src-2510.24882` bound in `frozen/freeze-note.json`):

- **Sampling law:** "random integer initialization {a₀,a₁} ∈ Z²"; remark (14) explicitly asserts for bounded initializations {a₀,a₁} ∈ [−N,N]²∩Z² that **P_N(n) = P(n) + ε(N), ε(N) → 0**. So the only reading with literal content is: P(n) := box-sampling limit. (The remark's ratio is written r = a₀/a₁; the cone structure is the transpose of r = a₁/a₀ used below — same conclusion.)
- **Index set:** bi-infinite; |aₙ| → ∞ both directions, minimum attained. **Ties:** immaterial for the limit — tie events lie on finitely many lines through the origin (aₙ = Fₙa₁ + Fₙ₋₁a₀ are pairwise non-proportional integer forms); exactly, weak count = strong count + 2⌊N/3⌋ + 2⌊N/2⌋ + 1 (verified exactly at N ∈ {10, 40}; prior Lean proof bounds the gap by 2(2N+1)).
- **Meaning of (13):** it is exactly the *angular* (uniform-direction) cone law. The argmin-0 cone has total angle 2[(π/2 − arctan 3) + (π/2 − arctan 2)] = 2(π − 3π/4) = **π/2** exactly (arctan 2 + arctan 3 = 3π/4), giving P(0) = 1/4 under angular sampling. The formula sums to exactly 1 over Z (Σ_{n≥0} = 3/4; Σ_{n≥2} = 1/4 via 2·arctan(1/φ) = arctan 2). So (13) contains **no typo and no mass error** — the sole defect is the sampling claim (14).

## 2. Decisive calculation (exact; no simulation in any decision)

**Criterion.** For (x,y) ≠ (0,0) the sequence has its absolute minimum *uniquely* at 0 ⟺ (after negating to x > 0) **y > 3x or y < −2x**, plus the axis case x = 0, y ≠ 0. Necessity: neighbor ratios at n = ±1, ±2 give |y|>|x|, |y−x|>|x|, |y+x|>|x|, |2x−y|>|x| ⟺ y>3x ∪ y<−2x. Sufficiency: y>3x → forward tail positive increasing, backward tail opposite-sign growing (|a_{n−2}| = |aₙ| + |aₙ₋₁|); y<−2x → forward tail negative with |aₙ| = (−r)Fₙ − Fₙ₋₁ increasing (Δ = (−r)Fₙ₋₂ − Fₙ₋₃ > 0 for −r > 2). Verified against brute-force window argmin (|n| ≤ 140, exact ints) over the full box N = 60: **0 mismatches**.

**Count.** #(unique min at 0) = C_N = 2N + 2Σ_{j≤⌊(N−1)/2⌋}(N−2j) + 2Σ_{j≤⌊(N−1)/3⌋}(N−3j) = 2N + (2mN−2m²−2m) + (2kN−3k²−3k). Loop == direct predicate == closed form for N ∈ {1,2,3,5,10,40,111,300}; C_300 = 75000 = 5·300²/6 exactly.

**Limit.** C_N = 5N²/6 + O(N) ⟹ **lim P_N(0) = 5/24 ≠ 1/4** (exact-rational error 2.08×10⁻⁷ at N = 10⁶, ~1/N decay). Weak (tie-inclusive) limit identical; any deterministic tie rule lies between them. Hence Conjecture 8's n = 0 case — and remark (14)'s ε(N) → 0 claim — are **false** under the source's own law. The shift map (x,y) ↦ (y, x+y) (det ±1) transfers the count to n = 1, giving lim P_N(1) = 5/24, matching the source's P(n) = P(1−n) symmetry.

## 3. Prior coverage (bounded)

- **MathDB record:** status *open*, but carries a public **counterexample** by Shivam Patel (2026-08-20, UUID 009c10c4-…-0b9ae15e58a3): lim P_N(0) = 5/24. Zero review votes; the record's progress check ran 31 s *after* the posting and never accounted for it. Cached record only (429 hold respected).
- **In-house:** `frontier/campaigns/2026-10-25/extension-fibonacci-minima` — complete Lean formalization `FibonacciMinima.fibonacci_minima_square_counterexample` (cone criterion, exact count, strict + weak limits 5/24, tie-rule exclusion), pinned audit, 48 declarations, only propext/Classical.choice/Quot.sound; explicitly credits Patel and qualifies "square-uniform interpretation". Sibling 371201 (Conjecture 7) already counted in that campaign — not touched.
- **Versions:** v2 Conjecture 20 → v5 Conjecture 8 reconciled; **v5 (2026-04-09) is current** (arXiv submission history checked live 2026-10-30). Bounded search found no published proof/refutation/successor (only arXiv pages and mirrors; not exhaustive).
- **New this lane:** v5's remark (14) explicitly claims the box-limit convergence, which the prior lane's v2-based qualification ("source does not specify the sampling") left open. This upgrades the framing to *refutation of the source's own stated claim* — a documentation note for the parent, no new mathematics.

## 4. Triage audit (r303 dependencies checked, not assumed)

- "Natural density is angular measure of cones" — **false as stated**: box density weights cones by square-intersection area, not angle (5/24 vs 1/4 at n=0). This was exactly the flagged trap.
- "Formula sums to 1 on n ≥ 0" — **false**: exact telescoping gives 3/4 on n ≥ 0, 1 over Z. The formula is consistent; only (14) fails.
- Triage MC (0.2086, 0.2086, 0.1873, 0.0597) — consistent with exact 5/24 = 0.2083̄ at n = 0, 1.

## 5. Strongest classical-adaptation objection

The angular version of (13) is a true, short, complete theorem (cone decomposition + Lucas-ratio angle identities + tie negligibility). Why not claim it? It is the author's own derivation ("derived under the assumption of uniform random initialization"; v2 derives from intervals between Lucas ratios), concerns a direction-uniform model with no canonical realization on integer initializations, and would be a **sampling/wording correction** — excluded from substantive credit.

## 6. Residuals (parked; non-blocking)

- Exact box limits P_box(n) for n ≥ 2 (MC suggests P_box(2) ≈ 0.1873 vs angular 0.1476) — same cone/area method, not needed for the disposition.
- Parity-recurrence counterpart — Fibonacci-refutation already suffices against "either … or".

## 7. Runnable checks

`checks/verify_371202_exact.py` — pure integer arithmetic; run under the guard:
`OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 python3 ../sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py python3 checks/verify_371202_exact.py`
Latest output: `checks/run_output.json` (A: 0 criterion mismatches; B: loop=direct=closed, tie brute=closed at N ∈ {10,40}; C: 5/24 limit flag True; D: exact angular identities).

## 8. Failures preserved

Two guarded-run failures are preserved in history: a Fraction-not-JSON-serializable crash and a wrong closed-form parenthesization (`2*(kN−3k²−3k)` vs `2kN−3k²−3k`) plus an inverted tail flag — both caught by exact cross-checks (loop vs closed form), fixed, and re-verified. The initial criterion omitted the x < 0 negation reduction, caught by the closed-form mismatch at N = 300.

## 9. Source/provenance bindings

All inputs hash-bound in `frozen/freeze-note.json` *before* content reads (record sha256 6fd96a7f…b2f4 matches the r303/r311 registration; PDF 0abb26a3…a7a6; layout b7465fa7…cbb7; r311 proposals 3679cab1…a8939). Flat references only; no recursive duplication. Access: arXiv HTTP 200; exa web search; no MathDB/GitHub/ScienceDirect/Google routes. All first-pass statements remain unqualified for acceptance; this lane makes no novelty claim beyond the audit above.
