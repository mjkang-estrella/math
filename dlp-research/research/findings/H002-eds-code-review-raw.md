# H002 EDS diagnostic independent pre-run review

Factory Fable5.1, task `ecdloop-h002-eds-code-review-fable-20261008-r1`, completed
read-only desk review. Root accepts approve-to-run for the frozen source under
the existing cap, not the estimated costs or any result inferred from them.
The integer-add counter omission and PRNG wording nit are retained below.

## Verdict: approve-to-run

No blockers. I found no mathematical, accounting, or output-path defect that would invalidate the run. Nothing was executed (not even `py_compile`); this is a desk review of `eds_diagnostic.py` (501 lines), `eds_protocol.md`, the disposition, and the r2 raw report. No children, no edits.

### Mathematics checked against the code

| Item | Lines | Result |
|---|---|---|
| ψ0..ψ4 base values (3x⁴+6ax²+12bx−a², 4y(x⁶+5ax⁴+20bx³−5a²x²−4abx−8b²−a³)) | 246–257 | Standard forms, all via field wrapper; no `**` or builtin `pow` anywhere |
| Odd recurrence ψ_{m+2}ψ_m³−ψ_{m−1}ψ_{m+1}³ ; even (ψ_m/ψ_2)(ψ_{m+2}ψ_{m−1}²−ψ_{m−2}ψ_{m+1}²) | 275–280 | Correct; base cache 0..4 means recursion only hits m≥2 (odd) / m≥3 (even), so no index drops below 0 |
| Zero handling | 258, 280, 293, 369 | Only `inv(W(2))`, never divided by an intermediate; `W(q)=0` can appear in half-index bands harmlessly; ratio numerator/denominator and every tested `W(n)` required nonzero |
| Whole-ratio exponent `e = (q²)⁻¹ mod (p−1)` | 139–151, 335–337, 294 | Extended Euclid invariants correct; `pow(num·inv(den), e)`; gcd(q,p−1)=1 holds for all five curves (residues 5,5,15,13,7) and is also enforced at 213 |
| Identity `phi(nP)=phi(P)^{n²}W_P(n)` and `χ(W(n))=χ(phi(nP))c^n` | 371–375 | Matches disposition; n² unreduced and actually exponentiated; quasi-period `χ(W(k+q))=c·χ(W(k))` at 381 |
| `c = χ(W(p−1)W(p−1+q))` | 346–347 | Valid because e is odd (p−1 even) |
| Independence of phi | 286–294, 360 | Fresh `DivisionPolynomial` per point from Q's own coordinates; k=1 reuse is safe because `scalar(P,1)==Q` is always checked (358–359) |
| Group law / scalar / admission | 171–236, 333–334, 385 | Affine add/double correct; trial-division primes, q≠p, discriminant, point count = q−1, `qP=O`, orbit closes |
| Window identity `G_A = c^{|A|k+Σa}∏χ(W(k+a))`, c=−1 twist | 404–420 | Point lookups wrapped (407), EDS reads unwrapped (409); all required keys exist since k+a ≤ q−1+8 < 2q−1 and k+a=q is excluded |
| Exclusion mask, mass, fixed +1 sign, N/T, (T+N)/2 | 400–403, 316–325, 424–428 | As specified; no label-driven sign |
| Shuffled controls | 302–313, 429–432 | Counted Fisher–Yates on labels only, all three seeds reported, no significance fields |

### Budget, accounting, output path

- Both caps checked before each increment (42–45); total can never exceed the limit; CLI can only lower (445). No reset or skip logic exists.
- Exponent work fully charged: `inv` → `pow(p−2)`, `character` → `pow((p−1)/2)`, n·n and q·q integer muls, Euclid steps. `exponent_muls` double-ticks `field_muls` as declared.
- Hidden-cost scan: `P in points` linear scan is charged (471); cache hits charged on top of reads; the only uncharged work is interpreter/PRNG/`time.monotonic()`/JSON/sha256, all declared exclusions. Elapsed is captured before hashing (487–489, dict evaluation order).
- Partial output: `result` is appended before `run_case` (468), so phase, completed rows, completed families, and `partial_event_vector` survive a stop; correlations only run after the full row loop; exit 2 on any incomplete status (496); `output["complete"]` set only after all cases (478). A write failure raises and exits non-zero rather than printing a summary.

### Expected outcome (analytical estimate, not a measurement)

Per recurrence node ≈ 30 ticks; a pointwise phi ≈ 1.1k ticks at p=59 and ≈ 1.5k at p=127, so a row costs ≈ 1.5k / 1.9k events. Rough running total: two fixtures ≈ 60k, three p=59 cases ≈ 435k, first p=127 case ≈ 315k → ~815k after 6 cases. The second p=127 case should hit the 1M cap mid-way through `pointwise_phi_and_normalization`; the p=251 cases will not run. This is the protocol's declared possibility (line 209–212), so it is not a blocker, but root should expect ≈ 6 of 11 completed cases and must not treat that as grounds to enlarge or reset. Wall-clock should be a few seconds, well under 60 s.

### Nits (describe only; none require a change before running)

1. Line 419: `sum(offsets)` and the `+1` are recomputed but only one `integer_adds` is charged; undercounts ≈ |A| trivial integer adds per c=−1 window (<0.5% of a case).
2. Line 435 writes `event_vector`, immediately overwritten at 477 by the larger delta that includes generator choice. Dead assignment; the final value is the correct one per protocol line 102–103.
3. Protocol lines 39–41: the standard even recurrence never divides by W(m); "rather than dividing by a possibly zero intermediate W(m)" could mislead a reader. Optional rewording.
4. Protocol line 141 calls control seeds 7,19,43 "independent", but they are the same integers as the generator seeds. The shuffles are still fixed, predeclared permutations and valid negative controls; "predeclared" would be more accurate than "independent".
5. A budget stop inside `validate()` leaves that `curve_record` without an `event_vector`; totals and `stop_reason` still make the stop explicit. Acceptable.

No theorem, solver, or reconstruction-cost inference follows from whatever finite correlations the run produces; the protocol states that correctly and the output carries no fields that would suggest otherwise.
