# Independent review: MathDB 336624 printed ternary sign

Decision: **PASS, exclusively as a correction to the literal printed alternating signs.** This does **not** approve a claim to resolve or refute the sign-corrected nonreducible-operation classification.

Reviewed on 2026-10-26 by the independent discrete/Fibonacci lane. The reviewer did not author this artifact and made no edits to it. The authoritative package reviewed is `thirty-proof-campaign/outcomes/ternary-sign/`.

## Exact final content reviewed

- `formal/TernarySign.lean`: SHA256 `2093e61d9604dbd26a8fc4c77466889c75304f0b0a239e1a04f55610817899ec`.
- `main.tex`: SHA256 `b6cdada4bbe2b88cbc1739cf9af22edc403a3ab16b74c3de53af55f905ce69f9`.
- Main theorem: `TernarySign.source_sign_counterexample`.

The final source includes the additional unrestricted-bijection lemma described below. The final TeX was reread after its 11-point font/margin formatting change. Authored-PDF rendering and visual QA are assigned separately to the parent; this review does not certify layout.

## Fresh kernel and dependency audit

Copied the manifest and exact formal source into the unique review scratch outcome `extension-discrete-second/review-ternary/` and ran the pinned `twenty-proof-campaign/verify_outcome.py` there. After the parent added the stronger bijection lemma, refreshed the source copy and reran the audit.

Final audit: **PASS**, Lean 4.34.1, **15 declarations**, warnings treated as errors. The verifier checked the pinned dependency revisions and audited every local declaration. Observed foundational dependencies are exactly `propext`, `Classical.choice`, and `Quot.sound`. Fresh audit/logs are in the scratch `build/` directory. No unproved bridge assumptions or prohibited proof mechanism appear in the source.

## Actual primary-source verification

Read the original archived v3 PDF text at:

- Section 2, Definition 2.1 and equation (1): the full n-ary associativity definition;
- Section 2: coordinate-wise monotonicity, permitting an increasing or decreasing map in each separate coordinate;
- Definition 3.1: reducibility as iteration of an associative binary operation;
- Example 4.10: the already known ternary alternating-sum/heap construction;
- Conjecture 5.3, equation (24), printed page 11, including the strict-monotonicity footnote.

Visually inspected the actual saved printed-page-11 rendering `extension-ternary-reserve/sources/conjecture-11.png`. The source really prints the sum from `i=1` to `n` with coefficient `(-1)^i`; this is not an extraction mistake or merely a MathDB transcription issue. The v1 archived HTML/text likewise prints those signs (equation (23) there). The MathDB formulation omits v3's added strictness word, but the witness satisfies the stronger coordinate-strict version, so this discrepancy creates no loophole.

Recomputed the v3 PDF, v3 HTML, and v1 HTML hashes; all match `primary-reference.json`. In particular the reviewed original v3 PDF hash is `4eb9d9e379ad2adf1a4365ba202a2865338c67538281344fff997169550e14e7`.

## Complete hypothesis and source-definition bridges

The witness is the actual real ternary operation `heap x y z = x-y+z`; the real line supplies an admissible totally ordered Abelian group.

1. **Full ternary associativity.** `TernaryAssociative` includes both equalities comparing `F(F(a,b,c),d,e)` with `F(a,F(b,c,d),e)` and with `F(a,b,F(c,d,e))`. These are exactly all placements required by equation (1) at arity three. `heap_associative` proves both identities, not just one placement or a weakened law.
2. **Idempotence.** `heap_idempotent` proves `F(x,x,x)=x` for every real `x`.
3. **Strict coordinate monotonicity.** The predicate requires `StrictMono` in the first and third coordinates and `StrictAnti` in the middle coordinate, for every choice of the other two arguments. `heap_strictly_monotone` proves all three. This is stronger than weak coordinate monotonicity and meets the actual v3 strict hypothesis.
4. **Arbitrary binary nonreducibility.** `Reducible` quantifies over every real binary function `G`, requiring only associativity and `G(G(x,y),z)=F(x,y,z)`. It imposes no convenient idempotence, commutativity, continuity, order, or algebraic-form restriction on `G`. The proof is complete: setting `c=G(0,0)` gives `G(c,z)=z`; associativity plus the reduction gives `G(x,c)=x`. The reduction at `(c,x,c)` then says `x=2c-x` for every `x`, contradicted at 0 and 1. Thus it rules out the full source reduction class.
5. **One-based source sum.** `PrintedRepresentation` uses `Fin 3` but the exponent is `i.val+1`. `printed_sign_sum` computes that actual finite sum as `-f(0)+f(1)-f(2)`. Hence the sign failure is attached to the printed one-based formula, with no indexing shift hidden in the formalization.
6. **Genuine inverse and obstruction.** The generator is a real equivalence, so `g.symm` is its actual inverse. On constant inputs the printed sum is `-g(x)`, while the heap is `x`; applying `g` forces `g(x)=0` for every real `x`, contradicting injectivity at 0 and 1.
7. **Arity admissibility.** The main theorem explicitly includes `Odd 3`. Three is also within the source's n-ary regime `n≥2`.

The final main theorem packages the full admissible witness, nonreducibility, odd arity, and failure of the literal printed representation. It is not merely a calculation showing the formula has a bad diagonal with no qualifying operation supplied.

## Formal-coverage observation resolved during review

The initial formal theorem excluded only `PrintedRepresentation`, whose definition includes monotone/antitone generators. The paper additionally stated that even arbitrary bijections fail. The mathematical diagonal argument already ignored monotonicity, but the stronger assertion lacked its own formal statement. The reviewer identified this mismatch.

The parent added `heap_no_arbitrary_bijection (g : ℝ ≃ ℝ)` with no monotonicity premise and the complete same diagonal contradiction. `heap_no_printed_representation` now derives the source-class result from that unrestricted theorem. The updated file was reread and freshly audited. This resolves the coverage wording issue; the final hash above includes the correction.

## Paper, attribution, and mandatory limits

The final paper provides the complete associativity, strict monotonicity, arbitrary binary-reduction obstruction, and diagonal-sign proof. It identifies the example as already present in Kiss–Somlai Example 4.10 and makes no claim of a new example or a new classification theorem. The source question, version, equation number, one-based signs, and stronger v3 strictness are accurately described.

The limitation is mathematical, not optional editorial wording: changing `(-1)^i` to `(-1)^(i+1)` represents this same heap by the identity bijection. Thus this witness supplies no counterexample to that sign-corrected statement. The abstract, scope paragraph, outcome metadata, and README expressly limit the outcome to the printed signs. No status claim concerning the intended corrected conjecture is approved by this review.

## Final verdict

**PASS: one complete literal printed-sign correction for MathDB 336624, with all source hypotheses and definition bridges covered.** No unresolved proof or source-fidelity objection remains at the exact hashes above. Count and describe it only with the explicit printed-sign-only qualification; it is not a substantive solution of the intended sign-corrected classification.
