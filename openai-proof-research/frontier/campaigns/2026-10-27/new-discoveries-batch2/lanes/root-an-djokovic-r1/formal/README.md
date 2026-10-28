# Initial formal certificate, not full source theorem

`TwoLevel.lean` has seven definitions and nine proved theorems. It imports the pinned Mathlib. It defines the literal one-based source pair set, polynomial, Vandermonde, and monomial-orthonormal pairing, but **does not prove their conjectured value**.

Run from this lane:

```
python checks/replay.py
```

The script uses the user-specified absolute Lean binary and the cached 2026-10-14 formal project's compiled libraries. `replay.log` prints the exact definitions, selected full theorem types and their axiom sets. `verification.json` records the source hash, process status and audit output. The selected terminal lemmas cover all nine theorem dependencies; only propext, Classical.choice and Quot.sound occur.

Proved:

- `doubleStar_twoLevel_lt`, `_gt`, `_eq`, and combined `doubleStar_twoLevel`: the product evaluates to zero except at the cut k, where it is `(1-t)^(n-1)`. The statement is for every commutative ring, so it also applies to a formal indeterminate t.
- `alternating_tail`: the exact signed binomial tail for all 1≤k<n.
- `prefixDefect_antitone`: internal exponent bounds imply decreasing prefix defects.
- `eval_doubleStarPolynomial` and `numerator_twoLevel`: the evaluation bridge for the actual multivariate numerator polynomial.
- `twoGroup_evaluation`: the final signed Pascal arithmetic for all 1≤k<n.

The intended missing theorem has the exact type

```
∀ (n k : ℕ), 1 ≤ k → k < n →
  sourceInner n k =
    (-1 : ℤ) ^ (n - 1) * n.choose k * (n - 2).choose (k - 1)
```

This is recorded as text, not introduced as a theorem, axiom, or hypothesis. The assumptions imply n≥2.

Still to formalize:

1. Product factorization from `sourcePairs` into non-path Vandermonde factors and `doubleStarPolynomial`; homogeneity and internal degree bounds.
2. The alternation/coefficient identity connecting the literal `sourceInner` to divided symmetrization, with no n! or derivative factorial error.
3. Either the full Postnikov monomial formula, or the restricted edge-splitting/transfer proof supplied in discovery.md. The latter avoids general descent-set enumeration.
4. Finite coefficient regrouping into first-negative-prefix classes, its cumulative sums, and the polynomial specialization/coefficient identity. Merely assuming these would not certify the source question.
5. Assemble the literal endpoint and replay it in the final extracted packet.

No independent formal review or final-paper extraction has occurred. This is meaningful initial Lean only; the mathematical proof is in discovery.md.
