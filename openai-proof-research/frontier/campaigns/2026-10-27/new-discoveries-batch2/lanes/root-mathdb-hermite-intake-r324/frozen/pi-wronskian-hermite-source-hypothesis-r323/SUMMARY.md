# MathDB 338289 — Integer-coefficient conjecture for Wronskian Hermite polynomials

**Disposition: RETIRED — resolved by a public theorem (no substitute target).**

## Scope (literal, from the frozen MathDB record + source body)

Source: N. Bonneux, M. Stevens, *Recurrence Relations for Wronskian Hermite Polynomials*,
arXiv:1801.07980 (v1, 2018-01-24), published SIGMA 14 (2018) 048.

- **Definition 2.2**: for a partition λ of length r, with degree sequence
  n_λ = (λ₁+r−1, …, λ_r) and Δ(n_λ) = ∏_{i<j}(n_j − n_i),
  `He_λ := Wr[He_{n_1},…,He_{n_r}] / Δ(n_λ)` (probabilists' He_n, monic). By [source, Lemma 2.1] He_λ is monic of degree |λ|.
- **Conjecture 3.7**: for every partition λ, `He_λ(x) ∈ Z[x]` (rationality stated as known; source verified |λ| ≤ 35 in Maple).

The MathDB record is statement-only with no prior qualification; it matches Conjecture 3.7 exactly.

## Resolution screen (primary/successor gate)

Citation sweep of the source (Semantic Scholar, 12 citing papers, all titles reviewed) found the
**same authors' successor body** resolving the conjecture:

**N. Bonneux, Z. Hamaker, J. Stembridge, M. Stevens, *Wronskian Appell Polynomials and
Symmetric Functions*, arXiv:1812.01864 (v1 2018-12-05, v2 read; published Adv. Appl. Math.,
DOI 10.1016/j.aam.2019.101932, 2019).**

Verified **in the actual body** (not from abstract):
- Definition (1.2): `A_λ = Wr[A_{n_1},…,A_{n_r}] / Δ(n_λ)`, n_λ = (λ_r, …, λ₁+r−1) — identical
  monic normalization to source Def. 2.2 (they cite [6, Lemma 2.1]).
- **Theorem 5.8**: if (A_n) is an Appell sequence with cumulants c_k (eq. (3.9)) and
  `c_k/(k−1)! ∈ Z` for all k ≥ 1, then `A_λ ∈ Z[x]` for all λ ∈ Y.
  Proof route: φ_A(H(λ) s_λ) = A_λ (Theorem 4.1); H(λ)s_λ ∈ Z[p_μ] (Macdonald I.7 Ex. 17(a));
  φ_A(p_n) = c_n/(n−1)! (Prop. 4.3).
- **Corollary 7.1**: "For any partition λ, we have He_λ ∈ Z[x]." — exactly Conjecture 3.7.
  Applicability: Hermite has generating series exp(xt − t²/2), so c₂ = −1 and c_k = 0 (k ≠ 2);
  c₂/1! = −1 ∈ Z. Theorem 5.8 applies verbatim.

**Scope match**: exact — every partition λ (including ∅: He_∅ = 1), same monic He_λ, same Z[x] claim.
Chronology: source conjecture 2018; resolution v1 Dec 2018 / published 2019. The MathDB open
label is stale ("An open record label is not evidence").

## Interpretation check (diagnostic, not proof)

`checks/check_he_lambda_definition.py` (exact Fractions, run under helper_guard, PASS):
He_λ for λ ∈ {(1),(2),(3),(1,1),(2,1),(2,2),(3,1),(4,2,1),(3,3,1),(5,2,2,1)} — all monic of
degree |λ|, all integral, matching hand computation (e.g. (1,1) → x²+1, (2,1) → x³, (2,2) → x⁴+3,
(3,1) → x⁴−2x²−1). Confirms the reading of Definition 2.2; it is NOT the proof.

## Decision

Per instructions: a public theorem resolves the exact scope ⇒ **RETIRE, no substitute target**.
No further computation invested. No credit changes. The proof is ordinary and public; nothing
here is a claim of new mathematics.

## Unresolved gaps (honest)

- The published AAM version was not fetched (ScienceDirect prohibited by access constraints);
  the arXiv v2 PDF is the body read (v2 == unversioned fetch, byte-identical). The AAM
  correspondence rests on DOI/journal metadata, not a body diff.
- No exhaustive registry clearance was attempted (not required for retirement by a direct
  successor theorem); Semantic Scholar citation list (12 items) and web search were the sweep.
- Integrity PASS of this lane is not a mathematical PASS — here there is no mathematical claim
  of ours to pass; the retirement rests on the retained successor bytes.

## Files

- `frozen/input-freeze.txt` — SHA256+sizes of MathDB inputs before reading (record hash matches expected 0c6bffdd…92c3).
- `frozen/source-bindings.txt` — URLs, UTC timestamps, SHA256, byte counts of all retrieved bytes.
- `primary/` — retained primary bytes (abs pages, PDFs, PDF→text extractions, S2 citations JSON).
- `checks/` — interpretation check + output. `verify.py` — post-write verifier; run it separately.
