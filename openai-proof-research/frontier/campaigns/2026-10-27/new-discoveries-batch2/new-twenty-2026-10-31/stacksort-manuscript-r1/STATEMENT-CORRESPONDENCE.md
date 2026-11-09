# Statement correspondence: MathDB 345545

This is a DRAFT with zero accepted credit; the root decides. The full table is Table 3 of `paper.pdf`. The round-6 lane's own note is preserved at `evidence/formal-r6/STATEMENT-CORRESPONDENCE.md`.

## Source reading (substantive; carries any credit)

- **Source.** Defant and Propp, arXiv:2002.07144 v3/v4, Conjecture 4.4 (EJC 27(3) P3.51, Conjecture 23). It states that lim_{n→∞} deg(s : S_n → S_n)^{1/n} ∈ (1.68, 1.73), with deg as in Definition 1.1, the average fibre multiplicity.
- **Lean definitions.**
  - `StackSort.Conj := ∃ L : ℝ, Tendsto roots atTop (𝓝 L) ∧ L ∈ Set.Ioo 1.68 1.73`;
  - `roots n = deg n ^ (1/(n:ℝ))`;
  - `deg n = (P n : ℝ) / n!`;
  - `P n` is the literal number of pairs in `words n × words n` with equal `s`-image;
  - `words n` is the set of permutations of `List.range n`;
  - `s` is the literal max-split map.
  - The bridges are `P_eq_sum`, `fibre_square_identity`, `deg_eq_average`, `words_card` and `s_map_orderEmbedding` (the label shift 0..n−1 ↔ 1..n).
- **Endpoints** (`StackSortFinal6.lean`, namespace `StackSort.Round6`):
  - `mathdb_345545 : ¬ Conj`;
  - `limit_ge : ∀ L, Tendsto … → 1.73 ≤ L`;
  - `nonvacuity : ∃ᶠ n in atTop, 1.73 < deg n ^ (1/n)`;
  - `subsequence_companion : ∀ k, 1.73 < roots (index 130 k)`, with `index 130 k = 131·2^k − 1`.
- **Not formalised.**
  - Existence of the limit (the source's Theorem 2.5);
  - any bound above 1.73 (the ordinary proof gives > 1.73006 from G_130, and ≥ 1.80468 from the exact P_82);
  - the general recursion beyond the seed cone (the formal recursion is clipped to r, s ≤ min(M, 21−M)).
- **Conventions.** `roots 0 = 1` because 1/0 = 0 in ℝ; this has no effect at infinity.

## MathDB paraphrase (defective; no credit)

- **The record's wording.** MathDB says "deg(s : S_n → S_n) denote its maximum fiber size".
- **Lean definitions.**
  - `maxFib n` is the supremum over w ∈ words n of the size of the fibre of s(w);
  - `maxRoots n` is its n-th root;
  - `ConjMax` is the same existential as `Conj`, for `maxRoots`.
- **Endpoints.**
  - `mathdb_345545_max : ¬ ConjMax`;
  - `max_companion : ∀ n ≥ 5, 1.73 < maxRoots n`.
  - Both come from the 2^(n−1) family of identity preimages (`family`, `StackSortMaximum.lean`).
- **Status.** This reading is refuted trivially and earns no credit.

## Version scope

- arXiv v1 and v2 (17 and 18 February 2020) have only the remark "(1.6, 1.8)", which is also refuted, since the exact bound exceeds 1.8 for a = 79..82.
- The numbered conjecture with (1.68, 1.73) appears in v3 (29 March 2020) and v4 (27 September 2020), and in the EJC version as Conjecture 23.
- Defant restated it as open in Troupes, Cumulants, and Stack-Sorting (arXiv:2004.11367v2; Adv. Math. 2022), Section 7.6, with the lower bound 1.62924 (Theorem 7.29).
