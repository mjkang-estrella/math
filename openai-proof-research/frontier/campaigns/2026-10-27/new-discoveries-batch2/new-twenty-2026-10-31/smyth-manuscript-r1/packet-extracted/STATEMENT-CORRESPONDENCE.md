# Literal statement correspondence

Local source: ../expanded-corpus-r151/sources/text/1512.04084.txt, extracted from arXiv:1512.04084v1. Text SHA256: ce073f41358754ce8042a6639116f1731c35b6914d30e55d829ed9650d0182be. PDF SHA256: 144eaaff58f9c87e98ce4f8189d30a5fa93b44670e27fcdfd83137fdf3cff007.

| Source text lines | Source object | Formal correspondence |
| --- | --- | --- |
| 51–60 | Nonnegative integers; partitions with finite support; equal weights and all positive prefix sums | Base.lean:24–29, psum and DomL. Lists can have different lengths. take beyond a list's length contributes no further summands, precisely zero padding. Prefix 0 adds the tautology 0 ≤ 0. Bridges.lean:52–71 proves the finite test equivalent to all prefixes for five parts. |
| 146–155 | [m] = {1,…,m}, [0] empty; maps to ℕ with weight n | Base.lean:17, U m n is the sum-n subtype of Fin m → ℕ. Fin m uses indices 0,…,m−1, identified with [m] by adding 1. This reindexing preserves all entries and sums, including m = 0. |
| 156–158 | Non-increasing rearrangement; composition dominance inherited from partitions | Base.lean:20–21 and 33; Controls.lean:3–7 proves permutation and non-increasing sortedness for every m and every f. |
| 160–162 | Concatenation, first A coordinates followed by B coordinates | Base.lean:36 uses Fin.append. Bridges.lean:84–86 proves its ofFn list is the corresponding list append after sorting. |
| 164–166 | All A,a,B,b with A ≥ B ≥ 0 and a ≥ b ≥ 0 | Base.lean:40–43 quantifies ∀ A a B b : ℕ, B ≤ A → b ≤ a → …, with no positivity or strictness restrictions. |
| 165 | Injection from Uᴬ_b × Uᴮ_a to Uᴬ_a × Uᴮ_b | Base.lean:42 uses exactly this domain and codomain, with Function.Injective. |
| 165–166 | For every domain pair, its concatenation dominates the image's concatenation | Base.lean:43 places the domain concatenation first in Dom. DomL first argument has larger prefix sums. This is the source orientation. |
| 164–166 (negated) | Conjecture 1.5 is false | Endpoint.lean:4 proves not_conjecture15 : ¬ Conjecture15 by specializing the universal quantifiers to 3,20,2,19. |

The source PDF's Conjecture 1.5, rather than the sign typo in the later Theorem 3.1 discussion, controls the orientation. The control in Controls.lean uses the same definitions. No narrower parameter range replaces the literal universal conjecture. No claim is made about fidelity to an unread journal version.
