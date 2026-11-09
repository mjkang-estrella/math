# Statement correspondence

The primary source is P. Alexandersson and F. Getachew Kebede, *An involution
on derangements preserving excedances and right-to-left minima*, Australasian
Journal of Combinatorics 86(3) (2023), 387–413, Conjecture 5.2.1.
Read-only cached text: `../expanded-corpus-r204/sources/ajc/ajc_v86_p387.txt`,
lines 1654–1668. Its literal wording is:

> Let k be a fixed positive integer such that 2 ≤ k ≤ n. Then
> (−1)^(n−1) Σ_{π∈S_n, min(type(π))≥k} (−1)^inv(π)
> x_RLMv(π) y_EXCv(π), where type(π), the cycle type of π, is an element
> in N[x_1, …, x_n, y_1, …, y_n].

The displayed formula is transcribed from the extracted PDF's rearranged lines.
The next sentence says the case k = 2 follows from Theorem 1.0.1 and the
conjecture is not true for k = 1.

MathDB 350721 follows arXiv v3, `sources/tex/2105.08455/main.tex`, lines
2032–2040:

> Let k be a fixed positive integer such that 1 ≤ k ≤ n. Then
> Σ_{π∈S_n, min(type(π))≥k} (−1)^inv(π) x_RLMv(π) y_EXCv(π),
> where type(π) is the cycle type of π, is an element in N[x_1, …, x_n,
> y_1, …, y_n].

The MathDB text is also preserved in the candidate's raw record; this lane
uses the review's verified identification, and makes no new live-source claim.
Versions 1 and 2 have a different malformed conjecture with k absent from
the sum; neither is represented by the two propositions here.

| Source symbol | Lean definition |
| --- | --- |
| S_n | `Equiv.Perm (Fin n)` |
| inv | `invCount`, card of ordered inverted index pairs |
| EXCv | `excv`, values v whose inverse position is smaller than v |
| RLMv | `rlmv`, values smaller than every value at a later inverse position |
| x_R y_E | `term`, product of X over R with `Sum.inl` and E with `Sum.inr` |
| type, including 1-cycles | `pi.partition.parts` |
| min(type) ≥ k | `cycleGe`, every part at least k |
| sum without prefactor | `rawSum` |
| prefactored sum | `F` |
| membership in N[variables] | `InNat`, existence of an ℕ polynomial mapping to the ℤ polynomial |
| refereed conjecture | `VoRConj` |
| MathDB / v3 conjecture | `MathDBConj` |

Positions and values both shift down by one. This is an order-preserving
bijection, preserving all comparisons in the source definitions. Variable
`Sum.inl i` is x_(i+1), and `Sum.inr i` is y_(i+1). Inverse-position
formulations are obtained by substituting j = π⁻¹(v). The value sets contain
no repetitions because π is a bijection. The empty product is 1.

Both propositions universally quantify natural n and k with precisely their
respective lower bounds; no assumption is replaced by coefficient positivity.
`InNat.coeff_nonneg` proves the one direction of the literal map membership
needed for contradiction. No sign homomorphism is used.

At n = 9 and k = 3, `m9` is x_{1,5,7,8} y_{2,3,4,6,9}. Its raw coefficient
is −1. Since (−1)^8 = 1, its normalized coefficient is also −1. This witnesses
both negations inside the refereed range and does not exploit the v3 sign error.
