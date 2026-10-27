# Sokal Conjecture3.3: a short prospective argument

Credit0. No formal source endpoint, independent review, or completed novelty
assessment. Eligibility is particularly uncertain because this short argument
combines already proved source facts. Do not count it as a discovery merely
because the MathDB label remains open.

Source: Sokal, arXiv1804.04498v3, Conjecture3.3 p14, MathDB338918. Set
e_n=E_n/n! for the Euler zigzag numbers (sec+tan exponential generating
function). The exact target is, for n≥0 and j,k≥1,

    (-1)^(n-1)(e_n e_{n+j+k}−e_{n+j}e_{n+k})>0.

Normalize a_n=e_n/[2(2/π)^{n+1}]. The exponential factor cancels from every
comparison. Source (1.6) gives a_n→1. Source Proposition3.2 gives strict
log-concavity of b_m=a_{2m}; (3.8) gives strict log-convexity of c_m=a_{2m+1}.
All terms are positive.

An elementary lemma: a positive strictly log-concave sequence tending to1 is
strictly increasing and less than1. Its consecutive ratios strictly decrease;
any ratio≤1 would force all later ratios≤r<1 and the sequence to0. Thus every
ratio>1, and convergence gives every term<1. Reversing inequalities gives that
a positive strictly log-convex sequence tending to1 is strictly decreasing and
greater than1. Therefore b strictly increases below1 and c strictly decreases
above1.

If j,k are even, the desired determinant sign follows directly from strict
log-concavity of b or strict log-convexity of c (consecutive-ratio products give
arbitrary positive shifts). If j,k are odd, for even n the outside factors are
both<1 and the inside factors both>1, so the determinant is negative; for odd
n the reverse holds. If j is even and k odd, compare

    a_n/a_{n+j}  with  a_{n+k}/a_{n+j+k}.

For even n the first ratio<1 (increasing b) and the second>1 (decreasing c),
giving a negative determinant. For odd n the first>1 and the second<1, giving
a positive determinant. Interchange j,k for the remaining mixed case.

This includes n0 (source Proposition3.2 and the asymptotic apply to it) and
j1/k1. `check_euler.py` independently constructs E_n from the exact defining
recurrence and verifies 127500 integer cross-multiplied instances covering all
eight parity types. This numerical verification is not the proof above.

Prior-art work remains incomplete. The exact source's 12 OpenAlex-indexed
citers were retrieved by the correct ID W2798014112 (an initial wrong-ID query
was overwritten and not used). Three primary citing bodies were downloaded:
Han1906.00103, Pan2408.12865, and toric-manifolds2407.11313; the latter cites
only Proposition3.2 in Lemma7.4. No entire-corpus or global priority conclusion.
