# Finite-grid bridge for the fractional-binomial candidate

This is a supporting lemma, with no separate discovery credit. For positive integers j and l and a decreasing real function φ on [0,1],

    Σ(r=1..j) φ(r/j) + Σ(s=1..l) φ(s/l) ≤ Σ(t=1..j+l) φ(t/(j+l)).

Set L(r)=r+floor(lr/j) and R(s)=s+floor((js−1)/l). The two maps are injective, their images are disjoint and partition {1,…,j+l}, and

    j L(r) ≤ (j+l)r,     l R(s) < (j+l)s.

The integer statements are proved in the independently authored GridRanks.lean. Thus L(r)/(j+l) ≤ r/j and R(s)/(j+l) ≤ s/l. Apply monotonicity in reverse order and sum over the partition. GridMajorization.lean proves the real comparison and unconditional assembly.

The relevant derivative kernel is φ(t)=1/(x+i+t)² for x>0 and i≥0. Applying the grid inequality to each block in Euler’s finite Gamma approximants proves convexity of the scaled Gamma quotient logarithm. Passage to the pointwise limit preserves convexity. This avoids assuming the classical log-convexity result as an unproved formal hypothesis.
