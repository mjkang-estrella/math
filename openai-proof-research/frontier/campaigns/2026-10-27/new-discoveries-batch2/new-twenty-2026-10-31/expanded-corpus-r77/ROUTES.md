# Mathematical routes and limits

This is a partial investigation, not a completed campaign pass. All computations below are unformalized diagnostics. No result is nominated for credit.

## 340094: equivariant Fishburn bijection

The actual source is Chen–Yan–Zhou, arXiv1808.04191. Its Conjecture1.1 has five conditions. Theorem3.8 proves only the four statistic conditions, and Remark3.2 explicitly records failure of inversion equivariance for their constructed map (permutation85231647). Thus the abstract does **not** exclude the full literal problem. This corrects the initial tentative assessment during this investigation.

Fix the source's bivincular pattern: a forbidden triple has positions i,i+1,j with j>i+1 and pi_i+1=pi_j<pi_(i+1). A Fishburn matrix is upper triangular, nonnegative integral, weight n, with no empty row or column. Its involution is reflection in the NE diagonal, (i,j)->(d-1-j,d-1-i). Four statistics are first-row sum, last-column sum, number of weak NE extreme nonzero cells, number of occupied diagonal cells.

Inversion swaps LRmax with RLmin and fixes RLmax and LRmin. NE reflection has the same action on the four matrix statistics. For finite sets with involutions and compatible statistic maps, an equivariant statistic-preserving bijection exists precisely when (a) total fiber cardinalities agree, and (b) fixed-point fiber cardinalities agree in invariant fibers. Proof: match the fixed points; then match remaining two-element orbits within invariant fibers, and match orbits crossing pairs of swapped fibers. Conversely any equivariant bijection preserves those counts. This reduces the unresolved fifth condition to a refined involution enumeration once the four-statistic equidistribution theorem is used.

The exact search enumerates every permutation and every upper-triangular composition of n in every dimension1..n. Both distributions agree through n6; n7 is logged separately. This does not prove the uniform fixed-point identity. A new route needs a generating series for pattern-avoiding involutions refined by the four statistics and a matching series for NE-symmetric Fishburn matrices. Merely modifying the published map without controlling inversion does not close the gap. Later journal body and exhaustive citing literature remain unread. No author-catalogue novelty clearance is claimed.

## 331759: multiply-union families

Read actual definitions and Theorems1,2 in arXiv1511.03828v2. The ambient naturals include zero. Tuple repetitions are allowed. The downward closure of an r-wise s-union family is again r-wise s-union: choose a dominating original vector for each selected downward vector and compare their coordinatewise joins. Cardinality cannot decrease, so an extremal family is downward closed. Coordinate permutations preserve the property.

The candidate K is tested literally: x belongs to its i-th layer iff sum_j max(0,x_j-a_j-i)<=d-(n-r+1)i. This is equivalent to membership in the downward closure of the corresponding exact-weight sphere: the excess above its base must fit the available nonnegative increments, with unused increments placed arbitrarily. The search includes every family inside weight<=s, adding a vector only when every newly created r-tuple (including repetitions) passes the join test. Hence no valid family is pruned by the compatibility condition. All balanced-coordinate permutations are included for the equality test.

The first parameter grid is fully exhausted, including the cases outside the source's n=r+1 theorem; precise rows are in search-union.json. The n4,s4 extension is capped at2000 recursion nodes for each r2,3 and is incomplete. A prior larger extension hit its CPU cap before producing a durable checkpoint; it contributes **no** coverage. The retained smaller rerun records its lexicographic prefix, best sizes and lack of counterexample.

Theorem2 uses additional coordinate-maximum conditions to identify a containing polytope. Those conditions are not implied by downclosure alone. Closing that implication or finding a family violating the proposed classification while still r-wise union is the main remaining step. The asymptotic theorem cannot supply a uniform finite-n classification. No full solution found.

## 400138: incidence deficit and finite projective planes

Primary arXiv1507.04080 Conjecture1.2 has numerator q^3-q^2+2q-2 in the i=2q-1 clause, whereas the raw MathDB line has q^3+q^2-2q+2. A counterexample to that discrepancy is an excluded transcription correction.

For d distinct projective lines, each unordered pair meets in exactly one singular point, so sum_P m_P(m_P-1)=d(d-1). Consequently H=(d-sum_P m_P)/s. This identity is exact over arbitrary fields. The total-incidence bound is the substantive optimization; plugging a prescribed multiplicity list into the identity is insufficient because the list must be geometrically realizable. Likewise a lower bound restricted to subconfigurations of one finite plane is insufficient for H(d), which minimizes over every field and arrangement.

All subsets of PG(2,2) and PG(2,3) were enumerated with exact rational H values. These small examples are in the authors' already computed d<=31 range; they cannot be new outcomes. The full-plane d=q^2+q+1 case is already in the source. The route needs a sharp incidence deficit for deleted-line ranges over **all** realizable arrangements, beyond the source's square-root lower bound. No such gap was proved.

## 381131: recurrence diagnostic quarantined

The later source arXiv1506.06238 Lemma1 states stabilization at exactly i+j+1. Its Table1 has q1=x-x^2+x^3/3 and q2 coefficient of x^2 equal3. The copied Proposition1 recurrence script initialized from q1 instead produces coefficient2 at q2. Therefore the implementation/printed recurrence requires reconciliation with the density transition; all script violations are quarantined and cannot support a mathematical refutation. The literal >=3k zero threshold also contradicts the authors' own k1 x^3 coefficient1/3. That endpoint discrepancy is an excluded formulation defect, not a significant new result. A corrected intended staircase proof would need the density transition itself and later-publication comparison.

## 380929: full ordinary identity, routine and uncredited

Let C(t)=sum_{j>=1} c_j t^j and P_k(z)=[t^k] exp(z C(t)), working over any commutative Q-algebra. Expanding each factor exp(z c_j t^j) gives exactly the source sum over J with sum j J_j=k and coefficient product c_j^{J_j}/J_j! times z^{sum J_j}. Coefficient extraction from exp(lambda C)exp(mu C)=exp((lambda+mu)C) gives sum_i P_i(lambda)P_(k-i)(mu)=P_k(lambda+mu).

A direct finite proof avoids formal-series prerequisites: reindex a term on the left by J=A+B. For each fixed J, its total contribution is product_j c_j^{J_j} times product_j sum_{a=0}^{J_j} lambda^a mu^(J_j-a)/(a!(J_j-a)!). The ordinary binomial theorem makes the j-th sum (lambda+mu)^{J_j}/J_j!, yielding the literal right side. The outer source index i is uniquely sum_j j A_j. This is a routine multinomial/binomial-type identity; no novelty or campaign credit is claimed. Symbolic checks k0..10 are only implementation sanity checks. No Lean packet was pursued for an excluded routine identity.
