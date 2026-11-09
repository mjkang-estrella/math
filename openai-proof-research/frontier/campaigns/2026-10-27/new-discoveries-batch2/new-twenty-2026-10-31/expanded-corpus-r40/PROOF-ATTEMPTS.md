# r40 mathematical attempts (zero accepted credit)

## 347712: exact Latin-strategy refutation at n=5

Primary manuscript 2008.11448, Definitions 2–3 and Section 7.2, Conjecture 3, actually read. A strategy is a partition of S_n into n labelled parts. For a part C_h, magneticity of position i for target k is the cardinality of {σ∈C_h:σ(i)=k}; intensity is the maximum over positions. Field is the sum of intensities over h,k. Optimality means maximum field, not merely asymptotic order. Latin strategies use a Latin-square row with maximum agreements; arbitrary tie choices are expressly allowed in the paragraph preceding the conjecture. The published Wiley URL returned403; no retry. Web-indexed publisher text agrees, but this is not an independently downloaded published-body audit.

For n=5, take the cyclic square A_hi=h+i mod5, and assign each permutation to its first maximum-agreement row. The class sizes are 46,26,21,16,11. Direct enumeration of all120 permutations gives intensities [18,18,18,18,18], [13,13,13,13,13], [11,11,11,11,11], [9,9,9,9,9], [7,7,7,7,7], hence field290. A second square has rows

    4 0 3 2 1
    3 2 4 1 0
    1 4 2 0 3
    2 1 0 3 4
    0 3 1 4 2.

The same first-maximum rule gives class sizes33,27,25,20,15 and intensity sums76,67,63,53,43, totaling302. Consequently the cyclic strategy is Latin but not optimal, refuting the universal biconditional. It is unnecessary to determine the exact optimum or to prove that the second square is Latin. Formal source definitions use actual Equiv.Perm(Fin n), full-universe filtered cardinalities, finite maxima and both universal optimality and Latin selection predicates. This is neither a surrogate score-only theorem nor a bounded conjecture asserted as an all-n proof. A counterexample at5 suffices to refute the universal assertion.

Remaining qualification gates: bounded prior-art screen has not demonstrated worldwide novelty; independent fidelity/significance review is essential, especially given the elementary finite nature and the authors' asymptotic context. Exact finite optimality is their Definition3, but this interpretation deserves adversarial review. No acceptance requested by this lane.

## 347913: full ordinary convexity mechanism

Source 2009.04510 Eq(2), complete L-uniform edge family E, simplex definitions and Section3 Conjecture1 read. Published SIAM copy retrieved separately. Polak2104.08264 Theorem1.1 and Section2 Procedure2.1 actually inspected: it proves only L=2,d≤9 through coefficient-Hessian PSD and symmetry reduction, not arbitrary d,L.

Let T_v, v∈[n], be independent exponential(rate1) variables, and Z_e=min_{v∈e}T_v. For any ordered d-tuple e=(e_1,...,e_d), expand

 E[∏ Z_ei] = ∫_[0,∞)^d exp(-∑_v max({t_i:v∈e_i}∪{0})) dt.

This follows from the layer-cake identity for each nonnegative factor and Tonelli. Partition the integration region by the d! total orders of t_i; ties have measure zero, even when edges repeat (the integration coordinates remain labelled). On the chamber t_{π1}≥...≥t_{πd}≥0 set u_j=t_{πj}-t_{π(j+1)}, t_{π(d+1)}=0. Then ∑_v max_i t_i = ∑_{j=1}^d |e_{π1}∪...∪e_{πj}|u_j. The triangular substitution has determinant1, and integrating each u_j gives the product of reciprocal union sizes. Thus

 E[∏ Z_ei] = ∑_{π∈S_d} ∏_{j=1}^d 1/|e_{π1}∪...∪e_{πj}|.

Multiply by ∏x_ei and sum over all labelled tuples. Relabelling tuples separately for each π yields

    E[(∑_{e∈E} x_e Z_e)^d] = d! f_d(x).

Every moment is finite: each Z_e≤T_v for any chosen v∈e, and the finite sum is bounded by a constant times ∑T_v for fixed x. For nonnegative x,y and θ∈[0,1], the inner linear forms are nonnegative and t↦t^d is convex there. Apply that scalar convexity pointwise and take expectations. This proves the literal convexity claim, indeed on the full nonnegative orthant. No source scope widening is needed: specialize to its simplex.

Exact rational diagnostics independently implement ordered-exponential spacings and source tuple denominators, comparing n=3,d=3 and n=4,d=3,4 at unequal positive weights. All agree. These checks are diagnostics, not proof certificates.

Formal gap: a literal Lean endpoint requires a certified joint survival/layer-cake expansion, chamber decomposition with repeated edge labels, product integration and relabelling, integrability, and convexity integration. None of these semantic bridges is discharged by the diagnostic. No dummy moment predicate is offered. Alternate finite order-statistic expansion turns the moment into a finite average of complete homogeneous polynomials in nonnegative linear forms, but monomial positivity alone does NOT imply convexity: the moment representation is still needed. Material novelty gaps include full contemporary citing literature and the currently changed Omega proof tree. HOLD, zero credit.

## 348265: routine generating-function bridge, no new credit

Source Sections1,9 and Eq(41) and corresponding published author PDF read. Put H(t,x)=N(t,x)/(1-t-t²-xt³-x(x+1)t⁵), as in Eq(41). Every coefficient is nonnegative. A denominator monomial of x-degree b and t-degree a has a≥5b/2 (the x²t⁵ term attains equality); numerator monomials all satisfy a≥(5b-4)/2. Products retain the latter bound, so a term x^n t^m requires m≥ceil((5n-4)/2). Attainment: for n=2r+1 use numerator xt and r copies x²t⁵, obtaining t^(5r+1)x^(2r+1); for n=2r+2 use numerator x²t³ and r copies x²t⁵, obtaining t^(5r+3)x^(2r+2). This exactly gives the claimed threshold for n≥1, using the source's explicit identification of coefficient support with hypercube subgraphs. This is a direct support calculation from a supplied full generating function, hence a routine consequence under campaign rules. No formalization or credit. The earlier arbitrary-dilation encoding is a different notion of embedding; the conjecture's cube-polynomial paragraph explicitly concerns subgraphs.

## 347711 and 348181

347711 shares the actual primary Definitions2–3 and Section7.1. A dual formulation maximizes ∑_{σ∈S_n} max_h #{k:σ(i_h(k))=k} over m response maps i_h:[n]→[n]. This is maximum coverage with graded match utilities; individual set-function submodularity does not prove concavity of its optimized cardinality profile. The n=5 Latin comparison does not disprove concavity in m. No unproved submodularity-to-concavity bridge is asserted.

348181 primary Conjecture4.21 and preceding Lemmas4.16–4.20 proofs read. Source partial induction isolates the difficult appended-coefficient subcase; monotonicity in the principal root after appending a positive coefficient is not enough because λ_L decreases with L. A bounded root sweep would not resolve incompleteness, whose definition quantifies over all positive integers. No numerical root shortcut or endpoint/domain correction is claimed.
