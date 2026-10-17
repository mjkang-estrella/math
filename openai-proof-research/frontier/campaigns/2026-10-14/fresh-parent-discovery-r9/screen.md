# Family329: a single compact-operator consequence, technical only

This is a pre-freeze screen, not a new substantial nominee. No acceptance or independent proof verdict is claimed. Myeongjin Kang, no affiliation; original prose CC BY4.0, original code MIT. Source truth is stipulated at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.

## Exact consequence and why it is not nominated

There are separable reflexive real Banach spaces E,F and one compact operator T:E→F such that for every a,b≥1 and every ε0>0 there is 0<ε<ε0 with

    log N(T(B_E), ε B_F) > b log N(T*(B_F*), (ε/a) B_E*).

All covering centers are arbitrary ambient centers. Thus even constants depending on this single operator cannot give the upper entropy-duality comparison at all sufficiently small scales. Reflexivity alone does not fix the comparison. The added operation below is ordinary lacunary finite-block assembly. The stronger quantifier order and reflexive realization do not themselves make this a substantial new operation; no formal/manuscript/contribution gates are requested for it.

## Finite input with arbitrarily large entropy

Read source329 introduction, full matrix-to-body lemma/proof, and complete final parameter argument, not just the catalogue headline. For each a,b≥1 its proof gives a finite-dimensional identity T_j:(R^n,||·||_K)→(R^n,||·||_∞), with ||T_j||≤4, and numbers m,Q satisfying

    N(T_j(B), B_∞)≥m,
    N(T_j*(B_1), a^(-1) K°)≤Q²,
    log Q² < log m/(2b).

The norm bound follows directly from K=3 absconv{R_x}+θ B_∞, entries R_x in [0,1], and θ=1/(1000a). Its proof chooses h,r,u,C before the prime p; then m=p^(D_h). Keeping those first parameters fixed and enlarging p preserves the strict ratio bounds and makes log m arbitrarily large. This last freedom, already explicit in the actual parameter proof, pays every finite head cost below. The finite identity/adjoint correspondence is the support-function calculation already in the source.

## Complete block argument

Choose c_1>0. Inductively, after blocks i<j and c_j are fixed, let H_j be the finite logarithm of a cover at radius c_j/(3j) for the adjoint of the finite head diag(c_i T_i)_{i<j}, acting between the finite ℓ2 sums. Its image is compact; take H_1=0. Apply the preceding source construction with a=3j and b=4j, choosing p still larger so that log m_j>8j H_j. It gives

    log Q_j² < log m_j/(8j).

After this block is fixed choose 0<c_(j+1)≤c_j/(48j). Let E=(⊕E_j)_2, F=(⊕F_j)_2 and T=diag(c_jT_j). These countable sums of finite-dimensional spaces are separable and reflexive. Because ||T_j||≤4 and c_j→0, T is a norm limit of its finite-rank truncations and is compact. Its adjoint is diag(c_jT_j*) between the corresponding dual ℓ2 sums.

At ε_j=c_j, projection to block j maps any ε_j-cover of T(B_E) to such a cover of c_jT_j(B_Ej). Hence its cardinality is at least m_j. In the source, the separated row points actually have distance at least 3 before scaling, so there is no boundary ambiguity.

For T*, the head has a c_j/(3j)-cover of size exp(H_j); the current block has such a cover of size Q_j². Every future block has operator norm at most 4c_(j+1)≤c_j/(12j), so the entire ℓ2 tail image of the unit ball is in one ball of that radius. Product centers for the first two parts, followed by zero on the tail, give covering error at most

    c_j/(3j)+c_j/(3j)+c_j/(12j)=3c_j/(4j)<c_j/j.

The unit ball of the full sum projects into each of the relevant unit balls; no assertion that it equals their Cartesian product is needed. Thus

    log N(T*(B_F*), (c_j/j)B_E*)
      ≤ H_j+log Q_j² < log m_j/(4j).

Given fixed a,b, take any sufficiently large integer j≥max(a,b). Increasing the adjoint cover radius from c_j/j to c_j/a only decreases its size; multiplication by b≤j gives a quantity strictly below log m_j, itself at most the primal entropy. Since c_j→0 there are arbitrarily small such scales. This proves the displayed consequence.

If desired, a compact square-zero operator on the single reflexive space E⊕₂F is S(x,y)=(0,Tx). Coordinate projection/inclusion shows its image-cover counts and those of its adjoint equal the corresponding T/T* counts. This is another routine packaging, not a second result.

## Limits and next distinction

The argument proves neither failure of a particular Lorentz entropy ideal to be invariant under adjoints nor a prescribed power-law entropy profile. A bad comparison at isolated radii does not control the integral of the whole entropy profile. The finite source construction does not provide those missing upper/lower profile bounds. Nor is a uniformly convex or B-convex realization asserted. Those stronger questions are not frozen targets here.

The source's own asymptotic finite-dimensional ratio and separation from convexified packing are already printed consequences, not discoveries in this screen. The operation just proved is fully reduced to its norm-bounded finite witnesses, the available prime enlargement, finite head covers and classical ℓ2 sums. It is therefore retained as technical support and not counted toward 10/10.
