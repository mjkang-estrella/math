# Exact formal-Smith interface and remaining strata

Let C(Y) be the actual 4x4 digit-polynomial matrix of degree at most k-1, with positive digits <=L, and choose B as in r56. Every coefficient of each 2x2 minor has absolute value <=2kL^2<B; every coefficient of each 3x3 minor has absolute value <=6k^2L^3<B. If f(Y) is any of these nonzero minors, with first nonzero coefficient at degree v, then

    v_B(f(B))=v.

Indeed f(B)=B^v(a_v+B a_(v+1)+...), and 0<|a_v|<B, so the parenthesis is not divisible by B. For an identically zero minor both orders are infinite. This proves an EXACT identity of the B-adic orders of the two determinantal ideals with the Y-adic orders over Q[[Y]]. It is not merely a one-way implication for the first k coefficients.

Every entry of C(Y) has positive constant coefficient below B. Thus its first Smith invariant is a unit both over Z_B and over Q[[Y]]. If the formal Smith valuations are 0<=a2<=a3<=a4 (allowing infinity), the second and third B-adic invariant valuations of C(B) equal a2 and a3, by subtraction of the determinantal-ideal valuations whenever finite, and by the usual rank convention when infinite. Reducing modulo B^k caps each invariant separately. Consequently

    D E = B^(min(a2,k)+min(a3,k)).                    (S)

This statement includes the nonunit-second-pivot strata and exact-rank-one/two matrices. The existence of Smith form is elementary over each discrete valuation ring; for Q[[Y]] no integrality of the change-of-basis matrices is asserted. Applying a formal change of basis to the coefficient box would lose its integer/residue geometry.

Equation (S) identifies precisely the remaining counting problem: average this capped valuation weight over the prescribed independent digit sets. The unit-second-pivot estimate in moment-attempt.md is only the a2=0 stratum. It cannot establish the full DE moment.

One must not replace (S) by a single truncated-minor condition without retaining separate caps. For example an exact formal rank-two matrix can have a2=0,a3=infinity and hence DE=B^k, although all 3x3 minors vanish to every order. Counting it with weight B^(2k) solely because those minors vanish to order 2k overweights it by B^k. This invalidates a shortcut reducing all nonunit strata to an unconditional rank-two jet count at order 2k.

The source-style nine-entry conditioning does bound Pr(a2>=b)<= (L/r)^(-9b) for 1<=b<=k. It fixes the bottom 3x3 block after conditioning on the first row and column; a unit first entry is always present. But replacing E by its deterministic bound h yields only

    E[DE 1_(D>1)] <= h * O(sum_(b=1)^k B^b (L/r)^(-9b)).

Even when the ratio B(L/r)^(-9) contracts, the prefactor h=B^k loses the needed hierarchy. A joint estimate in a2,a3, with the actual caps in (S), is still necessary.

For homogeneous zero residues, write C(Y)=r Z(Y). As r is a unit in Q[[Y]] and modulo B, it does not change any formal or B-adic Smith valuation. The entries of Z have coefficients in [Q], Q=L/r. Thus homogeneous residue classes reduce exactly to the unconditioned integer-polynomial count at side length Q, while the valuation weight is still B~_k L^4~_k r^4 Q^4. Discarding that r^4 in the weight would silently change the problem. The positive tangent example in moment-attempt.md shows the corresponding per-step loss concretely; it does not decide the weighted average over whole histories.

## Lower-rank geometric obligations remain unchanged

The new formal identification does not supply FD4 or the auxiliary weighted singular-matrix estimate. In rank three, exceptional null vectors modulo q still require a joint divisor/normal count. In rank at most two, a single primitive null vector does not parametrize the matrix, so the source's three-dimensional proof cannot be copied. Pairwise distinct projected columns do not remove these configurations. No algebraic valuation identity makes them negligible at the intended sample size.

No estimate in this note is offered as a substitute for the full tetrahedral target.
