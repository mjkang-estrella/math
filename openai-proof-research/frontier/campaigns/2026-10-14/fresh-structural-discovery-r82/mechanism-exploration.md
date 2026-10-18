# Pre-freeze mechanism exploration: whole-block parameter stratification

**CLOSED PRE-FREEZE SCREEN: the prospective theorem is already stated and developed in Meiburg arXiv2610.10514v1, §§4 and O.10. No nominee.**

**Correction retained transparently:** §2 below originally misidentified ord_U Norm(U+q') as ell minus the number of distinct roots. Parent caught this before freeze: it instead counts the total algebraic multiplicity of repeated roots. For q=(X-a)^2(X-b), the order is2, while ell minus the number of distinct roots is1. Thus the original branch-stability argument as written is incomplete. Individual higher derivative norms also do not fix this: q=X^3-X has a simple root0 but q''(0)=0. A possible generic-derivative-sum repair is recorded after the original outline, but not developed into a proof after exact primary overlap closed the target.

This file records an author proof attempt before any scope freeze. It is not an assembled theorem, review, or nominee. Source141 operations are stipulated. The full prospective fixed-number-of-real-blocks CH target is unchanged. The constructions below need complete quantitative and primary comparison checks.

## 1. Abstraction to propagate

A truth predicate P(a,y) has a controlled stratifier if there is a uniformly controlled short-index family S_i(a,y) such that P is locally constant on every set with a fixed zero/nonzero status for every S_i. The number of polynomials may be exponential, but the index tuple and variable tuple are polynomial length. A quantifier-free Boolean formula has this property using its atom polynomials. Signs cannot change locally when their zero/nonzero status is fixed.

Set H(a,y,T)=product_i(T+S_i(a,y)^2). Order at T=0 equals the number of zero S_i. On a fixed-order piece, zero/nonzero status of every S_i is locally constant (initially nonzero entries persist, and the fixed count prohibits a new nonzero entry). If h_d is the first nonzero coefficient, the closed lift

W_d(a,y,t)=(h_d(a,y)t-1)^2+sum_{j<d}h_j(a,y)^2

realizes that piece. For fixed a, P and its complement give clopen subsets of W_d=0. Source proposition candidate-coordinates, now retaining a as polynomial parameters, yields coordinate polynomials P_{d,i,j}(a,T), where j is a w-coefficient index. If any true point exists in this fiber, a true point has every coordinate among roots of suitable nonzero P_{d,i,j}(a,T). The identical assertion holds for false points. Soundness is automatic when candidate grid points are checked against W_d and the original predicate. Families include all d and j tuples, whose total encoding length is polynomial.

## 2. A finite grid can be made locally stable

For a coordinate polynomial p_i(a,T)=sum_k c_ik(a) T^k, include all coefficients c_ik in the new outer stratifier. Within a fixed zero-pattern stratum its actual degree m_i and zero-polynomial status are constant. Ignore candidate tuples containing a zero polynomial or a nonzero constant. For each possible positive-degree tuple m_i, the leading coefficients b_i=c_i,m_i are nonzero on the relevant stratum.

Scale roots by X_i=b_i y_i. The monic polynomial

q_i(a,X_i)=X_i^m_i+sum_{k<m_i} c_ik(a)b_i(a)^(m_i-1-k)X_i^k

is b_i^(m_i-1)p_i(a,X_i/b_i). Choose one common short degree bound ell≥all m_i, and pad q_i by X_i^(ell-m_i). The padded q_i are monic degree ell and fit the source pure-power quotient rule. Padding adds only zero roots; filter them by the original p_i constraints, or include these among the grid tests. No division is used in defining q_i.

Include in the outer stratifier the coefficients in U of the univariate quotient characteristic polynomial Norm(U+q_i'). Its U-order at0 equals sum_over_distinct_roots(multiplicity-1)=ell-number_of_distinct_roots(q_i). Therefore fixed zero status of these coefficients fixes the number of distinct complex roots. Locally at a parameter point, disjoint small disks about the roots retain their total multiplicities. Fixed total number of distinct roots means every disk contains exactly one distinct root; roots and their multiplicities therefore vary continuously. Real roots stay real: a nonreal split of one real root would increase the number of distinct roots in its disk. This must be formalized for arbitrary relative parameter subsets, without assuming path connectedness or smoothness.

The tensor product of these univariate quotients is again a source pure-power quotient, with polynomially many variables and common exponent ell. Its multiplication spectrum is the finite grid of complex root tuples, each weighted by the product of coordinate multiplicities, including at nonreduced fibers.

For every lower stratum polynomial g(a,y,t), and each filter p_i and W_d if needed, replace coordinates by X_i/b_i and clear denominators polynomially. Let B=product_i b_i and Y_i=X_i product_{h≠i}b_h. For a uniform degree bound e in the coordinate variables define

g_tilde(a,X)=sum_beta [y^beta]g(a,y) Y^beta B^(e-|beta|).

Thus g_tilde=B^e g(a,X_i/b_i) wherever all b_i≠0. This is controlled by coefficient extraction and one short-index sum. Only zero status matters; no sign-preserving denominator claim is needed.

Include all U-coefficients of Norm(U+g_tilde) in the outer stratifier. Its order at0 counts grid branches where g_tilde=0, with their positive integer multiplicity weights. Nonzero branch values persist locally. Root branch weights are fixed. Constancy of the weighted number of zeros forces every initially zero branch value to stay zero as well: any loss of such a zero would strictly decrease the weighted count and cannot be compensated by an initially nonzero branch becoming zero in a sufficiently small neighborhood. Hence every lower-test zero status is fixed along each branch. The actual real-coordinate map is continuous. The original P is locally constant along it by the assumed stratifier property. All finite grids, filters and candidate tuples are finite in number, so one neighborhood suffices at each outer parameter point.

Consequently both existential and universal projection should have a controlled outer stratifier. Construct all candidate degree/index tuples, scaled/padded systems, derivative norms and test norms uniformly, whether or not a tuple is valid at a particular parameter. Invalid tuples simply contribute surplus polynomials. Degree validity is recognized in the proof from included coefficient zero patterns. There are a fixed number of controlled operations per real block, not one per real variable.

## 3. Finite game evaluation: global root covers

A stratifier alone does not evaluate the truth. The intended second operation replaces each real move by short discrete choices that select a genuine singleton candidate. For the outer block, candidate-coordinate polynomials have integer coefficients, and source root labels apply directly. For deeper blocks, their coefficient polynomials depend on already selected algebraic prefix coordinates.

Maintain nonzero integer coordinate polynomials covering the selected prefix, with their actual leading coefficient/degree supplied or checked using CH coefficient-sign routines. Form scaled monic padded coordinate quotients for the prefix as above. Given a candidate polynomial P(prefix,T), take the multiplication norm

R(U,T)=Norm_prefix(U+P_tilde(prefix,T)),

where denominator clearing scales P by a nonzero integer. Its lowest nonzero coefficient as a polynomial in U (nonzero as a polynomial in T) is the product, with multiplicities, of all nonzero specialized P_tilde branches. Identically zero branches are discarded by the U power. If P at the actual selected prefix is nonzero, that branch is a factor, so every candidate coordinate root is a root of this single nonzero integer polynomial. The norm is monic in U and is never zero; the selected coefficient can be found or guessed and checked using coefficient sign tests. All degree and height bounds must be checked to remain short after a fixed number of blocks.

Source integer root labels then select roots of the global cover. Some labels may select more than one root, so require nonempty singleton selection explicitly. With the already unique prefix constraints, nonemptiness and failure of uniqueness are controlled existential tests; uniqueness failure is an OR over polynomially many coordinates with two distinct satisfying coordinate tuples, and can be checked using strict inequalities and a polynomial number of calls. Also require the actual P(prefix,coordinate)=0, W_d=0, and validity/nonzero degree of each conditional candidate polynomial. All are controlled equations or sign tests after finite-index interpolation if necessary.

For an existential real block, accept iff some valid singleton candidate continuation accepts. For a universal block, accept iff every valid singleton candidate continuation accepts (invalid encodings are harmless). Candidate sampling hits every nonempty true and false clopen piece, so both directions need proof. At a leaf, the original Boolean circuit/formula is evaluated at the uniquely selected tuple by controlled existential atom tests. Every discrete move has polynomial length, and a fixed number of blocks gives fixed CH depth.

## 4. Essential checks still open before freeze

- Prove the spectrum/norm multiplicity statement for possibly nonreduced tensor products, rather than silently assuming squarefreeness.
- Check coefficient selection for conditional candidate polynomials uniformly and soundness of skipping identically zero polynomials.
- Ensure parameter strata fix *all* branch-filter statuses; W_d and original candidate constraints must be accounted for.
- Give explicit short degree/norm/cutoff recurrences for one projection and one global-cover step; no bound may depend on an evaluation prime or unencoded real parameter.
- State the finite-game induction with the same prefix singleton constraints in all existential oracle tests.
- Read nearest primary controlled quantifier-elimination and real-counting constructions; generic exponential-size bounds alone do not pay the evaluator.
- No root-label polynomial with a uniform margin is claimed for arbitrary real coefficients. That naive statement is false already for P_a(t)=t-a, b0=t, by continuity at a=0 and finitely many fixed labels. Global integer covers are intended to avoid that obstacle.

## Post-outline correction, not an assembled repair

Parent independently identified the first-derivative multiplicity error during author collaboration, not an independent gate. The author first suggested all individual derivatives, then immediately corrected that suggestion because higher derivatives can vanish accidentally. A possible repair is g_j(X,Z)=sum_{s=1}^j Z^s q^(s)(X), with one independent indeterminate Z. Over C(Z), g_j(r,Z) vanishes identically exactly when the root multiplicity m exceeds j. Therefore ord_U Norm(U+g_j), interpreting its U coefficients as polynomials in Z, is sum_{m>j}m. Consecutive tails determine the number of roots of each multiplicity. All (U,Z)-coefficient tests would be included. This is only a proposed replacement interface, not a completed revised proof or nominee. No scope freeze occurred. The exact primary theorem subsequently read is stronger than the prospective full containment, so this lane does not pursue the repair as a new contribution.
