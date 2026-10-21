# Prefreeze calculations: unequal-size permanent sums and a joint polar certificate

These are feasibility calculations, not a frozen theorem, author-proof nominee, or independently reviewed result. Only the confirmed border permanent–determinant family is developed. All canonical operative files were read before this development. Primary proof comparisons and the original history section reads are recorded privately. The prospective direction was considered during those readings; no candidate statement was frozen. Nothing here assigns a correctness/contribution grade or campaign count.

## 1. The full operation being sought

For a finite list m_1,...,m_b of positive integers and pairwise disjoint matrix-variable blocks X_i, put

    P(X_1,...,X_b) = sum_i c_i per_(m_i)(X_i),     c_i in C*,
    S_3 = sum_i m_i^3.

The prospective target is a universal lower bound proportional to S_3 for unrestricted complex BORDER determinantal complexity, for all lists whose entries exceed one absolute threshold, independently of the number of blocks and the ratio max(m_i)/min(m_i). The coefficientwise approximating affine pencils may have unbounded entries and mix all blocks. The target does not assume a layered computation, separate matrix resources for different summands, equal sizes, or a bounded number of size scales.

This is an exploratory full-scope question, not a frozen assertion. An equal-size result, a one-scale result, a logarithmic-loss result, or a weighted geometric-mean bound will not be offered as its substitute. The original one-permanent cubic bound, exact complexity, fixed-budget affine ABPs, smooth initial forms, and the source's whole ambient-polar mechanism are paid inputs.

The reason to examine this target is that the source supplies smooth restrictions with degree linear and variable count quadratic in permanent size. For equal degrees their sum is smooth and directly yields an additive lower bound. Unequal sizes require paying how those restrictions interact in one pencil; declaring that separate lower bounds add would assume the desired operation.

## 2. Unlock the actual selector parameters, without claiming a new gadget

Let r>=2 and q>=0 be integers with q<=r-1. Set

    k=r+2q,   T=(q+1)(q+2)/2,
    Delta=T-k=(q^2-q+2)/2-r,
    m >= 11k-2q = 11r+20q.                         (2.1)

Assume Delta>=2. The operative proof of the source's coefficient construction works with these parameters, even though its headline chooses one particular q. Here is the exact compatibility check.

The characteristic-two coefficient polynomial has degree r. Its gradient annihilates the coefficient functional [s^q t^q u^(r-1)] on every adjugate entry. The generation proof depends only on the distinct diagonal parameters and the pencil size k, not on the particular value of q. For every degree-q monomial s^i t^j u^ell, its complement

    s^(q-i) t^(q-j) u^(r-1-ell)

has nonnegative exponents because ell<=q<=r-1. Thus degree-q forms inject into the full-adjugate zero scheme, giving length>=T. The conductor comparison, reduced-curve defect dimension estimate, fixed-boundary-frame injection into the row Hilbert scheme, and matrix-fiber bound depend on k and T exactly as in the source. They yield gradient codimension>=Delta.

Proper specialization transfers this to a nonempty open set of complex parameters. No Euler division is used before characteristic zero. A general linear subspace of vector dimension d=Delta misses the singular locus and meets the smooth locus transversely: d-1<Delta is the exact condition. Also Delta<k^2, so the Grassmannian step applies. The nonzero restriction G is a smooth projective homogeneous form of degree r in Delta variables.

Finally, the selector uses m>=11r+20q rows. Its fixed nonzero scalar is absorbed in the first row. Thus G is a fixed affine restriction of per_m. Every operation in this paragraph is an application of an already-read operative source argument, including the integral parameter family, conductor comparison, count gates and cancellation. It is not a new contribution merely because q is left variable.

A convenient exact subfamily is

    q=r-1, k=3r-2, Delta=(r-1)(r-4)/2,
    m>=31r-20, r>=5.                              (2.2)

For r=5 the dimension is 2, so this endpoint is legitimate. The numerical k>=128 in the headline smooth-projection corollary is used there to simplify scale estimates; the earlier gradient and slice arguments apply at (2.2) as just checked. This threshold improvement is a paid parameter consequence, not a nominee.

For a fixed r and input m_i, the largest permitted q in this palette is

    q_i = min(r-1, floor((m_i-11r)/20)).

Discard indices with q_i<0 or Delta_i<2, and use any 2<=d_i<=Delta_i on the others. Independent affine restrictions of the blocks, with first-row scalar adjustment for c_i, give

    P o Phi = sum_i G_i(x_i)                       (2.3)

in disjoint variable blocks, with every G_i smooth and of degree r. An unused permanent block can be made zero by setting one row to zero. All maps and scalars are fixed BEFORE a determinant approximation is selected.

## 3. Equal degree, the strongest direct paid combination

Let D=sum_i d_i and F=sum_i G_i for equal degree r. Euler's identity and projective smoothness say that grad G_i vanishes only at x_i=0. Thus grad F vanishes only at the simultaneous origin, and V(F) in P^(D-1) is smooth. The source bound gives

    bdc(P) >= bdc(F) >= (r-1)(D-1)/(4e).            (3.1)

There is no addition of independently estimated determinant sizes here: a SINGLE smooth polynomial supplies a single certificate. This proves linear growth in the number of equal-size summands and a uniform one-scale estimate using (2.2). It is already a compatible source composition.

In particular, use only blocks m_i>=31r-20 and let N_r be their number. Then

    bdc(P) >= (r-1)(N_r (r-1)(r-4)/2 -1)/(4e)     (3.2)

whenever r>=5 and N_r>=1. Optimizing r is permitted. For m_i>=228, r=floor((min selected m_i+20)/31)>=8, and the usual absolute-constant form is r^3 N_r. A bounded ratio of sizes therefore costs only an absolute constant; unrestricted scale diversity is the real issue.

Dyadic grouping gives a lower bound of order S_3 divided by the number of occupied dyadic size intervals. That is a consequence, not the full target. The next calculation uses all selected unequal degrees at once rather than stopping at this grouping loss.

## 4. A finite gradient cover for each smooth block

Now allow smooth G_i of degrees r_i>=2 in d_i>=2 variables. Write

    a_i=r_i-1, D=sum_i d_i, A=product_i a_i^(d_i),
    L=lcm(a_1,...,a_b), F=sum_i G_i.

The projective gradient map of G_i has no base point, because its partial derivatives have no simultaneous nonzero zero. It pulls back O(1) to O(a_i). It is finite: a positive-dimensional projective fiber would contain a curve on which the ample O(a_i) had degree zero. It is surjective, and its degree is a_i^(d_i-1), obtained by pulling back d_i-1 general hyperplanes. Over C it is generically separable and étale on a nonempty open set.

Consequently the affine gradient map has generic fiber of A_i=a_i^(d_i) distinct points: each projective inverse contributes exactly a_i radial solutions to grad G_i(z_i)=v_i. Equivalently, homogenizing these d_i equations gives no point at infinity, so the affine degree is the product of their degrees. Choose v_i such that this fiber Z_i is reduced and avoids G_i=0. The latter condition is possible because the image of G_i=0 under the finite gradient map has dimension d_i-1, hence is a proper closed subset of the d_i-dimensional target. Every z_i in Z_i is nonzero and has invertible Hessian, and c_i(z_i):=G_i(z_i) is nonzero.

These choices are not yet polar directions. They provide a finite model for the curve along which ALL gradients are proportional to the same scalar.

## 5. Resolve all branches with one finite cyclic cover

Consider the affine curve over C* defined by

    grad G_i(x_i)=lambda v_i    for all i, lambda!=0. (5.1)

For lambda=t^L, all its points are parametrized by

    x_i=t^(L/a_i) z_i,    z_i in Z_i, t in C*.       (5.2)

This is surjective since any lambda has an L-th root and homogeneity recovers z_i. Its identifications are exactly

    (t,(z_i)) ~ (zeta t,(zeta^(-L/a_i) z_i)), zeta^L=1.

The action on the finite tuple set Z=product Z_i is free: if a root zeta fixes a tuple, then zeta^(L/a_i)=1 for every i; gcd_i(L/a_i)=1, so zeta=1. Thus there are A/L components, each with parameter t in C*. Choosing one tuple from each orbit gives a parametrization without additional self-identification on that component. This division by L is essential; counting A tuples without it would overcount every polar point L times.

On each component,

    F(x(t)) = H_z(t) = sum_i c_i(z_i) t^(b_i),
    b_i=L r_i/(r_i-1)=L+L/a_i.                     (5.3)

All these exponents are positive integers. The curve (5.1) is smooth: its Hessian blocks remain invertible after nonzero scaling, so the equations solve locally for x as a function of lambda.

## 6. Pay genericity simultaneously, including roots and endpoints

We can choose the v_i so that every branch polynomial in (5.3) has nonzero highest and lowest coefficient and has only simple nonzero roots after removing its monomial factor, provided not all r_i are equal.

Here is a finite argument rather than an unsupported genericity assertion. Start with the good fibers Z_i above. Replace v_i by alpha_i^(a_i) v_i with alpha_i in C*. Its fiber becomes alpha_i Z_i and its values of G_i become alpha_i^(r_i)c_i(z_i). Thus each branch coefficient is a linear combination of independent nonzero parameters beta_i=alpha_i^(r_i), grouped by the distinct exponents b_i. For any fixed tuple, the map from the beta_i to the grouped coefficients is surjective, since groups are disjoint and all c_i(z_i) are nonzero.

The bad endpoint coefficients are proper hyperplanes. The discriminant condition is also proper: specialize the grouped coefficients to just the smallest and largest exponents, both nonzero. After removing t^(b_min), this is a nonconstant binomial with nonzero constant term, whose nonzero roots are all simple in characteristic zero. Hence the discriminant polynomial is not identically zero. Although this test point may set some beta_i to zero, its nonzero discriminant defines a nonempty open in affine beta-space, which meets the dense torus. There are only A finitely many tuples, so all endpoint and discriminant conditions can be avoided simultaneously. The power map alpha_i -> beta_i is surjective on C*, so these choices are attainable while preserving every gradient-fiber property.

Set a_min=min_i a_i and a_max=max_i a_i. When a_min<a_max, each component has exactly

    b_max-b_min=L(1/a_min-1/a_max)

nonzero simple zeros of F. Therefore (5.1) and F=0 have exactly

    mu=(1/a_min-1/a_max) product_i a_i^(d_i)         (6.1)

points over lambda!=0, all simple. This is a positive integer, as is also clear from the A/L component count.

To check simplicity in the needed coordinates, use the invertible Hessian blocks to eliminate x locally in (5.1). The remaining derivative is dH_z/dt, nonzero at a selected root; dt/dlambda is nonzero on C*. Thus the square (D+1)-variable system (gradient equations,F) has invertible Jacobian. Choose a coordinate of v=(v_1,...,v_b) that is nonzero and eliminate lambda using that gradient equation. The remaining D equations are exactly

    F=0, partial_(w_j) F=0, j=1,...,D-1,

where the w_j form a basis of the annihilator of the covector v. For example, if v_D!=0, take w_j=e_j-(v_j/v_D)e_D. These are CONSTANT ambient directions. Elimination preserves the invertibility of the Jacobian. Hence every selected point is a distinct simple zero of the source's ambient-polar certificate on the full affine D-space.

There is no polar certificate of this form with the same formula when all degrees coincide: b_max=b_min, H_z is a monomial, and there are no such torus zeros. That is the homogeneous scaling degeneracy, not evidence that the homogeneous source bound vanishes. Section 3 uses a projective affine chart and D-2 polars in that case.

## 7. Pass the joint certificate through arbitrary border approximation

Suppose F is in the closure of size-n affine determinants. Freeze the finite points and constant directions from section 6. Each selected simple root persists for all sufficiently close coefficient vectors, so ONE actual size-n determinant has all mu of them, still simple. This does not bound matrix entries or demand a coherent matrix-valued parameterization. At every such point the determinant matrix has corank one; the source's common kernel chart, Schur elimination, and bilinear product count apply without any change.

With h=D-1 the resulting exact inequality is

    mu <= B(n,D)
      := [H^D U^(n-1) V^(n-1)]
         (H+U)^n (H+V)^(n-1) (U+V)^(D-1)
       <= 2^(D-1) binom(2n-1,D).                  (7.1)

Consequently

    bdc(F) >= D/(4e) *
      [(1/a_min-1/a_max) product_i a_i^(d_i)]^(1/D). (7.2)

Combining independent fixed selector restrictions with affine monotonicity gives exactly the same inequality for P whenever r_i,q_i,k_i,d_i satisfy section 2 in the corresponding permanent blocks. Restricting to any subcollection is allowed by zeroing unused blocks. Each c_i in the original P is absorbed by a fixed nonzero row scaling, so it does not create an extra hypothesis. Fixed determinant sizes, total degree ceilings, and all affine substitutions remain in the correct order.

This is a concrete joint construction, stronger information than simply taking the maximum of independently stated block bounds. It is nevertheless built from the already-paid ambient certificate and finite gradient-cover algebra. No substantial-contribution claim is inferred from its absence in the headline statements.

## 8. Weighted initial forms: a compatible robustness operation

The same certificate applies whenever F is a weighted initial form. Choose positive integer weights w_i constant on each block such that w_i r_i=R, for example R=lcm(r_i), w_i=R/r_i. If g=F+E and every monomial of E has weight strictly greater than R, then

    t^(-R) g(t^(w_1)x_1,...,t^(w_b)x_b) -> F as t->0.

If every error weight is strictly less than R, use t->infinity instead. For each fixed t!=0 this is an affine substitution followed by a scalar. The closure of fixed-size determinants is closed, so the same size contains the limit. Thus (7.2), or section 3 in the equal-degree case, transfers to g.

This is a paid affine-degeneration operation. It does not handle an error with both higher and lower weights, nor arbitrary perturbations of the same weight. For an ordinary coefficientwise sufficiently small perturbation, finite simple-root persistence gives a neighborhood obstruction for each fixed n, but no uniform numerical radius has been obtained. Such a neighborhood is not a new quantitative robustness theorem by assertion.

## 9. Carry the exact binomial comparison further: a scale-loss diagnostic

The joint count remains a geometric mean. To locate the obstruction precisely, define the weak cubic size quantity

    W = sup_(s>0) s^3 #{i:m_i>=s}.                  (9.1)

Even grant every input block the generous choices

    1<=a_i<=m_i, 0<=d_i<=m_i^2,

and allow arbitrary subcollections. These include all selector choices above. For t>0,

    sum_(a_i>=t) d_i
      <= sum_(m_i>=t) m_i^2
      = t^2 N(t) + integral_t^infinity 2s N(s) ds
      <= 3W/t.                                    (9.2)

Endpoint conventions at the finitely many sizes do not affect the integral. Let D=sum d_i>0 and t0=3W/D. Using log(a/t0)<=max(0,log(a/t0)), integrate the tail:

    (1/D) sum_i d_i log a_i
      <= log t0 + integral_t0^infinity
                      [sum_(a_i>=t)d_i]/(D t) dt
      <= log(3W/D)+1.

Therefore

    D product_i a_i^(d_i/D) <= 3e W.              (9.3)

For mixed degrees, the prefactor 1/a_min-1/a_max is at most one, so the displayed lower-bound expression (7.2) is at most 3W/4. This alone would not rule out a much sharper inversion of the exact coefficient B. We therefore check that coefficient too.

Expanding B(n,D), choose H exponents j and D-j in the first two factors. The required U exponent in (U+V)^(D-1) is j-1, giving the positive term

    binom(n,j) binom(n-1,D-j) binom(D-1,j-1).       (9.4)

For D>=2 choose 1<=j<=D-1. If n>=D+1, the elementary product bound binom(N,k)>=(N/k)^k gives

    B(n,D) >= ((n-1)/D)^D.                        (9.5)

In fact (9.5) follows by replacing both denominators j,D-j by D and discarding the last factor. With

    n0 = ceil(D product_i a_i^(d_i/D)) + 1,

we have n0>=D+1 and B(n0,D)>=product_i a_i^(d_i)>=mu. Thus the exact inequality (7.1) cannot rule out n0, and

    n0 <= 3eW+2.                                  (9.6)

So retaining the exact coefficient instead of its exponential upper estimate does not recover the missing sum over scales for this certificate. This is a statement about THIS count comparison, not about actual determinantal complexity or all polar methods.

The equal-degree certificate has E=D-1, mu=r(r-1)^(D-2). Its root is at most r. The same positive-term argument (or j=1 when E=1, where B(n,1)=n) makes its exact comparison compatible with n<=ceil(Er)+1. Since r<=m_i on every used block,

    rD <= r sum_(m_i>=r) m_i^2 <=3W,

so its exact comparison also cannot exceed a constant multiple of W. Optimizing degrees, dimensions, and subcollections within these constructions does not alter this conclusion.

## 10. An explicit list with an arbitrarily large missing factor

Fix an integer M0>=228 and J>=0. For j=0,...,J take 8^j blocks of size

    m_j=M0*2^(J-j).

Each tier has exactly the same cubic mass

    8^j m_j^3 = C0:=M0^3*8^J.

Thus S_3=(J+1)C0. The maximum in (9.1) occurs at one of these block sizes, and at m_j

    m_j^3 sum_(ell=0)^j 8^ell
      = C0 (8-8^(-j))/7 <= (8/7)C0.

Also W>=C0. Hence S_3/W grows linearly with the number of tiers. Sections 3 and 7, including exact binomial inversion and arbitrary subcollections, give at most a constant times C0 from their certificate budgets. They do not establish a universal constant times (J+1)C0.

Conversely, section 3 on any single tier already gives a constant times C0. So the scale-loss diagnosis is matched on this explicit list: it is not an artifact of discarding a useful factor in the final Stirling inequality. No assertion about an upper bound on the true bdc(P) follows.

## 11. Test the strongest alternative compatible operation

The primary layered-ABP reduction does more than compare isolated gradients. It repeatedly cuts a narrow middle layer, subtracts products P_j Q_j with P_j(0)=Q_j(0)=0, preserves vertex size, and reduces depth by a constant factor. A robust singular-locus calculation tolerates the accumulated product errors once the formal degree is controlled. This is a genuine paid size-budget operation and must be included in the comparison.

It does not presently finish the full target for arbitrary affine determinant pencils. The source converts ABPs TO determinants at almost linear vertex cost, not arbitrary determinants TO layered ABPs of the same size. A linearization that introduces states for successive homogeneous components charges the degree and does not preserve the matrix-size budget needed for an additive cubic determinant bound. Likewise the ordinary geometric count can be applied separately at multiple scales, but those separate inequalities all spend the SAME n. They do not certify disjoint subspaces or separate resource payments inside one pencil.

Ordinary homogenization does not silently synchronize the block degrees. If R=max r_i, the fixed homogeneous completion is H(x,z)=sum_i z^(R-r_i)G_i(x_i). Whenever R-r_i>=2, the entire x_i-coordinate block is contained in the gradient-zero set at z=0 with all other blocks zero: every x_i derivative retains a factor z, every other block derivative vanishes at its origin, and the z derivative still retains z (the remaining summands vanish at their origins). Thus the completion is not a smooth form in all D+1 variables. This observation only invalidates an immediate use of the smooth-form theorem; it does not rule out more elaborate polar or conormal counts of H. Taking an ordinary initial form retains the largest degree, and weighted initial forms in section 8 retain the unequal-degree sum rather than creating a smooth common-degree form. None of these paid affine degenerations provides the missing additive charge.

A concrete local issue is visible in Schur elimination. At a selected corank-one point,

    A=[[a,beta],[gamma,E]],
    S=a-beta E^(-1) gamma,
    grad det A = (det E) grad S on S=0.

Even though the target F splits into variable blocks, E and E^(-1) in an arbitrary approximating pencil need not split. Blockwise derivatives contain

    partial_i partial_j S
      = terms involving (partial_i E) E^(-1) (partial_j E)

as well as beta/gamma terms. The vanishing of mixed derivatives of the limiting F does not force the matrix coefficients into independently chargeable invariant blocks; cancellation and the varying Schur scalar remain. Removing one scale's polar contribution therefore has no constructed smaller pencil representing the remaining scales. The earlier original realization history likewise preserves the distinction between an actual tree/layer construction and uncharged shared computation.

The precise unpaid operation is a simultaneous resource argument for an arbitrary mixed affine determinant approximation that accumulates the cubic charges of all tiers (or a different full-scope construction with such an accumulation). The gradient-cover computation and the explicit tail bound above isolate what the present certificate does and does not pay. They are not an impossibility claim and do not replace the target with a named circuit conjecture.

## 12. Status

No full theorem asserting the additive cubic target has been frozen. The exact selector palette, the mixed-degree polar count with cyclic quotient and simplicity, its fixed-budget border transfer, weighted-initial-form compatibility, and the exact-coefficient scale-loss diagnostic are retained as durable prefreeze calculations. No equal-size or geometric-mean consequence is nominated as the remaining substantial result. The gap is the accumulated resource payment across arbitrarily many size scales. No worldwide-priority, exhaustive-clearance, correctness, contribution, acceptance or count claim is made.
