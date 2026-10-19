# Geometric interfaces inspected before selection

No statement was frozen in these screens. Calculations below are feasibility diagnostics and comparisons, not proposed findings or independent contribution ratings.

## 091: scalar dilation is paid; anisotropic dilation has an actual counterexample

The pinned source's `cor:measure` gives the log-Brunn–Minkowski inequality for every even log-concave measure, including measures supported on a proper linear subspace. Its proof already supplies the support-restriction/Wulff inclusion, the same-dimensional transfer, and the full scalar B-property t -> mu(e^t K). The last step is the exact support-function identity for scalar dilation. The source variance section already combines its two Cauchy–Schwarz inequalities through the same tensor and the same q. Neither a singular support nor a differently written scalar-dilation conclusion is an unpaid operation.

The stronger anisotropic claim must not be inferred from this scalar result. Cordero-Erausquin–Rotem, [Several results regarding the (B)-conjecture, author manuscript](https://webusers.imj-prg.fr/~dario.cordero/Docs/articles/B-note-gafa.pdf), Theorem6, constructs Gaussian covariance matrices arbitrarily close to the identity and symmetric convex bodies for which the multivariable diagonal-dilation mass is not log-concave. Theorem6 and the whole accompanying Fact8/proof were read, rather than relying on the abstract. The author's PDF contains unresolved citation placeholders; no dated journal-version identification is asserted.

The actual mechanism uses P with 2-by-2 block ((1,2 eta),(eta,1)), conjugates a diagonal generator by P, and uses thin rectangles to make the restricted standard Gaussian tend to a one-dimensional Gaussian. The resulting second logarithmic derivative is positive. Thus a small perturbation of a Gaussian covariance does not supply a full anisotropic B-property. This is an existing primary counterexample, not an original candidate or a refutation of the stipulated source. The source concerns a different interpolation.

## 336: the parameter direction has a stronger historical antecedent

The higher-dimensional source's `thm:main` assumes -4 Delta+Scal >=1 and gives one dimension-only bound for the diameters of entire fibers of an (n-2)-dimensional simplicial map on every connected complete smooth boundaryless n-manifold, n>=4. Its `pre:supersolution` supplies w=-2 log v. Its actual `pre:reserve` accepts arbitrary smooth w on a complete metric h and produces h+ >=h and t+ with

    D_1(h+,t+) >= D_1(h,w)+(t+)^2-C(n),
    D_beta(h,t)=Scal_h+2 Delta_h t-beta |dt|_h^2.

The graph/pressure setup is operative input; it is not merely an existence slogan. The full reserve proof was not freshly read, so no improvement of that proof is asserted.

Before selection, the actual I14 sharp-spectral-width body was inspected. It already treats the three-dimensional coefficient interval 4<=a<6 using beta=4/a, the weighted surface transfer and the coefficient c_beta=(3 beta-2)/(2 beta-1); it also contains the higher-dimensional warped-model endpoint observation. A new coefficient-only headline would therefore ignore a stronger old antecedent. The three-dimensional companion's positive-weight and weighted stability setup were checked at their actual proof bodies.

For n>=4, the displayed reserve does not automatically become the same statement for beta<1. Substitution introduces

    (1-beta)(|dt+|_(h+)^2-|dw|_h^2),

whose sign is uncontrolled by the stated contract. Even h+>=h compares the norms of the SAME covector, not these two different functions. A general higher-dimensional coefficient extension would need an appropriately compatible reserve or a different complete geometric construction. None was derived here, and the unchanged source coefficient was not renamed as a candidate. This identifies a limit of this attempted reduction; it does not prove that a wider coefficient theorem is impossible.

## 365: rank bookkeeping and the conformal-potential gauge

The source `thm:main` recovers a metric and rank-two unitary connection from a boundary patch. The matrix section contains the finite jet spanning operation, projected first-order system, `mat:finite-type`, improvement and local dilation argument. The finite-type statement itself accepts an arbitrary finite-dimensional real target V. Thus merely replacing the displayed matrix projection by q_r(Z)=Z-(Re tr Z)/r I, or writing more frame columns, does not identify a new structural operation. The remaining global bundle/frame interfaces were not completely checked for arbitrary rank, and no rank-r theorem is submitted.

Adding an unknown scalar potential changes a different, exact step. The source `glob:conformal` uses harmonic frames to compare first-order coefficients. It obtains C2=C1-d phi I and, because the original operators have no added potential, Delta(phi)+|d phi|^2=0. Hence exp(phi) is harmonic and equals 1 on the known side; unique continuation removes the conformal factor. This operative proof was read completely.

For comparison, the classical conformal identity already shows why literal simultaneous uniqueness cannot simply be carried to an added potential. In dimension n>=3, let c>0 be smooth and equal to 1 near the boundary, and put

    g_tilde=c^(4/(n-2)) g,
    Q_tilde=c^(-4/(n-2))(Q-c^(-1) Delta_g c).

For scalar functions, with Delta=div grad,

    (-Delta_g_tilde+Q_tilde)(c^(-1)u)
      =c^(-(n+2)/(n-2))(-Delta_g+Q)u.

This follows by applying the conformal Laplacian formula and differentiating c^(-1)u; the mixed gradient terms cancel. Multiplying by the identity gives the same diagnostic for a trivial unitary bundle. Since c=1 on a whole boundary collar, traces and normal derivatives agree there. Dirichlet invertibility is transported by the displayed invertible conjugation. On a Euclidean ball, a nonconstant c with Delta c nonzero gives nonflat scalar curvature somewhere, so the changed metric need not be isometric to the original. The potential absorbs the exact scalar equation used by `glob:conformal`.

This is a familiar gauge calculation, not a new result. It does not refute the source's potential-free theorem, and it does not settle an inverse theorem formulated modulo the enlarged gauge. Such a quotient theorem would require further complete comparisons that were not supplied here. No potential-added or rank-modified target was frozen.
