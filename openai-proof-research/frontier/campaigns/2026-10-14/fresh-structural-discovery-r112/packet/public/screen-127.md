# 127: the product-space operation is paid, and already screened

Pre-freeze exclusion, not a candidate. A later targeted history search located `fresh-arithmetic-discovery-r49/working127.md`, which explicitly excludes the same arbitrary-product resampling consequence. Its heterogeneous-bias influence target remains outside this round.

The pinned source's `01-introduction.tex`, `thm:main`, gives I(g)≤8d√m on the uniform m-cube, including zeros. Its **complete** `06-consequences.tex`, `cor:noise-sensitivity`, already proves NS_flip,η(g)≤8√2 d√η by random buckets, and supplies the associated uniform-marginal learning theorem. DRST [0909.5011v2](https://arxiv.org/pdf/0909.5011v2), Theorem7.1 and full §7.1, gives the underlying bucketing identity (14).

The stronger relevant comparator is Blais–O'Donnell–Wimmer, *Polynomial regression under arbitrary product distributions*, retained March2009 author PDF, [§3 Theorem3.2 proof and §4](https://cs.uwaterloo.ca/~eblais/assets/pdf/polynomial_regression.pdf). It already supplies the independent-pair/Boolean-selector transfer. Here is an explicit convention-safe verification for polynomial thresholds; it avoids confusing Boolean bit flips with replacement by a fresh sample.

Let μ=product_i μ_i be any finite-dimensional product of Borel probability measures on R, with no moment, atom, or bias assumptions, and f=sgn P for a real polynomial of total degree at most d. Draw U,V independently from μ and a uniform sign vector z. Put

    X_i(z)=(U_i+V_i)/2 + (U_i−V_i)z_i/2,
    g_(U,V)(z)=f(X(z)).

The substituted polynomial has degree at most d; cube multilinearization only lowers it and preserves zeros. If d exceeds the cube dimension, use its actual degree or the trivial influence bound. Flip each selector independently with probability t≤1/2. A flipped coordinate replaces the selected sample by the other, independent sample. An unflipped coordinate is unchanged. Conditional on the flip mask, pairs from different coordinates remain independent and each selected first sample has marginal μ_i. Thus the resulting pair (X,Y) has exactly the product **resampling** law at rate t. Averaging the source flip-noise bound gives

    Pr[f(X)≠f(Y)] ≤ 8√2 d√t,  0<t≤1/2.

For t>1/2 the same displayed constant follows from probability≤1 for d≥1. Constants have zero noise sensitivity. This is a complete compatibility calculation; no Gaussian invariance principle or density approximation is needed. Equivalently one can combine the selectors with the source buckets in one affine substitution.

The operation is already present in the primary proof, and r49 already records its applicability here. It neither closes the different square-root-weighted heterogeneous influence sum nor supplies its missing weighted trace/grading identity. We record the successful reduction to prevent another misleading nominee, not as a new substantial theorem or a contribution rating.
