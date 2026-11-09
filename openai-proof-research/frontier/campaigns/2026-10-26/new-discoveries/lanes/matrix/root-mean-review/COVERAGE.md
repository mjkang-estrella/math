# Formal coverage of336466

All6modules frozen2026-10-26. `build/verified/audit.json` independently recopies/recompiles every declaration using pinned Lean4.34.1 and locked mathlib, with warningAsError. PASS50declarations; observed foundational axioms onlypropext,Classical.choice,Quot.sound.

- RootNewton: Newton identities evaluated on arbitrary complex multisets, finite antidiagonal reindexing, Vieta's coefficient bridge including indices above degree, monic root power-sum recurrence.
- MomentPolynomials: binomial polynomials and their evaluations at naturals, normalized Newton-moment polynomials, degree≤i−1, their zero-parameter values, and equality of evaluated moment polynomials with actual root multiset power sums for every indexi (includingi>numberofroots).
- AppellRoots: coefficient and degree formulas, monicity, ordinary and iterated polynomial derivatives, exact derivative-root multiset equality, polynomial evaluation and root-sum expansions.
- MeanPolynomial: continuation of the actual source mean at each positive degree parameter; degree≤D−1; cancellation at the artificial zero parameter foroddD; zero atD because evaluation occurs on the polynomial's own roots. The artificial parameter is explicitly not assigned a constant-polynomial root average.
- OddMeanIdentity: full finite-difference sum and reindexing; source `derivativeRootMean` defined as the sum of evaluations over the actual iterated-derivative root multiset divided by D−r; identity for every coefficient familya witha0=1; interval endpoint deletion justified explicitly.
- SourceIdentity: arbitrary complex polynomial coefficient normalization, exact representation by a nonzero-leading-coefficient multiple of an Appell family, mean scaling, and `source_conjecture_336466` for arbitraryp:ℂ[X] assuming onlyOddp.natDegree.

The source denominator is the natural degree minusr, cast toℂ. Everyr in the final sum satisfies0<r<D, so it is positive/nonzero. The root polynomial has degreeD−r, proved through the Appell derivative identity and scaling; complex algebraic closure supplies all root slots with multiplicity. The proof includesD=1 (empty interval) and repeated or nonreal roots. It does not rely on numerical root finding, positivity, distinct roots, or user-supplied moment/source bridges.

No classification of all mean relations or claimed two-dimensional odd-degree relation space is formalized. No numerical validation is used as a theorem dependency. The independent exact rational trace experiment is supplementary only.
