# Source and formal correspondence

## 6. Formal statement and correspondence

The Lean namespace is ContactPilot. SourceContact defines the contact predicates independently of the example. HasZeroSetContact includes unit norms of the boundary coordinates, the boundary numerator zero, positive delta,rho,c,C, and for every punctured nearby circle parameter: a lower bound for every local numerator zero in the disk and an upper witness among those zeros. HasHalfPlaneContact has the analogous lower-half-plane clauses. These are two-sided infimum comparisons with an explicit nonempty witness.

ReducedCertificate f stores a numerator and nonzero denominator, common-divisor reduction, stability, representation of beta composed with f composed with betaInv, bidegree support bounds, a phase of norm one and the reflection identity. This prevents arbitrary factors or unrelated analytic branches from entering the contact assertion. NearestWDistance requires a w-reaching walk of length d and says every such walk has length at least d; it assigns no fictitious distance to an empty reachable colour class.

The universal definition SourceConjecture literally quantifies all n, simple graphs G on Fin n, Boolean colourings isZ, roots i, certificates cert for graphFunction G isZ i, and natural d,K. Its conclusion is

    NearestWDistance G isZ i d -> 0<K -> Even K ->
    HasZeroSetContact (eval2 cert.numerator) (-1) 1 K -> K=2*d.

These contact-existence hypotheses weaken the informal universal claim, so their negation still refutes it. The witness graph is connected, with both colours present and a z root, although the definition need not settle degenerate source conventions. The endpoint is ContactPilot.refutation : not ContactPilot.SourceConjecture.

Correspondence table (declaration - source meaning):

    resolventMatrix, graphFunction - A minus colour diagonal; inverse entry
    beta, betaInv                - upper-half-plane / disk coordinate maps
    ReducedCertificate          - actual reduced rational-inner representation
    reflect                     - coefficient reflection in bounded bidegree
    HasZeroSetContact           - local bidisk zero-set infimum comparison
    HasHalfPlaneContact         - lower-half-plane zero-set comparison
    NearestWDistance            - shortest root-to-w walk length
    SourceConjecture            - universal nearest-w prediction of [1, 6.1]

The analytic chain is QuadraticBranches -> ExactOrders -> SecondBranch -> BranchBounds -> HalfPlane. It constructs analytic branches by a local inverse, extracts analytic remainders, proves analyticOrderAt exactly 6 and 2, then bounds every root and a witness. GraphResolvent ties N/Q to the matrix. Coprimality proves reduction in C[Z,W]. CayleyPolynomials, BidiskReduced, BidiskStable, BidiskDegrees, BidiskReflection and BidiskCertificate supply the reduced global certificate. RootLocalization through CircleChart prove the uniform coordinate transfer. BidiskContact proves contact six; ContactExclusion excludes two; Refutation applies the universal statement to d=1,K=6 and derives a contradiction.

