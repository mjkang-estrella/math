# I283 — The ball–slab asymptotic is not uniform at the ball–tube transition

Parent analytic check, 2026-10-12. **TECHNICAL boundary observation, not an accepted finding.** This preserves the fixed-R scope of R018. No independent review, new substantiality claim or count increment is asserted.

## Exact elementary bound

Use the unit cubic torus and R018's functional

    L_R(epsilon)=inf{P(E)+P(F)-4pi R^2-2:
                     E subset F a.e., |E|=4pi R^3/3,
                     |F|=2(R-epsilon)}.

For R<=1/3 sufficiently close to 1/3 and epsilon>0 sufficiently small, put

    rho(R)=sqrt(4R^3/3),
    g(R)=2pi rho(R)-4pi R^2
        =4pi R^(3/2)(1/sqrt(3)-sqrt(R)).

Then

    0 <= L_R(epsilon) <= g(R),
    g(R)/(1/3-R) -> 2pi/3 as R increases to 1/3.

Indeed, choose F to be the coordinate slab |z|<R-epsilon and E to be the solid radius-rho(R) tube about the x-axis. Its volume is pi rho(R)^2=4pi R^3/3 and its perimeter is 2pi rho(R). Because rho(1/3)=2/9<1/3, the strict inequality rho(R)<R-epsilon holds throughout a neighborhood of (R,epsilon)=(1/3,0). Thus the tube lies in the slab with a positive gap. Both are embedded in the torus, and their exact volumes have the required values.

The lower bound follows from the stipulated scalar profile: at R<=1/3 the inner scalar minimum is 4piR^2; for these outer volumes it is 2. The upper bound follows by inserting the explicit pair. Rationalizing gives

    g(R)/(1/3-R)=4pi R^(3/2)/(1/sqrt(3)+sqrt(R)),

whose limit is 2pi/3. At R=1/3, the two scalar inner equality classes coexist and the constructed nested pair gives L_(1/3)(epsilon)=0 for every sufficiently small positive epsilon.

Consequently, for any R_epsilon<1/3 satisfying

    delta_epsilon=1/3-R_epsilon=o(epsilon^2/|log epsilon|),

the normalized quantity |log epsilon|L_(R_epsilon)(epsilon)/epsilon^2 tends to zero. It cannot converge uniformly to R018's fixed-R coefficient 2pi as R approaches this endpoint. More generally, if delta_epsilon |log epsilon|/epsilon^2 tends to a finite lambda>=0, the explicit pair gives limsup at most (2pi/3)lambda.

These are exact analytic estimates, not numerical evidence. They use only one explicit competitor and the stipulated scalar theorem.

## A possible crossover is not a new theorem here

The ball-shaped recovery in I275 has constants that can be chosen uniformly in a sufficiently small compact radius interval ending at 1/3: its free patches retain positive separation, its local spherical chart and volume derivatives stay nonsingular, and its area estimates require only these bounds. Together with the cylinder competitor this suggests the upper envelope

    limsup |log epsilon|L_(R_epsilon)(epsilon)/epsilon^2
       <= min{2pi,(2pi/3)lambda}.

An equality or morphology-selection theorem is **not claimed or independently reviewed** in this record. R018's fixed-radius lower bound may not simply be substituted with a moving R: limiting scalar minimizers at the endpoint include cylinders as well as balls. A complete lower passage must separate those classes, prove uniform local stability/graph control on the cylinder branch, and use the singular ball-contact argument on the other branch. The nominal crossing lambda=3 comes only from comparing these two costs until that work is supplied.

Even a completed minimum-of-two-branches theorem would need a separate contribution judgment. Standard compactness, local stability and comparison of two already-paid mechanisms may make it only a technical extension. This record is useful as an endpoint counterexample and a guard against overclaiming, not as progress in the accepted-finding count.

## Source and read boundary

The actual pinned source is [family 354, Theorem intro:main](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/build/paper.tex). The retained entry-file lines 48–100 were read, including the full scalar theorem, both equality cases at volume 4pi/81 and the complement clause. Its SHA256 is `ab75095f542adf4073a41a26a3c3ae97be7b55fa19674ec4fb4c288f7145a813`. No upstream proof audit was performed.

R018's full I275 proof and I277 reconstruction Sections 1–5 were consulted for the fixed-radius scope and upper construction. A bounded web search returned Milman's [slab-isoperimetry paper](https://arxiv.org/abs/2403.06602) and other scalar phase-transition literature. Only search abstracts were inspected in this check, so no theorem or novelty conclusion is inferred from those results. The exact competitor and endpoint limit above are derived here. No comprehensive prior-art screen is claimed.
