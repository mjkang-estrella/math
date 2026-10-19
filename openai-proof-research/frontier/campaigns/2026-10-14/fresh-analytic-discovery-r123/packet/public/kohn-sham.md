# Source278: symmetry, local forms and the full paid endgame

This is preselection feasibility work. No theorem scope was frozen, no full proof is submitted for review, and no contribution classification is assigned. The main question tested was whether replacing the source's global `L^(3/2)+L^infinity` potential condition by a uniform local integrability condition leaves a genuinely new operation. No approximation-rate or generalized Friedrichs-representation target from r29/r84 is reopened.

## The actual source is much stronger than its representation headline

The pinned manuscript is *A Coulomb Ground State Density without Kohn–Sham Ensemble Representation*, September25,2026. Exact file paths, raw URLs, Git blobs and reading extents appear in the registers. Its `04-ensemble.tex` already handles arbitrary three-electron spin ensembles, including an infinite ensemble in a degenerate ground space. The Pauli inequality `0<=gamma<=I`, trace3, the rank-two ground spin space and the weighted gap give the determinant comparison. For an admissible representing potential, infinitesimal form boundedness provides finite kinetic energy before the orbital variation. The singly occupied down-spin sector then identifies the representing potential with `V=Delta g/(2g)` up to a constant. `07-functional-consequence.tex` already obtains the empty subdifferential consequence. None of these is a fresh corollary.

In `03-angle-spectrum.tex`, `prop:angle-minimizer` minimizes the weighted angle energy over odd angles with `integral n sin²(theta)=1`. Every folded minimum has `0<theta<pi/2` above the plane, a positive multiplier d, and the common orbital equations for `g=sqrt(n)cos(theta)` and `h=sqrt(n)sin(theta)`. `prop:angle-convergence` is uniform over all folded choices, and `prop:weighted-gap` applies to every folded minimum at the stated sufficiently large D/small coupling scope. Its full even/odd proof, including exterior loss of weighted mass, was inspected. The exact-charge parameter-selection section was not freshly read; no uniform numerical charge estimate is asserted.

The source's `05-plane-obstruction.tex` is the operative comparator. It already uses:

* the exact normalized plane translate `n(p omega+x)/(A(p)/p)^2 -> a² z² exp(-2k omega·x)` and the polynomially suppressed but positive plane trace;
* translated orbital compactness, nonnegative ground-state exclusion on the nodal plane, and the other orbital to identify the limiting potential;
* positivity of theta on the whole plane z=1, followed by the global weighted negative-part test proving `theta>=m>0` on z>=1;
* the bounded delta equation with a strictly positive linear lower bound, all sequences with diverging height, and the global `epsilon sqrt(1+|x|²)` maximum argument;
* all remaining escaping centers via bounded shifts, not just a chosen plane subsequence;
* local **uniform quadratic-form** convergence, the fixed quadratic partition, and the subsequent Agmon/trace contradiction.

The target constant is `c_infinity=d+k²/2`. Weak-star convergence of the bounded part alone is not passed directly through moving quadratic tests: the source proves compactness of their squares in L1. Its theorem is already for the stipulated density properties and positive gap, and its molecule realization covers all sufficiently large permitted integer charges after fixing the source separation. It is not just one numerical counterexample.

## Correction: axial density does not by itself imply axial angle

Initial feasibility used axiality of V too quickly. Reading the actual angle proposition and the strip proof found explicit warnings that theta need not be assumed axisymmetric. This was corrected in commentary before any freeze. No assertion that source278 itself proves angle symmetry is made.

The strongest compatible preprocessing uses the classical convexity operation, not averaging theta. For a folded theta put q=sin²(theta), extending q evenly across the plane. The exact energy is

    integral n |grad theta|²
      = (1/4) integral n [ |grad q|²/q + |grad q|²/(1-q) ].

Here `0<q<1` off the plane, q has zero trace on the plane, and `integral n q=1`. The two summands are quadratic perspectives. For two minima q1,q2, their convex combination retains the exact linear constraint and evenness. Reconstruct the odd angle by `arcsin sqrt(q)` on the upper half-space. The pointwise perspective inequality controls its energy; local approximation, or the square-root norm formula for the two sine components, handles the zero trace without asserting that arcsin-sqrt is globally Lipschitz.

This is the square-root convexity calculation in [Benguria–Brezis–Lieb, CMP79(1981), Lemma4, pp170–171](https://sites.math.rutgers.edu/~brezis/PUBlications/92-journal.pdf), read in the original journal scan. Their full functional is strictly convex also because of its other terms; strictness for this constrained angle problem is not imported from their theorem without checking equality.

For that equality check, the midpoint cannot have lower energy than a minimum. The nonnegative pointwise deficits in both perspective terms therefore vanish. Positivity in the connected upper half-space makes equality in the first Cauchy–Schwarz inequality give

    grad log q1 = grad log q2.

Thus q2=c q1 there. Their identical upper-half weighted mass (1/2) forces c=1. Local positivity justifies the logarithms; no uniform lower bound at infinity is used. Consequently two folded minima coincide, and rotating one around the symmetry axis of n returns the same minimum. The equations then make g,h and V axial. This is a feasibility certificate for the required symmetry, using the classical compatible convexity/equality operation. It is not a fresh uniqueness nomination or a claim that the source asserted it verbatim.

This calculation followed the initial local-form idea and the explicit nonassertion in the source. The BBL primary read was later still, before any freeze. Those times are not backdated.

## Two-dimensional compactness for arbitrary tests

Fix a finite q>1. Suppose, for the purpose of testing the reduction, that the axial formal V has bounded L^q norms on all fixed-size physical balls whose horizontal radii tend to infinity. No smallness, equiintegrability, pointwise bound or derivative of V is assumed. Constants may depend on the fixed q, the bound, the fixed density and its d,k; nothing is uniform as q decreases to1, coupling tends to zero or the nuclear geometry varies.

At a center of horizontal radius p_j tending to infinity use coordinates

    Phi_j(s,t,z)=((p_j+s)cos(t/p_j),(p_j+s)sin(t/p_j),z_j+z).

On each fixed box the metric tends smoothly to Euclidean, the Jacobian is `1+s/p_j`, and the axial multiplier F_j(s,z) is independent of t. Fixed finitely many physical balls cover the box. Integration over a fixed t interval therefore bounds F_j in L^q of the meridional rectangle. Subsequencing gives weak L^q limits there. The shrinking angular aperture is not a demand for an entire expanding annulus estimate.

For an **arbitrary**, possibly azimuth-dependent H1 test u supported in the box, set

    w(s,z)=(integral |u(s,t,z)|² dt)^(1/2).

Cauchy–Schwarz gives `|grad_(s,z) w|² <= integral |grad_(s,z)u|²dt` in the weak sense. Thus w stays in a bounded H1 set in two dimensions. The Jacobian can be included as the smooth factor `1+s/p_j` in the multiplier; its uniform bounds cause no loss. Rellich compactness gives precompactness of w² in L^(q') for every fixed finite q'=q/(q-1). Weak L^q convergence of F_j is consequently uniform over these quadratic tests. This is the exact replacement for the source's L-infinity/L1-square compactness operation. It does not restrict the original tests to symmetric functions.

The same two-dimensional interpolation bound gives, for every epsilon>0,

    integral |F_j| |u|² <= epsilon ||grad u||² + C_epsilon ||u||²

uniformly on such boxes. The constants depend on q and the uniform L^q bound. Near the physical axis this argument is not asserted; the final localization uses the exterior of a cylinder instead.

Last–Simon, *The Essential Spectrum of Schrödinger, Jacobi, and CMV Operators*, author-hosted April12,2005 version, [Theorem4.2/Proposition4.4](https://math.caltech.edu/papers/bsimon/p304.pdf), was checked at its actual form/resolvent and Fourier-cutoff proof. It supplies a strong general comparison through uniform local Kato/form control, not a license to treat bare critical three-dimensional L^(3/2) as compact. Its uniform Kato modulus is a real hypothesis. Here symmetry provides the lower effective dimension that makes every fixed q>1 subcritical. The source itself already contains the local-form-to-exterior argument, so a new essential-spectrum theorem is unnecessary.

## Checking that the whole endgame remains compatible

The normalized axial orbitals satisfy two-dimensional equations with radial drift `(p_j+s)^(-1) partial_s`, tending to zero on fixed boxes. The density bounds give local boundedness of the orbitals. Caccioppoli and the preceding form bound give local H1 control; subcritical potential estimates provide local compactness/positivity in the plane-limit step. The formal bounded-potential lemma cannot simply be cited for this changed class without these estimates. This round has not written a standalone all-hypotheses proof of that enlarged lemma or independently reviewed it.

After that replacement, the source's angle equation has exactly the same coefficient convergence and bounded-angle estimates: it needs local uniform convergence of normalized n, not derivatives of V. The positive lower angle on z=1, the integrable-weight cutoff argument, the bounded-delta maximum principle and the identification of `c_infinity` at diverging heights are the **same operations**. For horizontal radius tending to infinity, height either has a bounded convergent subsequence or tends to one of the two infinities. The cylindrical coordinate argument covers both, even if height grows much faster than horizontal radius.

One obtains the contemplated uniform local form limit for centers far from the axis; the source fixed partition sums it to an exterior-**cylinder** form estimate. This suffices for the same contradiction. Use an inner cutoff depending on horizontal radius p and the truncated weight `a min(p,T)`, with

    k < a < sqrt(k²+2d).

Its gradient has norm at most a. The cutoff error is in a fixed horizontal-radius strip and is bounded by the global L2 norm of g, even though that strip is unbounded in z. Outer spatial cutoffs justify testing before removal. Thus the Agmon step would give exponential p-weighted H1 control outside the cylinder. The trace on z=0 contradicts the source's exact exponential rate k with only polynomial suppression. There is no need to prove a new estimate on the infinite axis cylinder or replace the full conclusion by a special sequence of radii.

This is the full compatible reduction that the screen tests. The global source operations, classical occupation convexity and effective-dimensional Sobolev compactness fit together; no further unpaid operation has been identified. A stronger integrability headline alone would not establish contribution. Because no eligible candidate was selected, this is not presented as a completed full theorem or independent correctness PASS.

## Endpoint and representation limits

The q=1 endpoint is not obtained by writing q'=infinity. Two-dimensional H1 does not compactly embed there. More specifically, bounded local L1 permits sheet concentrations that are invisible in the limiting odd orbital's equation on its nodal plane. On a fixed meridional rectangle, the elementary model

    F_epsilon(s,z)=-a epsilon^(-1) chi(z/epsilon)

with smooth compactly supported nonnegative chi has bounded L1 norm and tends as a measure to `-a(integral chi) delta_{z=0}`. Its quadratic form on a smooth test with nonzero trace does not disappear. This is only a diagnostic for an endpoint limit argument, not a construction of the actual source potential, a counterexample to an enlarged Kohn–Sham theorem, or a nominee. No sheet-sign control or quantitative ridge asymptotic for the source minimum was proved. The full old r29 global barrier-rate question is not solved by this model.

Nor does exclusion of a particular formal potential automatically exclude ground ensembles for every proposed enlarged potential class. The source potential-identification proof first obtains finite ensemble kinetic energy from the **original** class's form bound. An arbitrary signed uniformly local critical potential can require a different realization/domain argument. The axial formal-potential calculation and a general representing potential must not be conflated. No generalized-operator or enlarged-class representation theorem is asserted here.

## Actual earlier work

Actual r29 `screen-278.md` already proves the qualitative blowup of gauge-fixed admissible representing potentials along approximating densities by closedness of the convex subgradient graph. It explicitly does not give a rate. Its local `g_epsilon=epsilon exp(-kx)cosh(sqrt(2d)z)` model has positive d and constant V, showing that local density ridge data alone do not force potential blowup. The source's global angle/trace chain, retained above, is essential. This model is not a refutation of the source.

Actual r84 `form-domain.md` constructs the weighted ground-transform closure and arbitrary spin-ensemble comparison for the generalized Friedrichs realization. That is a stronger old interface than merely observing that V is locally integrable. It was read before final disposition and is not repackaged here. Its external Gori-Giorgi/Gál/Baerends and inverse-periodic primary bodies were not freshly read in r123; their described results remain credited historical comparisons, not new primary clearance.
