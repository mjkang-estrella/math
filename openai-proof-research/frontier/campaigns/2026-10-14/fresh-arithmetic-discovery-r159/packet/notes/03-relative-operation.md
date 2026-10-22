# Uniform near-critical tails: strongest combined reduction and exact unpaid interface

PREFREEZE, no nominee. This is one developed quantitative operation on Source060's full positive-b2 minimal class-VII family, not a strengthened GSS claim, a conditional nominee, or a restricted replacement for an old target. Notes 00–02 establish the actual source/primary mechanisms before these deductions.

## Full feasibility specification, not frozen theorem bytes

Take any proper holomorphic submersion p:X->B over a complex ball, with every fiber connected, compact, minimal, b1=1, kappa=-infinity and common b2=b>0. Choose its fiberwise universal cyclic cover Y->X, the generator f towards the pseudoconcave end, and a locally constant lift u of one standard negative basis class. Choose a smooth family of Hermitian metrics on X and a smooth height on Y with h(fy)=h(y)-1. Let E be the flat family of fundamental divisors supplied by the *actual* DT extension and uniqueness construction after the stipulated source shell theorem. Its existence, flatness, one-sided support and base-change behavior are already paid. A chosen basis lift is part of the data; no global family of shells or irreducible curves is assumed.

For t in B let rho_t be the spectral radius in note 02, using the ordered Kato basis with u_t as index zero. This number is independent of its phase presentation and is positive. For compact K contained in B put rho_K=max_{t in K}rho_t. The maximum exists since b fixes a finite set of possible period matrices; there is no continuity assumption on rho_t.

The desired operation would prove, for every such family, compact K, and beta>log(rho_K), a constant C(K,beta) with

    sup_{t in K} integral_{E_t} exp(beta h_t) omega_t <= C(K,beta),       (U)

and uniform decay of the integrals on {h_t<-M} as M tends to infinity. Together with the already known local current continuity, the latter would give continuity in the associated exponentially weighted current topology under a smooth deck-equivariant local trivialization. All minimal fiber types, including changes involving the Enoki branch, remain in the scope. No conclusion is asserted for b2=0, non-minimal fibers, noncompact bases without compact parameter control, higher dimensions, or moduli spaces. This is a feasibility question; (U) is not claimed true or false and was never frozen.

## The family part already closed by the primary construction

A base ball is 2-connected, so the universal cover of the total family restricts to each fiber's universal cover. The source topology proves pi1=Z and the required smooth type. Each fiber has a shell, hence the strictly pseudoconvex sphere used by DT. The missing generic simply-exceptional locus is not an obstruction for a family all of whose fibers are minimal: DT Remark 7 specifically handles this by passing to small deformations and the versal family, then base changing. Its Theorem 2 supplies the flat divisor even when the displayed family has no exceptional curve on any fiber.

In a relatively compact parameter neighborhood, the barrier argument in the proof of DT Theorem 5 gives a common upper height bound for E_t. Its construction with the forward semigroup and local finiteness provides the corresponding bound in the codimension-two extension proof as well. Flatness of effective relative Cartier divisors supplies continuity as local cycles and hence local current convergence; with a smooth metric, compactly supported mass tests are locally bounded. These are local-in-space statements. Replacing them by uniform weighted control on the entire negative end would be an additional operation.

## The finite spectral part is fully paid

Write beta=log(rho_K)+epsilon and beta'=log(rho_K)+epsilon/2. There are only finitely many b-periodic words s with 1<=s_j<=b+1. For each actually occurring word its rational functions F_r from (4) have nonnegative coefficients and are finite at z'=exp(-beta'). Therefore

    C_spec(b,rho_K,epsilon)
       = max_{occurring words,r} F_r(exp(-beta'))

is finite. It can be bounded using the larger finite set of words with rho<=rho_K. This involves only finitely many explicitly defined integer matrices, with no assumption that every word is realized by a surface. One may compute their resolvents or use Jordan form; no fixed graph, primitive Perron matrix, simple eigenvalue or spectral gap is needed. This closes the discrete uniformity problem.

For each t select its ordered reference curves C_{t,0},...,C_{t,b-1} as in DT. Define

    V_{t,r}(beta') = integral_{C_{t,r}} exp(beta' h_t) omega_t.

The exact nonnegative identity from note 02 yields

    W_beta'(E_t) = sum_r V_{t,r}(beta') F_{t,r}(exp(-beta')).            (7)

Moreover a_r>=1 for every r>=0, so F_{t,r}(z')>=1. Consequently the uniform boundedness of W_beta'(E_t) is equivalent, up to the explicit finite constant b C_spec, to

    sup_{t in K, 0<=r<b} V_{t,r}(beta') < infinity.                     (G)

The family uncertainty has thus been reduced from infinitely many divisor components to b compact *irreducible* reference curves, their actual geometric positions, and their weighted areas. The spectral denominator and every infinite coefficient sum have been paid.

If (G) were established at beta', then

    integral_{E_t cap {h_t<-M}} exp(beta h_t) omega_t
        <= exp(-(beta-beta')M) W_beta'(E_t)
        <= b C_spec C_geo exp(-epsilon M/2),                          (8)

uniformly on K. Together with a common upper support bound and local flat-cycle continuity, (8) supplies the desired weighted current continuity. There is no interchange of an uncontrolled infinite sum and a parameter limit in this implication.

## Trying the actual source analysis as the geometric input

On a compact parameter patch lying entirely in the source's no-square-zero branch, fixed nontrivial multiplier circles form a compact parameter set of acyclic compact elliptic complexes. The source's own Neumann-series inverse argument gives uniform bounds on such circles. Smooth compact data, a fixed large correction rate and the scalar top-degree solution can then be chosen locally with uniform norms. The index-one kernel has constant dimension; normalizing the positive-end coefficient gives a continuous family of sections. The Fourier residue calculation makes that coefficient a continuous functional. Thus the source ball-chain/three-circle proof has uniform atlas constants and a locally uniform starting logarithmic bound. It supplies a coarse common area exponent A_K and a common prefactor on such a patch.

This argument is a parameter version of the *same* source operators, not a new compactness theorem. It does not supply a value A_K<=log(rho_K). Summing its bound only gives uniform weighted mass for beta>A_K. The fixed-fiber spectral identity improves the convergence threshold separately on each fiber but does not, by itself, improve the family prefactor at beta between log(rho_K) and A_K. At a square-zero/Enoki transition the source's nontrivial-character acyclicity is no longer available at every character, so invoking one compact inverse family across that transition would be invalid. DT still supplies the flat divisors there; only this analytical shortcut ceases to justify the quantitative bound.

No theorem about all Enoki character cohomology is asserted here, nor is a source statement used outside its no-square-zero branch. The argument above explains exactly which compactness of operator parameters helps and which requested quantitative interval it leaves open.

## Why ordering and finite recurrence do not finish (G)

For a fixed fiber the integral triangular relations also give

    E_i = C_i + sum_{d=1}^{s_i} E_{i+d},
    E_{i+1} <= E_i,   f_*E_i=E_{i+b}.

To justify the first equality, both sides have the same Borel–Moore class and bounded-below curve indices, so DT's one-sided uniqueness applies. Positivity proves the second. Expanding the first relation through one period expresses E_0 as a positive sum of C_0,...,C_{b-1} and at most L future E_j with bounded integer coefficients. Since E_j<=E_b for j>=b, this gives a coarse positive recursion with a finite compact-curve forcing term. Iterating the recursion reproduces (7); it does not bound that forcing term geometrically.

In DT's elementary *holomorphic* ball decomposition each C_j lives in a uniformly bounded number of elementary pieces, at most b+1 steps after its creation. For one fixed fiber its Kato-chain height and the chosen smooth height differ by a bounded amount. To make this comparison uniform in t one needs control of the holomorphic pieces relative to the fixed smooth family trivialization, including their metric distortion and the positions of the marked classes. DT's flatness theorem chooses smooth pseudoconvex barriers; it does not assert such a uniform holomorphic Kato-data parametrization. The rational curves themselves can change homology class and have exploding area in minimal GSS families, as the actually read primary introduction illustrates. Therefore they cannot be silently treated as a proper fixed family of b curves.

The following elementary measure example diagnoses only a logical implication, not a geometric counterexample: on a line, nu_n=delta_0+exp(c n)delta_{-n} converges on every compact test to delta_0, is uniformly bounded towards the positive end, and each nu_n has finite weighted mass for every positive beta. Yet its beta-weighted mass is 1+exp((c-beta)n), unbounded for beta<c. Local convergence, one-sided support and fiberwise finiteness do not give uniform weighted tightness. No assertion is made that these measures occur on class VII surfaces. The geometry encoded by (G) could still exclude this behavior; that exclusion is what remains to be proved.

## Exact remaining operation and disposition

A full solution of this developed operation must prove (G) for the actual DT reference curves and every compact parameter set at every supercritical beta'>log(rho_K), or replace it with an equivalent estimate controlling the real holomorphic-to-smooth coordinate transfer and weighted areas through changes of curve configuration. The finite period matrices, their spectral bounds, the integral identification of Source060 divisors, local flat continuation, and compactness of individual components are already paid. A uniform inverse on the wrong character set, an assumed constant graph, or an unproved uniform Kato collar is not a substitute.

No such all-fiber geometric estimate was established. No counterexample, nonvanishing obstruction, general impossibility, exhaustive search, new-to-literature priority, or mathematical self-grade is claimed. Everything that has closed here is retained as a derivation or a source/primary composition; it is not submitted as a weaker theorem. Disposition: PREFREEZE/no nominee. There are no frozen theorem bytes and no author-proof development to preserve.
