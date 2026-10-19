# Hard block counts: prefreeze relocation calculation

This is a feasibility calculation inside the old full finite-range radial-transition question. It is NOT a frozen target, a nominee, a contribution classification or a correctness gate. In particular the finite-range question in r33 is not replaced by the following local moment statement. No full phase-transition theorem is proved here.

## Exact setting of the calculation

Use the bounded-core source228 family `f:modified-energy`, at the stipulated pin. The small cells have side b=1/4. Write the interaction as v(x,y)=c(x,y) psi_t(|x-y|)-K(x,y), with 0<=c<=1, c=1 within each small cell, K>=0 bounded and symmetric, and J_ij=sup K on C_i times C_j. Its row sums are <=M, D=t²/8>=8M, B=t²/2. The core is nonnegative, bounded, supported at distance <=2, and has finite integral P=integral_R³ psi_t. The intracell lower bound is D n²-B n. Arbitrary permitted deletions and interpolations remain included.

Partition the finite spatial region into finitely many disjoint axis-parallel cubes B_a, each a union of small cells, each side at least 8. They need not have equal sizes or form one larger cube. Fix arbitrary integers 0<=N_a<=rho_* |B_a| for one finite rho_*. Use the ordinary canonical Gibbs law with exactly N_a particles in each cube, and no external fixed particles outside the union. Beta belongs to one fixed interval [beta_-,beta_+] contained in (0,infinity). An arbitrary nonzero finite nonnegative weight depending ONLY on the vector (N_a), supported in these caps, can subsequently be mixed in. It may couple the block counts, have zero weights, or enforce exact counts/closed intervals; no positive lower count is needed. It must not depend on positions within a fixed count sector.

The calculation gives a constant C depending on t, rho_*, beta_-, beta_+ (and the fixed b), independent of cube count, cube sizes, count vector, attraction ranges and the allowed interaction deletions, such that

    E exp(beta D n_i²/4) <= C

for every small cell. The nonnegative-count mixture inherits the SAME bound. This is a useful local compatibility calculation, not the intended full physical conclusion.

## A reservoir inside the same block

Fix i in a cube B_a of volume V and side L>=8, and let

    A_i = {z in B_a : dist(z, B_a^c)>2} minus C_i.

Then |A_i| >= (L-4)^3-b³ >= V/16. This remains true when C_i touches the boundary; the reservoir does not have to be adjacent to i. Set c_*=1/16 and a_i=|A_i|. A particle placed in A_i has zero core interaction with EVERY particle outside B_a. This exact fact, not a bound on outside particle density, is why the fixed positive-core range matters.

Suppose n particles have been removed from C_i and Y denotes every remaining particle, including all other cubes. There are N_a-n remaining particles in B_a. Insert n independent uniform points Z_1,...,Z_n in A_i. Dropping the nonpositive attractions, using c<=1, and integrating the nonnegative core gives

    E_Z [U(Y,Z)-U(Y)]
      <= P [n(N_a-n)+n(n-1)/2]/a_i
      <= P n N_a/a_i <= L_* n,
    L_* = P rho_*/c_*.

No separation of the inserted particles is required: the bounded core permits coincidences, and the integral estimate covers their mutual interactions. Jensen therefore gives the fixed-count insertion inequality

    integral_(A_i^n) exp(-beta U(Y,Z)) dZ
      >= a_i^n exp(-beta L_* n) exp(-beta U(Y)).                 (1)

All counts are restored in their ORIGINAL block. This differs from emptying a cell and deleting particles, which is inadmissible under exact block counts.

## Factorials and the surviving field

Let G_i(Y)=sum_(j!=i) J_ij n_j(Y). Nonnegativity of J implies

    G_i(Y,Z)>=G_i(Y)>=0,

because all relocated particles lie outside C_i. Thus (1) also gives

    exp(-beta U(Y)) exp(beta G_i(Y)^2/D)
      <= a_i^(-n) exp(beta L_* n)
         integral_(A_i^n) exp(-beta U(Y,Z))
                      exp(beta G_i(Y,Z)^2/D) dZ.               (2)

For the original n particles in C_i, the exact source conditional energy estimate is

    U(Y,X)-U(Y) >= (D-J_ii/2)n²-Bn-nG_i(Y).

After multiplying by exp(beta D n²/4), use

    nG_i <= D n²/4 + G_i²/D,
    D/2-J_ii/2 >= 7D/16.

Integrating their positions costs at most b^(3n), so their contribution is bounded by

    b^(3n) exp(-7 beta D n²/16 + beta Bn)
        exp(-beta U(Y)) exp(beta G_i(Y)²/D).                    (3)

The sector measure for B_a has factor 1/N_a!. Splitting according to n_i=n gives exactly 1/[n!(N_a-n)!]. Substitute (2) into (3). The remaining coordinates Y in B_a\C_i and inserted coordinates in A_i together range over a subset of (B_a\C_i)^(N_a). The enlarged integrand is symmetric in these N_a coordinates. Extending this integration to all of B_a^(N_a), and retaining all other block coordinates, yields the normalized factor

    binom(N_a,n) (b³/a_i)^n
      <= (rho_* b³/c_*)^n/n! .                                (4)

There is no additional factorial or volume factor, and no division by the probability of the hard count event. The restored integral is bounded by the full sector expectation of exp(beta G_i²/D). The same inequality holds for n=0; in that case insertion is the empty integral. If N_a=0, n_i=0 identically.

Put z_*=rho_* b³/c_* and

    C_2 = sum_(n>=0) z_*^n/n!
          exp[-7 beta_- D n²/16 + beta_+(B+L_*)n] < infinity.

Summing (3)-(4), for each fixed count sector, gives

    F_i := E exp(beta D n_i²/4)
       <= C_2 E exp(beta G_i²/D).                              (5)

The fact that the other block counts were fixed causes no loss in (5): the insertion never changes any one of them. Finite total particle number gives F_max<infinity before taking a maximum.

## The strongest source closure now applies literally

The source's weighted Cauchy--Schwarz calculation gives

    G_i² <= M sum_(j!=i) J_ij n_j².

With u=beta D/4 and eta=4M²/D²<=1/16, add the missing zero weight to the weights J_ij/M, then apply convexity of exp and concavity of x^eta. Exactly as in source `f:moments`,

    E exp(beta G_i²/D) <= F_max^eta,
    F_max <= C_2 F_max^eta,
    F_max <= C_2^(1/(1-eta)).                                  (6)

When M=0, G_i=0 and (5) directly gives F_i<=C_2, so no division by zero is needed. The constant in (6) is uniform in the sector. Disintegration over any allowed count-vector weights proves the same estimate for the hard-constrained mixture. This last step is finite mixing, since the region and all count caps are finite.

The second moments obey E n_i²<=4C/(beta_- D); Cauchy--Schwarz controls mixed moments. Interpolating v_theta between two allowed interactions while retaining the SAME count weights consequently gives

    |log Z_1-log Z_0| <= (beta C_1/2) sum_ij Jdiff_ij.           (7)

Differentiation requires no infinite-series limit in this hard-capped setting: total particle number is bounded, all pair potentials are bounded, and the count sum is finite. A weight depending on theta would add another derivative and is NOT included.

## Why this does not close the full question

Equation (7) is absolute pair-error control for the hard-restricted partition functions. It can improve a particular preliminary comparison from r33, whose soft-penalty constant diverged as the penalty slope grew. It does not supply phase competition, contour suppression, metastable pressures, or the three simultaneous non-collinear slopes at one physical finite range.

For a smooth Kac kernel of range R and mesoscopic boxes of side ell, the usual Darboux error has total row discrepancy O(ell/R) per unit volume. The hard-count moment calculation keeps this estimate valid for each specified count pattern. On a droplet of diameter L, the resulting error remains O((ell/R)L³). At fixed ell/R>0 this cannot be charged to an O(L²) interface uniformly as L tends to infinity. Deleting only interactions incident to a contour is local, but first replacing the whole physical model by a boxed model changes the pure-phase bulk as well. Cancelling that bulk through correctly constructed restricted phase pressures and controlling the remaining contour activity has NOT been done.

The primary HJLP boxed model has an exact nearest-neighbor positive squared-density-gradient term. Its chessboard inequality is not a consequence of (7). A radial physical kernel is not made reflection positive by a small pressure error or by integrating over the box origin. The source's one-step ideal-attraction transform recovers slope groups after another positive attraction; it recovers the physical corner only after its infinite-range limit. Stopping after finitely many steps is still unjustified.

Hence the full finite-range common-temperature/open-density-interval target remains open in this work. There is no nominee and no replacement with a conditional, finite-volume, fixed-density, soft-phase, or moment-only theorem.

## Antecedents and timing

The source supplies more than a moment headline: `f:canonical-bounds` already uses uniform-position Jensen insertion; `f:modified-energy` allows the entire deletion/interpolation class; `f:moments` supplies the exact square-completion and F_max contraction; `f:perturbation` gives the derivative identity. The present calculation tries these strongest compatible operations together before any assertion of an unpaid mechanism. Ruelle1970 supplies the classical superstable/lower-regular correlation framework, actual Proposition2.6 induction and Proposition2.7 quadratic occupation estimate. Their displayed grand-canonical definitions were visually checked on printed pp140-141; they do not by themselves license conditioning on an arbitrarily rare exact count vector. This note supplies that interface explicitly, without claiming that the interface is new to the literature or substantial.

R33's full conditioned-comparison and checkpoint, r16's original scope/selection, the actual two-temperature contribution reduction, and r121's analytic-kernel calculation were read. The r121/two-temperature reads followed the initial relocation feasibility; they occurred before any freeze (none ever occurred). Ruelle and HJLP primary proof passages were also read after initial feasibility. Exact versions, hashes and reading limits are recorded separately. Their late reading cannot be backdated. This is author-side mathematical reasoning only, awaiting any independent assessment the parent elects to request.

A further late primary comparison was Jex–Lewin–Madsen, *Classical density functional theory: the local density approximation*, [2310.18028v1](https://arxiv.org/pdf/2310.18028v1). Actual Theorem20/Corollary21, the Step3 exponential integration, and Corollary26 with its proof were read. The quantitative Ruelle law there is grand canonical; the external-potential extension uses a uniform lower bound on that potential and constants depending on it. This does not justify passing to an arbitrary exact block-count vector by dividing by its probability, or taking an infinite penalty while retaining the same constants. Its local-density approximation theorem is not a contour-ratio theorem. The full main LDA proof was not read, so this is a comparison at the recorded operative interfaces only.

He–Jauslin–Lebowitz–Peled, *Liquid-vapor transition in a model of a continuum particle system with finite-range modified Kac pair potential*, [2510.24825v1](https://arxiv.org/pdf/2510.24825v1), was checked through the actual boxed-particle Hamiltonian (1.13)–(1.14), Assumption1, Theorems1.6/2.1, and chessboard/tightness machinery. Its model explicitly suppresses reference interactions across the fixed cubes and uses cube-constant adjacent attraction. No radial translation-invariant counterpart is silently substituted. The abstract transition criterion needs simultaneous rare-event/interface estimates. The moment bound above supplies neither that criterion's full hypotheses nor its reflection-positive construction. The original chessboard proof cited by that primary was not freshly read.

Ruelle, *Superstable Interactions in Classical Statistical Mechanics*, Commun.Math.Phys.18(1970),127–159, [author-hosted published body](https://www.ihes.fr/~ruelle/PUBLICATIONS/%5B28%5D.pdf), is credited for the classical superstable occupation framework. Its exact PDF hash fixes this unversioned URL. The two rendered pages were read to repair missing equations in text extraction. No original-literature novelty claim is based on a missing phrase in these three sources.
