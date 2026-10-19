# Analytic kernels: a preselection compatibility calculation

This is feasibility work, not a frozen theorem or a nomination. Source228 means the bounded-core radial continuum manuscript at the stipulated pin; exact raw paths, Git blobs and SHA256 values are in source-register.json. Its operative contracts, including proofs, are assumed true. No assertion below audits their truth. The calculations occurred before any freeze. There was no freeze.

The question explored was whether the same common inverse-temperature transition throughout an open density interval can be obtained with a radial real-analytic interaction, retaining an explicit integrable algebraic tail. A finite-volume transition, a density subsequence, or a different temperature for each density would not address that question. This note does not submit that full theorem. It tests whether analyticity leaves a new operation after using the strongest existing framework.

## The stronger source and historical operations

`f:thermodynamics` proves the canonical limit along EVERY real-side/integer-count sequence with prescribed limiting density. Its key product inequality uses nonpositive interbox interactions, with gaps of width two; exact count adjustment changes a vanishing fraction of boxes. `f:moments` works for the entire class `f:modified-energy`: full intracell core, arbitrary deletions of nonnegative cross-cell core, and attractive cell-supremum row bound M. It is not confined to a translation-invariant Gibbs state. The finite maximum of cell exponential moments is first proved finite and then satisfies F_max <= C F_max^(4M²/D0²), with D0>=8M. Consequently absolute pair-interaction interpolation has a volume-uniform logarithmic bound.

`k:range` is uniform in every positive added mass a, however small. Deleting reference interactions across boxes costs O(R0/s); upper/lower kernel row sums cost O(s/R). The lower product uses independent grand ensembles at the shifted field and the square -u d+d²/2>=-u²/2. It does not require convergence of finite-volume densities to an active density. This gives error C sqrt(R0/R), with C fixed after t and the parameter compact.

`k:transform-properties`, `m:one-step`, `m:schedule`, `m:propagation`, `m:pressure-ball`, and `m:canonical-corner` already retain full subdifferentials and a common support ball. The schedule R_n=R_1^(2^(n-1)), a_n=R_n^(-1/16) for n>=2, has delta_n=C R_n^(-1/4), and delta_n/a_(n+1)=C R_n^(-1/8). That summability, not mere pressure convergence, keeps the corner. The first attraction has mass A=3/(2p); the initial slopes are (0,0),(3p/4,p),(12p,4p). The source centers its density interval at 5p/3 and keeps one beta_c in [7/8,9/8].

The actual r16 candidate and two-temperature contribution comparison already develop changed core geometry, uniform moments, exact count adjustment, multiple simultaneously retained support regions, and the same schedule. The actual r33 `228-conditioned-comparison.md` additionally proves moments/interpolation under arbitrary bounded-Lipschitz soft block penalties. Its failure in the hard-conditioning limit is not an analytic-kernel obstruction. These are stronger antecedents than their titles. R33 was reread after the first Gaussian calculation, before any freeze. R49's similarly named boundary-pressure note is about imaginary chaos, not this interaction.

## First feasibility calculation: Gaussian rows and normal convergence

Write G_R(x)=pi^(-3/2) R^(-3) exp(-|x|²/R²). For fixed small-cell size b and R>=1, its cell-supremum matrix has bounded row sum independent of R. Its distance-weighted row sum is O(R). Both follow by rescaling the Gaussian and summing concentric lattice shells; the extra polynomial factors are integrable against exp(-c|x|²). Likewise a mesh of side s<=R has upper and lower Darboux row errors O(s/R): the difference is bounded by cell diameter times the cell supremum of |grad G_R|, whose scaled shell sum is O(1/R). An outer finite-box boundary is treated by first removing a fixed multiple of R and then letting that multiple tend to infinity. It cannot be declared exactly zero as for a compact kernel.

For a finite reference sum, translate the large-box grid through its small-cell offsets. A cell pair of displacement z is separated by a grid boundary for at most C min(1,(|z|+b)/s) of these offsets. Thus the average deleted cell-supremum sum per volume is at most

    C/s [M_core + t sum_(j<=n) a_j R_j].

At least one offset has this bound. Here M_core is a finite first-moment envelope for the fixed core, including the harmless b term. For increasing R_j>=1 and bounded total mass, the bracket is at most C_t R_n. The source interpolation moment bound then gives the desired O(R_n/s) pressure error. This is a first-moment replacement for literal support, using the SAME compatible deletion class. The infinite final attraction need not have a finite first moment; only each finite reference uses this estimate, and the remaining mass is handled by the source uniform pressure interpolation bound.

On a compact subset of C³, the entire extensions of G_R are bounded by C_K R^(-3) for R>=1. Hence any sum with summable nonnegative masses converges normally there. With epsilon=1/32,

    r^(3+epsilon) sum a_n G_(R_n)(r)
        <= C_epsilon sum a_n R_n^epsilon < infinity

under the source schedule, since sup_(u>=0) u^(3+epsilon) exp(-u²)<infinity and 1/16>epsilon. This verifies the analytic-series and tail interfaces at the level of the proposed kernels; it is not itself a phase-transition proof.

## A stronger compatible repair to the sign issue

Initially, smoothing the positive core seemed to lose the exact nonpositivity beyond radius two used in `f:canonical-product`. The following better reduction removes that particular issue before selection.

Extend the source core to R³ radially and put

    psi_e = psi_t * G_e,    v_0 = psi_e - d G_1,

with 0<e<1 and d>0 small, chosen after fixing t. This remains radial and entire as a function of the three Cartesian complex variables. Since psi_t is bounded, continuous and supported in the ball of radius two, psi_e converges to psi_t both uniformly and in the cell-supremum row norm. For the latter, uniform convergence handles finitely many cells and a common Gaussian tail handles the remaining cells. For r>2,

    psi_e(r) <= ||psi_t||_1 pi^(-3/2)e^(-3) exp(-(r-2)²/e²).

Its ratio to d G_1(r) tends to zero: the coefficient of r² in the logarithm is 1-e^(-2)<0. Therefore v_0<=0 outside a finite radius D depending on t,e,d. Every subsequent negative Gaussian attraction preserves that SAME sign radius. This is an exact eventual sign, not an approximate sign assertion.

Intracell stability is also retained. If ||psi_e-psi_t||_infinity<=tau, the source intracell core energy loses at most tau n(n-1)/2. Thus D0 can be replaced by D0-tau/2, with a harmless adjustment of the linear term. The extra attraction dG_1 adds at most C_b d to M. Choose t with a strict original margin and then tau,d small so D0'>=8M'. Reserve d/t within the unused attraction-mass budget before choosing the later schedule. The same conditional empty-cell proof yields F_max<=C F_max^eta, eta=4(M')²/(D0')²<1, uniformly under the deletions/interpolations needed above. These estimates close this local moment issue; it should not remain listed as an unknown central invariant.

The finite canonical upper cost follows from Jensen with uniform independent positions: the positive part has a finite L1 bound, so average pair energy is at most C N(N-1)/L³. The quadratic lower energy bound gives the other finite canonical estimate and grand-count truncation. In the source all-sequence argument, replace gap two by this fixed D. Its changed-box fraction is controlled by |d(1+D/s_j)³-n_j/s_j³| and tends to zero in exactly the prescribed order. Infinite attraction sums preserve the sign and quadratic bounds. Thus a generic thermodynamic-limit citation is not needed to repair this sign issue.

For a small initial pressure perturbation, interpolate the core and pedestal while retaining the preceding common moment constants. The logarithmic derivative estimate bounds the pressure change by the cell-row norm of psi_e-psi_t-dG_1, which tends to zero with e,d. The source initial active-shift/secant argument uses a fixed strict tolerance before the attraction iteration; it accepts such a small perturbation. This differs crucially from smoothing a completed final model. These calculations give a credible compatible route through the main previously apparent interfaces. I have not written or independently certified a full analytic-potential theorem with every finite-boundary row estimate, all constants and the final source iteration reassembled. More importantly, no genuinely unpaid compatibility operation has been isolated after these checks. There is no basis to nominate an analytic-regularity headline merely because no identical title was found.

## Limits of the calculations

A fixed uniform pressure perturbation after the final iteration does not preserve corners: sqrt(x²+delta²) approximates |x| uniformly but is smooth. This is a shortcut diagnostic only. It neither refutes analytic phase transitions nor supplies a new result. The pre-iteration core/pedestal construction is the stronger compatible reduction.

The same sufficient scale budget does not establish exponential decay. At r=R_n a positive Gaussian-mixture term is proportional to a_n R_n^(-3); a uniform exponential bound on that attraction alone would force a_n<=C R_n³ exp(-cR_n). Such small masses are incompatible with obtaining summability from the currently available polynomial RANGE-ERROR UPPER BOUND divided by the next mass. An upper bound is not a lower bound on the actual error. No impossibility theorem, lower error bound, or finite-range transition is inferred.

The primary comparison is deliberately limited. Ruelle's [1970 paper](https://www.ihes.fr/~ruelle/PUBLICATIONS/%5B28%5D.pdf), Theorems0.1–0.2 and the inspected part of §2, supplies the classical superstable/lower-regular occupation framework. Its OCR loses formulas; printed p139 was rendered and read, including the quadratic cell estimate (2.24) and weighted shell bound (2.23). This is not a full new reading of its canonical thermodynamic theory. The decisive canonical count correction and compatible moment mechanism above are present explicitly in the pinned source. No unread Lebowitz–Penrose or later Kac proof is represented as primary clearance. Further full-proof and primary comparison would be required before any theorem submission. No freeze, rating, gate or count is assigned here.
