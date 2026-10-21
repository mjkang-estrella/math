# Author proof development for the unchanged full question H

Research proof, not an independent review, manuscript, acceptance, or contribution grade. The statement is frozen in H-SCOPE.md. All pinned Source361 operations below are stipulated true at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. The present construction is a proposed proof of the full fixed-metric question retained in I130/I133, not a new version of their finite-prefix proposition.

## 1. Inputs, conventions, and the new operation

Write S for the September26 manuscript `A-Three-Dimensional-Counterexample-to-Integer-Degree-Harmonic-Dimension-Comparison-September-26-2026`, and use its TeX labels. The proof uses the following operations, with their actual finite-cutoff restrictions retained.

* `crossings.tex`: `n:lem-two-directions`, `n:lem-avoidance`, `n:lem-retained-double`, and `n:lem-adjacent-doubles`. In an arbitrarily small fixed C2 neighborhood of the round sphere, a prescribed sufficiently high adjacent pair can be made an isolated simple double, all other coincidences through any prescribed **finite** larger cutoff can be removed, and simple endpoints can be joined by a simple path through a prescribed finite cutoff. The fixed-area gauge `n:eq-fixed-area-gauge` gives one angular measure and uniform C0 tensor comparison.
* `angular-program.tex`: continuation of eigenlines through the doubles implements adjacent swaps. A cycle of a finite rank band has the rank-averaging identity `n:eq-band-frequency-average` independently of the durations of its constituent loops.
* `geometry.tex`: the exact Ricci block identities `n:ricci-radial-input` through `n:ricci-tangent-input`, including the mixed block. We use their formulas with a nonperiodic integrable radial buffer, whose choice is proved below.
* `transfer.tex`: whole-ball restrictions preserve mean and constants, are positive L2 contractions, and depend strongly continuously on the finitely many controls in each compact ball. The local freezing proof gives a full-operator o(1) estimate and, separately, a finite-frame error O(eta log(1/eta)+eta^2). The operator estimate is NOT treated as o(eta^(3/4)). The finite-cluster divided-difference computation gives the signed coefficient `n:eq-crossing-leading-coefficient`.
* `matching.tex`: the exact finite scalar recurrence, the orientation of zero versus matching cuts, and the Gaussian stable-weight calculation. Below we verify their extension across the nonperiodic stage joins; their fixed-program uniform constants are not assumed uniform over all stages.

The finite-band selection and rank averaging already occur in I130 H1 and I133. The proposed additional operation is to construct, for each band, two exact finite-rank spaces at its lower and upper cutoffs, take their quotient, and match only this finite quotient. A countable product then shares all controls. There is no infinite column inverse and no uniform cutoff bound. Each band is activated only after its finite angular data are available. The source's terminal graph iteration supplies compatibility by inclusion, rather than an independently chosen graph at each cutoff.

Let mu be round probability area measure on S2. Eigenvalues of -Delta_H are numbered from 1, including the constant. Set B_l=(l+1)^2 and d(x)=(sqrt(1+4x)-1)/2. All vector spaces are real. Logarithmic radius is t=log r; integer logarithmic radii are denoted j. Operator graph norms are the Hilbert-space norms induced by L2(mu).

## 2. Finite bands selected once

Fix v,c in the frozen range, let a=sqrt(v), and choose

    sqrt(c)<theta<3a/2,
    C_*>1 with 2theta sqrt(C_*)/(3a)<1,
    a^2<kappa_*<1.

Choose a convex C2 neighborhood U of the zero conformal parameter so small that all its fixed-area links satisfy K_H>kappa_*, a common C0 comparison with the round metric, and

    lambda_j(H)<=C_* l(l+1) for B_{l-1}<j<=B_l.

We may and do use a smaller neighborhood for reference paths, leaving a fixed C2 margin for controls. All smooth families used at an individual stage are compact finite-parameter families in U; no uniform bound on all their high spatial derivatives is asserted.

Choose strictly increasing integers k_i recursively. Put

    L_i=floor(sqrt(k_i)), M_i=floor(theta k_i),
    Q_i=B_{L_i}, P_i=B_{M_i}, D_i=P_i-Q_i,
    I_i={Q_i+1,...,P_i},
    m_i^*=sqrt(C_*)/a * [sum_{l=L_i+1}^{M_i}(2l+1)(l+1)]/D_i,
    beta_i=sqrt(C_*)/a*(L_i+1)+1.

Require L_i>M_{i-1}, D_i>c(k_i+1)^2, and max(m_i^*,beta_i)<k_i. Also require the source's high-adjacent-crossing threshold. These are cofinite requirements: D_i/k_i^2 tends to theta^2>c, m_i^*/k_i tends to 2theta sqrt(C_*)/(3a)<1, and beta_i/k_i tends to zero. Choose once a number

    max(m_i^*,beta_i)<gamma_i<k_i.

For each n construct a finite program containing the disjoint cycles on I_1,...,I_n and no other crossings through P_n+1. At each desired double, apply retained-double splitting at the larger cutoff P_n+1. Join all loop endpoints to one base simple through P_n+1. Each partial permutation preserves every band. Concatenate the loops and repeat by a common multiple of D_1,...,D_n, doubling for frame signs if necessary. Denote this full label period by A_n. The reference parameter is constant near the base; the continued frame returns exactly after A_n.

For every band i<=n and every one of its labels, the mean of Theta(s)=d(a^(-2)lambda_label(s)) over A_n is at most m_i^*. Indeed, at each fixed phase of the basic concatenation, successive returns of the label visit every rank of I_i equally often. The ordered bound and d(x)<=sqrt(x) give the displayed formula for m_i^*. This is precisely the credited finite-band operation. Every pair of labels in a band crosses during a full label period, and the pair's simple zero crossings alternate their sign changes. All cutoff gaps at Q_i and P_i remain strict.

Join the base of program n to that of n+1 by a path simple through P_n+1, constant near its endpoints. Call this connector C_n. It preserves all OLD cutoff gaps and all old ordered labels. No condition is imposed on new high modes along C_n. At the new base, where the spectrum is simple through P_{n+1}+1, place a constant collar before activating the new band. This explicitly avoids demanding a new graph through old high-spectrum degeneracies.

## 3. Two elementary graph facts

### 3.1 Nonuniform contraction

Suppose F_j maps a closed operator ball of radius rho into itself, and Lip(F_j)<=1-a_j, with 0<a_j<1 and sum_{j>=J}a_j=infinity. Iterate inward from terminal value 0 at N. For M>N, the value of the M-iterate at N is still in the same ball. Hence at fixed j<N the two iterates differ by at most

    2rho product_{l=j}^{N-1}(1-a_l).

This tends to zero, since log(1-a_l)<=-a_l. The terminal iterates therefore converge at each j, uniformly over any additional parameters for which the inequalities hold. The limit is the unique bounded graph family in that ball satisfying V_j=F_j(V_{j+1}). If finite iterates are continuous in product parameters, uniform tail convergence proves continuity of V_j. A sufficient ball-preservation condition is ||F_j(0)||<=a_j rho.

On a future window j,...,j+N-1 with a_l>=a_0>0 and ||F_l(0)||<=C delta_j, iteration gives

    ||V_j|| <= C delta_j/a_0 + rho exp(-a_0 N).                 (3.1)

In particular a window K log(1/delta_j), with K chosen after a_0, makes the last term o(delta_j). These facts require no positive lower bound for all the a_j at all times.

### 3.2 Inclusion of limiting low spaces

Let T_j be the SAME exact inward maps for two fixed cutoffs q<p. At a common terminal time N, the ordered reference low spaces satisfy E_q(N) subset E_p(N). Their inward images under T_j...T_{N-1} retain inclusion. Suppose both image families are graphs, with invertible low-coordinate maps, and converge in graph norm as N tends to infinity. Then their limits S_q(j), S_p(j) satisfy S_q(j) subset S_p(j). For example, unit vectors in the smaller image have distance zero from the larger image; convergence of their finite-dimensional graph projections passes this to the limit. This proves compatibility using common terminal data. It is not an assumption about two unrelated invariant-space choices.

## 4. Slow scheduling and local estimates

This is the main extension beyond a fixed finite source program. We give the scheduling construction and the estimates it must satisfy before selecting any controls.

Use eta(t)=t^(-3/4), delta(t)=eta(t)^(3/4)=t^(-9/16), at sufficiently large t. Traverse the reference paths with phase derivative eta. A stage consists of an integer number, at least two, of full label periods A_n, followed by C_n and a constant collar at the next base. Each repetition is a translation in phase, so its finite family bounds do not depend on the number of repetitions. Repeating program n indefinitely would make t tend to infinity, since the total phase integral is unbounded. Therefore its final repetition can always be chosen to place the next connector beyond any prescribed finite threshold.

At each crossing nu choose a fixed smooth phase bump chi_nu, supported in a small neighborhood of that crossing with plateau containing it. Supports are disjoint. Let psi_nu be the source conformal variation direction with nonzero off-diagonal entry on its pair. Use the controlled parameter

    w_z(t)=w(s(t))+sum_nu z_nu eta(t_nu)^(3/4) chi_nu(s(t)) psi_nu,
    -1<=z_nu<=1.                                             (4.1)

There are finitely many smooth bump types in each stage. At most one bump is active at a time. The schedule has no finite accumulation of stages or crossings, so every control sequence produces a locally smooth path and the metric on a compact ball depends on only finitely many controls. The reference path, speed, bumps, directions, and radial factor are independent of z.

Before the first activation, join the round link to the first simple base by a fixed smooth path inside U, constant near both ends. Place this transition at a sufficiently late radius, include its finite derivative bounds in the buffer budget, and follow it by a constant base collar. No spectral gap or graph is required during this initial transition. Activate the first cutoffs only deep inside the collar.

For a fixed stage, its connector to the next stage, and at most one neighboring full label period on either side, collect their finite smooth data into a compact family. For every previously active cutoff this gives a positive minimum outer frequency gap, finite frame norms, nonzero crossing slopes, separated crossings, and finite upper bounds for sign-interval phase lengths. For a newly introduced cutoff use only the new base collar and the subsequent program. All constants below are allowed to depend on this finite collection. The number of earlier repetitions does not enter them.

We impose the following requirements by delaying the appropriate entry or join. Their justification follows immediately below.

(a) The controlled paths stay inside U. Their speed and acceleration, including one spatial derivative of speed, have finite-family bounds C_n eta and C_n eta^2. A smooth envelope E(t), independent of z, dominates a fixed large multiple of ||H^(-1)H_t||^2 and ||div_H(H^(-1)H_t/2)||^2. Its mass on stage n and its connector is at most epsilon_n, where the positive epsilon_n are chosen with sum epsilon_n as small as needed below. Its local size is bounded by C_n t^(-3/2), including the adjacent collars. Positive-order time derivatives are locally bounded as required; no global C-infinity compactness is used.

(b) At each cutoff Q_i,P_i for i active, the exact graph transform preserves a fixed ball of radius rho_i<1/100 and has Lipschitz constant at most 1-a_i(j), with a_i(j)>0 independent of z. The sum of a_i(j) over each complete sufficiently late stage in which i is active is at least one. The exact local graph bound at every crossing or scalar sign interval in that stage is O(C_n delta(j)). The induced outward matrix is diagonal plus O(C_n delta(j)), and its crossing remainder after removal of the specified leading term is smaller than any prescribed finite multiple of delta(j). The coordinate and mismatch estimates below hold uniformly over all controls and all coordinate boxes.

(c) All scalar coordinate trial maps are strictly inside |u_hi(j)|<=eta(j)^(1/8); all fixed-point column matrices in the active finite quotients are invertible. On stage n, logarithmic multiplier errors and mesh errors for active bands are at most 1/n per unit time. Finite initial stages need only finite bounds.

(d) For each active band i, the entire prefix discrepancy in a stage relative to its phase mean is at most 2^(-n)t. Its connector contribution is also at most 2^(-n)t. Endpoints of stages are full label periods. The radial buffer has small total mass, and its local effect in the frame-freezing equation is o(delta).

We now justify that these are compatible finite demands and prove (b), rather than treating it as an extra input.

### 4.1 Geometry and buffer

On any one finite smooth collection, differentiating (4.1) gives the bounds in (a). Derivatives of eta are O(eta^2); speeds at points separated by bounded phase length are asymptotically equal because such intervals have time length O(t^(3/4))=o(t). Take a smooth finite-family upper envelope of the indicated squared norms. It can be bounded by C_n t^(-3/2), with transitions in constant collars. Extending its coefficient slightly into the collars makes the envelope smooth. Since

    integral_T^infinity C_n t^(-3/2)dt=2C_n/sqrt(T),

the entire mass cost of arbitrarily many repetitions beginning after T is small after delaying T. The connector is handled by the same estimate with its own finite constant. Choose summable budgets epsilon_n with total delta_0<1-a. No lower bound on a stage's duration conflicts with this bound.

Let beta be a nonnegative smooth function supported in (1,2), of integral one. Define

    f''(r)=-(1-a-delta_0) beta(r)-E(log r)/r,
    f(0)=0, f'(0)=1,                                         (4.2)

where E is zero before the tail begins and delta_0=integral E dt (the actual mass). Thus a<=f'<=1, f=r near zero, f' tends to a, and b(t)=e^(-t)f(e^t) tends to a. After the compact core,

    b_tt+b_t=-E,
    b_t(t)=e^(-(t-u))b_t(u)-integral_u^t e^(-(t-s))E(s)ds.      (4.3)

The bounded past contribution outside a window K log t is O(t^(-K)); on the local window E has its finite-family O(t^(-3/2)) bound. Therefore b_t,b_tt are locally O(C_n t^(-3/2))+O(t^(-K)), including stage boundaries. This is o(delta). These estimates are uniform in z, since f is independent of it. Also b>=a. By making total delta_0 small and the first angular motion late, b remains as close to a as required for the uniform tangential Ricci slack. Indeed after r>=2, f'(r)<=a+delta_0 and b<=a+delta_0+2/r.

Write A=H^(-1)H_t and B=A/2. Source formulas give

    r^2 Ric_rr=2E/b-tr(A^2)/4,
    r^2 Ric_rT=b^(-1) div_H B,
    r^2 Ric_T=(K_H/b^2-2q^2+q-q_t)I+(1-2q)B-B_t,
    q=1+b_t/b.

The last block is at least tau I for a fixed tau>0: K_H>kappa_*>a^2, b-a is small, and the derivative terms are small by delaying each finite stage. Choose the envelope coefficient so that

    2E/b >= tr(A^2)/4 + |div_H B|^2/(b^2 tau).

Since a<=b<=1, one fixed large multiplier suffices, with the finite-family norms included in E. The Schur complement gives Ric>=0. Where links are round or stationary, the same formula, or ordinary round-warped concavity on the compact core, applies. Thus the metric g_z=dr^2+f^2 H_z(log r) is smooth, complete, Euclidean near zero, and Ricci nonnegative for every z. Radial distance from zero is exactly r, and fixed angular area gives AVR=a^2. This verifies the geometric part without claiming any harmonic functions yet.

### 4.2 Whole-ball freezing on a nonperiodic end

For fixed cutoff d and a compact local reference family, the proof of S `n:lem-inward-transfer` is local at large logarithmic radius except for a uniformly bounded left boundary discrepancy. Its comparison on a backward slab of length 4log(1/eta) gives, on the finitely many smooth reference vectors,

    ||(T_j-P_j^*) e_h(s(j+1))||_2
       <= C_n [eta(j)log(1/eta(j))+eta(j)^2]+O(j^(-K)),         (4.4)

where P_j^*=exp[-d(b(j)^(-2)(-Delta_{H_z(j)}))]. The residual computation uses (4.3); the maximum principle bounds the left discrepancy independently of the whole earlier ball. Taking K>1 suffices for the displayed error to be o(delta) on a fixed finite collection. The same proof does not require b-a=O(t^(-1/2)): it freezes b(j) and uses small b_t,b_tt. The parameter b lies in the fixed compact interval [a,1].

The full-operator comparison with the reference frozen P_j^0 is only o(1). To check its uniformity here, assume failure along increasingly late positions in one fixed compact local collection with smaller and smaller speeds. Shift the outer boundary to zero. On every fixed-width past slab, coefficients converge smoothly after a subsequence to a constant cylinder with some limit b_* in [a,1] and some reference link H_*. Whole-ball L2 contraction bounds every sectional norm by the norm of the boundary data. Interior elliptic compactness, the weak boundary-trace argument in S, and elimination of the negative radial root identify the unique bounded-backward limit. Both exact and frozen inward maps on weakly convergent unit boundary data have this same strong inner trace. This contradicts operator-norm failure. The arbitrary earlier history never enters except via the contraction bound. It proves a finite-family threshold for any desired absolute operator accuracy, not a cutoff-uniform rate.

At a join, fixed-width slabs and the logarithmic slab of (4.4) lie in the union of the two neighboring finite programs, the connector, and their collars once the join is late. Uniformity follows from their combined finite bounds. A new cutoff is activated only well inside its constant base collar, farther than K_n log t from its left endpoint. The collar's time length is comparable to t^(3/4), so this is possible. Integer activation J_i can be chosen within it; the first crossing is separated by a positive phase distance.

### 4.3 Construct graphs before using their sharp local estimates

For each active d=Q_i or P_i, split T_j into LL,LQ,QL,QQ blocks using the reference first d modes. The first two bounds from (4.4) are

    T_LL=D_j+O(C_n delta_j), T_QL=O(C_n delta_j),
    D_j=diag(exp(-d_h(j))), d_h(j)=d(b(j)^(-2)lambda_h(s(j))).

The other two bounds are T_LQ=o(1) and ||T_QQ||<=kappa_ref,n tau_j+o(1), where tau_j=min_h exp(-d_h(j)) and kappa_ref,n<1 on the given finite collection. For each fixed d the near-round ordered bound gives a positive lower bound tau_d for tau_j over ALL later stages. It need not be uniform in d.

Use exactly the source transform

    F_j(V)=(T_QL+T_QQ V)(T_LL+T_LQ V)^(-1).                   (4.5)

On a ball of fixed radius rho_i, the inverse-difference identity in S bounds its Lipschitz constant by kappa_ref,n plus terms tending to zero as that finite collection is placed later. The low inverses are bounded by 2/tau_d. Delay until the extra terms are at most (1-kappa_ref,n)/2 and until ||F_j(0)||<rho_i(1-kappa_ref,n)/2. This proves ball preservation and a definite local deficit a_i,n>0, uniformly in all controls. For each stage, require enough late time that at least one full period contains total deficit at least one for every active cutoff. A full period has time length tending to infinity as its location tends to infinity. Requiring at least two full periods also ensures every scalar interval touches at most one join. Consequently sum_j a_i(j)=infinity for each fixed i. Section 3.1 now constructs the exact graphs, unique in their fixed balls, uniformly in controls.

The finite graph iterates are continuous in product controls. On any compact ball, only finitely many controls occur, and smooth-parameter Dirichlet dependence gives strong continuity of T_j. Acting on a finite-rank graph, strong continuity plus the uniform contraction bound gives norm continuity on its finite-dimensional domain, exactly as in S. The uniform terminal estimate of Section 3.1 then gives product continuity of the limiting graphs. Inclusion at Q_i,P_i follows from Section 3.2.

For the stronger LOCAL estimate, a future window of length K_n log j has contraction deficit bounded below by a positive number belonging to that finite collection. Enlarge K_n so that the terminal term in (3.1) is o(delta_j). On that window delta_l/delta_j tends uniformly to one, and (4.4) gives the inhomogeneous O(C_n delta_j) bound. Thus V_j=O(C_n delta_j). The window fits in one finite local collection; near a join use its two neighbors. A constant collar is much longer than log j, so no window has to cross two joins. This proves the local graph estimate **after** existence and continuity, avoiding circular use of a future-tail estimate.

Inverting the exact low map gives

    A_j=(T_LL+T_LQ V_{j+1})^(-1)
       =diag(exp(d_h(j)))+O(C_n delta_j),
    T_LQ V_{j+1}=o(delta_j).                                 (4.6)

The local divided-difference computation in S applies unchanged. On the plateau at a double crossing nu of labels h,l,

    (A_j)_{hl}=z_nu eta(t_nu)^(3/4) m_hl(s(j),b(j))+o(delta_j),
    m_hl(s_nu,b)=exp(d(b^(-2)lambda)) b^(-2)d'(b^(-2)lambda)
                 <e_h,dot L_nu e_l>.                        (4.7)

The coefficient is nonzero with one sign on a sufficiently small fixed plateau. Its minimum over the finite phase neighborhood and b in a fixed compact interval is positive. All other controls remain free: (4.4) is independent of earlier controls and the graph estimate is uniform over future tails. The remainders in (4.7) are made as small relative to this minimum as needed by the local threshold. No p=infinity claim has been used.

### 4.4 Exact finite quotients

Fix band i and abbreviate q=Q_i, p=P_i. In the reference p coordinates, split off the first q coordinates. The inclusion already proved identifies the q space inside the p space as

    {(x,W_j x): x in R^q},  W_j=Pi_(q,p] V_j^q.

Indeed the first q coordinates of its full Hilbert-space graph are x, and its next p-q coordinates are W_j x. Thus W_j=O(C_n delta_j). Let

    S_j=[[I,0],[W_j,I]].

Exact invariance of the q space makes the lower-left block of S_(j+1)^(-1) A_j^p S_j zero. Writing the resulting matrix as

    [[L_j,R_j],[0,B_j]],                                    (4.8)

direct block multiplication gives

    L_j=A_LL+A_LB W_j, R_j=A_LB,
    B_j=A_BB-W_(j+1) A_LB.                                  (4.9)

The last correction is O(C_n delta_j^2). Consequently B_j is the diagonal reference outward matrix on band i plus O(C_n delta_j), and its off-diagonal coefficient on that band's crossing plateau is precisely (4.7), up to o(delta_j). This verifies the signed coefficient AFTER taking the quotient; it is not inferred merely from a spectral analogy. All these matrices are continuous in the product of controls. For fixed i, the coordinate changes and their inverses have uniformly bounded norms by the fixed graph balls.

This quotient has dimension D_i at every later stage. No column outside this finite quotient is used in its scalar matching equations. In particular, it has no pairs which never cross: every pair crosses during each subsequent full label period. Couplings from other bands are already included in the exact matrices and their uniform remainder estimates.

### 4.5 Scalar estimates across a join

For a column label l of this quotient put v_l(j)=e_l+sum_(h!=l) u_hl(j)e_h, where |u_hl(j)|<=eta(j)^(1/8). Write B_j=diag(alpha_h(j))+E_j. Its exact scalar force is

    F_hl(j)=
      [E_hl+sum_(k!=l) E_hk u_kl
       -r_hl u_hl(E_ll+sum_(k!=l) E_lk u_kl)]
      /[alpha_l+E_ll+sum_(k!=l) E_lk u_kl],
    r_hl=alpha_h/alpha_l.                                   (4.10)

The denominator is positive for sufficiently late local thresholds. For each finite collection |F_hl|<=C_n delta. On the plateau of this pair's crossing nu, at z_nu=+/-1, it is

    z_nu eta(t_nu)^(3/4) m_hl/alpha_l+o(delta),               (4.11)

uniformly on all boxes. The terms with a column coordinate are O(C_n delta eta^(1/8)); the quotient correction in (4.9) is smaller still. Constants may depend on the band and collection.

Use the cut N_nu=ceil(t_nu). For log r changing from positive to negative prescribe the trial value zero at N_nu and propagate away in both stable directions. For its negative-to-positive crossings, propagate forward from the preceding zero cut and backward from the next zero cut, and form the difference D_nu of their arriving values. If the first interval starts at activation, use zero there when forward stable and backward propagation from its first zero cut otherwise. Reversing the ordered pair reverses these roles. There is exactly one mismatch and one control per double, including when the step begins precisely at the crossing.

These propagations are finite. A scalar interval between successive zero crossings lies in one stage, or in the last full old period, the connector, and the first full new period. No connector creates an old-band crossing, and every full period contains a crossing of each pair. At least two periods per stage prevent a sign interval from encountering two connectors. On the resulting finite compact collection, with local phase parameter s and sign-interval endpoints s_a,s_b,

    |log r_hl(s,b)|>=c_n min(s-s_a,s_b-s,1),                 (4.12)

and near either endpoint the reverse inequality holds with a finite constant. This is simple splitting at the endpoints and compactness away from them; b in [a,1] neither changes the zeros nor the sign. The finite phase length has positive lower and finite upper bounds. At activation the initial interval is a truncated sign interval. The constant collar can have fixed phase length and a positive spectral gap; all its constants remain finite. None of these statements requires periodicity across a connector.

Placing the collection late makes eta asymptotically constant over any of its sign intervals: their time lengths are O(C_n t^(3/4))=o(t). Summing (4.12) from an endpoint gives the stable-product upper bound C_n exp(-c_n eta m^2) until the interval's interior, followed by exponential damping. Thus the total Green weight for any stable propagation is at most C_n eta^(-1/2). With |F|<=C_n eta^(3/4), every trial coordinate has size

    |u_hl^trial(j)|<=C_n eta(j)^(1/4)<eta(j)^(1/8).           (4.13)

For clarity, the last strict inequality is a late-time requirement imposed separately for all the finitely many active bands; it is not a uniform bound in n.

At a mismatch, both arriving force sums enter D_nu with positive weights (the backward solution has a minus sign before subtraction). In a central window of theta_n eta_nu^(-1/2) steps on either side, the phase distance is O(eta_nu^(1/2)), so the window lies in the plateau and the weights are bounded below by a positive constant. Formula (4.11) contributes at least c_n eta_nu^(1/4) with the sign of the oriented control. All plateau contributions have that sign. Outside the plateau the weights have already crossed a fixed positive phase distance; they are at most C_n exp(-c_n/eta_nu). There are O(C_n/eta_nu) steps in the entire finite interval and each force is O(C_n eta_nu^(3/4)), so their total is bounded by

    C_n eta_nu^(-1/4) exp(-c_n/eta_nu)=o(eta_nu^(1/4)).

Orient each control once by its leading coefficient. We have proved

    D_nu|_(z_nu=1)>0,   D_nu|_(z_nu=-1)<0,                 (4.14)

with every other control and column variable free. This is the source Gaussian matching calculation on finite collections straddling joins. It supplies the needed extension rather than assuming a uniform gap or repeated type globally.

### 4.6 Choosing the schedule without a future uniform constant

We finish the scheduling argument explicitly. First fix all finite reference programs, collars, connectors, directions, and bands; this is a countable choice of finite data. For each stage n compute bounds for its interior and its two adjacent finite collections, restricted to the cutoffs already active on those portions. All required bounds above are finite. In particular the full-operator freezing argument gives an accuracy threshold for each prescribed finite accuracy; its assertion is uniform over arbitrary earlier histories satisfying the established whole-ball contraction. The graph contraction deficits and the finite local windows are fixed after these bounds. Existence of the graph itself requires only ball preservation and divergent total deficit; its sharper local estimate then uses those finite windows, not an unknown global constant.

Choose each stage's entry later than its interior thresholds, and its outgoing connector later than all thresholds for that connector and the next entry. Repeat the preceding program until these demands hold. This can be done at an integer number of full periods because integral eta dt diverges. The incoming thresholds can be fixed before this repetition count; no constant depends on how many earlier repetitions occur. Constant collars and full periods have time length comparable to t^(3/4), so logarithmic freezing/graph windows fit into their local collections after increasing these thresholds. The thresholds also guarantee contraction deficit at least one per active stage, and D_i eta^(1/8)<1/2 for each active quotient. The graph balls are fixed once for each cutoff, not shrunk during the iteration.

The radial envelope mass bound for stage n is at most 2C_n/sqrt(T_n), independently of how many repetitions are ultimately made. Allocate summable budgets to interiors and connectors separately and choose their entry thresholds accordingly. This proves (a) and all geometric requirements. The local formulas for b_t use a logarithmic window plus an exponentially small earlier contribution; b itself is in [a,1], which is sufficient for every spectral estimate. The eventual f can therefore be defined after the complete schedule without circular dependence on the controls or on a presumed decay rate for b-a.

Here are the additional growth thresholds in (c),(d). For fixed active i and one full label period of program n, subtract the label's phase mean from its reference frequency Theta=d(a^(-2)lambda). Its periodic primitive has a finite norm A_i,n. Integration by parts with s'=t^(-3/4) bounds its integral on ANY stage prefix [T,t] by

    C A_i,n (T^(3/4)+t^(3/4)+integral_T^t x^(-1/4)dx)
      <= C' A_i,n t^(3/4).                                 (4.15)

Choose entry so that this is at most 2^(-n)t for every i<=n. A connector's reference frequencies for an old fixed band have a finite upper bound; its fixed phase length yields a time length at most C_n t^(3/4). Delaying the connector makes its entire contribution, and every prefix of it, at most 2^(-n)t. Include collars in this connector budget (an activation collar gives only a finite initial contribution for its new band). The finite collection bounds for the derivative of Theta give a mesh error per unit time O(C_n eta); logarithmic multipliers have error O(C_n delta). Require both to be at most 1/n on stage n and its outgoing connector, for all active bands. The finite quotient and low-block bounds used below can also be imposed here. These are again only finitely many late-time requirements at each step. They coexist with arbitrarily many repetitions and with the curvature mass bound. This completes the construction claimed in (a)--(d).

## 5. One common selection of all controls

Take the product of the intervals [-1,1] for all crossing controls, and of the intervals [-eta(j)^(1/8),eta(j)^(1/8)] for all off-diagonal coordinates in every finite quotient, j>=J_i. This is a countable compact product of real intervals. Its trial map sends each column coordinate to the stable propagation just constructed, selecting the left arriving value at a mismatch cut. It sends each oriented control to

    clamp_[-1,1](z_nu-D_nu).

All trial coordinates lie in their intervals by (4.13). Each output coordinate is continuous: its finite stable propagation uses finitely many forces; each force depends continuously on finitely many column coordinates and on the exact quotient matrices; these matrices are continuous in the whole product of controls by the uniform graph-limit argument. This proves product continuity, even though a quotient matrix can depend on all future controls.

For completeness, fix all but the first N coordinates at their interval centers and apply finite-dimensional Brouwer to the first N output coordinates. Extend each such fixed point by the centers. A coordinatewise convergent subsequence exists by a diagonal subsequence argument. Continuity makes its limit a fixed point of every output coordinate. This proves existence without requiring a theorem for nonmetrizable products or a uniform finite-dimensional limit estimate.

At a fixed point, (4.14) excludes z_nu=1 and z_nu=-1: at either endpoint the clamped value moves strictly inside. At an interior fixed point the clamp identity forces D_nu=0. Hence the two arriving values agree at every matching cut, and the zero cuts and all other steps already satisfy the scalar recurrence. We obtain exact quotient lines

    B_j v_l(j)=sigma_l(j)v_l(j+1),
    sigma_l(j)=(B_jv_l(j))_l=alpha_l(j)+O(C_n delta_j)>0.      (5.1)

For fixed i their column matrix is invertible at each j by D_i eta(j)^(1/8)<1/2 (the operator norm of its difference from I is at most D_i times the entry bound). This same fixed point selects ONE control sequence and therefore ONE smooth metric for every band. Independence of the band equations is not asserted; their coupling through this shared metric is precisely why the common product fixed point is used.

## 6. Growth, lifting, and entire harmonic functions

### 6.1 Quotient growth at all logarithmic radii

Fix i and a label l in its quotient. Start with coefficient one at J_i and multiply the positive sigma_l(j) in (5.1), obtaining the exact quotient solution z_l(j). By construction,

    log ||z_l(j)|| <= C_i + sum_(m=J_i)^(j-1)
          d(b(m)^(-2)lambda_l(s(m))) + sum_m e_i(m),          (6.1)

where the logarithmic errors on stage n and its connector have magnitude at most 1/n. Therefore sum_m |e_i(m)|=o(j): any finite set of initial stages has finite total duration, while the remaining per-step bound is arbitrarily small. The column norms contribute a fixed bounded factor.

Because b>=a and d is increasing, replace the frequency in (6.1) from above by Theta_l=d(a^(-2)lambda_l). For each program n>=i its phase mean is at most m_i^*. On a stage prefix the discrepancy is bounded by (4.15) and the chosen 2^(-n)t budget. The connector and collar contributions have the same budget. Summing over all stages after an arbitrary fixed N bounds the total discrepancy up to time t by at most C sum_(n>=N) 2^(-n)t; the finitely many earlier completed stages contribute only a finite constant. Sending first t to infinity and then N to infinity proves

    limsup_(j->infinity) (1/j) log ||z_l(j)|| <= m_i^*.        (6.2)

The mesh errors are o(j) by the same per-unit-time threshold as in (6.1). This argument controls every stage prefix and connector, not just endpoints of complete periods. Since m_i^*<gamma_i, it gives ||z_l(j)||<=C_i,l exp(gamma_i j) for all j>=J_i.

### 6.2 Triangular lift with a strictly smaller low rate

The exact low block in (4.8) obeys

    ||L_j||<=exp(sqrt(C_*) (L_i+1)/a)+o(1)<=exp(beta_i)        (6.3)

for all j after increasing the schedule thresholds. The reference eigenvalues in the first Q_i ranks satisfy the stated uniform near-round bound, and local errors in (4.6),(4.9) can be made smaller than the fixed positive margin in (6.3), separately on each finite collection. Also ||R_j|| is bounded by a finite constant depending on i for all j>=J_i; one may make its local error at most one after activation. These requirements were included in Section 4.6. Finite initial terms could alternatively be absorbed in constants.

Set x_l(J_i)=0 and solve the finite exact recurrence

    x_l(j+1)=L_j x_l(j)+R_j z_l(j).

Because beta_i<gamma_i, its variation-of-constants sum gives

    ||x_l(j)|| <= C_i,l sum_(m=J_i)^(j-1)
                   exp(beta_i(j-1-m)) exp(gamma_i m)
                <= C'_i,l exp(gamma_i j).                   (6.4)

Thus the lift has the same subcritical rate; no cancellation or backward solution of the lower block is needed. In the full Hilbert space define its trace by applying the p graph embedding to S_j(x_l(j),z_l(j)). Equations (4.8) and (5.1) give exact inward consistency T_j w_l(j+1)=w_l(j). The embeddings have bounded norm for fixed i, so

    ||w_l(j)||_L2(mu)<=C_i,l exp(gamma_i j).                  (6.5)

### 6.3 Entire extension and pointwise growth

Each trace is smooth, since it is the inward restriction of the L2 boundary trace at the next larger ball. Solve the ordinary Dirichlet problem on every whole ball of radius e^j with trace w_l(j). The resulting harmonic functions agree on smaller balls by inward consistency and Dirichlet uniqueness. They therefore define a smooth entire harmonic function u_l on R3 with the single selected metric. The D_i functions for fixed i are linearly independent: their quotient traces at J_i form the invertible matrix of columns v_l(J_i). This does not require independence between different bands.

The source's whole-ball sectional L2 contraction also applies between noninteger radii, by the identical positivity, mean preservation, and Jensen argument. Thus (6.5) bounds the L2 norm of u_l on every logarithmic section by C exp(gamma_i t), after enlarging the constant by exp(gamma_i). On cylinders of a fixed logarithmic width, the harmonic equation has a uniformly elliptic divergence-form representation. The angular links have a common C0 comparison and fixed volume measure; a<=b<=1 and a<=f'<=1 give uniform coefficients and bounded density ratios on such a cylinder. Consequently the standard interior L2-to-sup estimate used in S `growth.tex` has a radius-independent constant. It requires no uniform high angular derivatives. Applying it on a width-four cylinder yields

    sup_(omega in S2) |u_l(e^t,omega)|<=C_i,l exp(gamma_i t).

Since gamma_i<k_i and radial distance is r=e^t, after absorbing the compact core this is |u_l(x)|<=C_i,l(1+d_g(0,x))^(k_i) at EVERY point. These are exactly the growth constants allowed in the frozen statement. We have proved

    dim H_(k_i)(R3,g)>=D_i>c(k_i+1)^2

for each i, on the ONE complete smooth metric g with Ric>=0, AVR=v, and Euclidean germ constructed above. The sequence k_i is strictly increasing and tends to infinity. This concludes the proposed author proof at the frozen full scope.

## 7. Strongest reduction and remaining review obligations

The finite high-band dimension count, angular transversality, retained double at any larger finite cutoff, rank averaging, source whole-ball contraction, finite graph transform, and scalar signed matching are credited inputs, not new claims. Colding--Naber already supplies the general slow-link geometric design principle. I130 supplies finite disjoint-band amplification; I133 supplies countable geometric scheduling and explains why normalized finite-prefix limits do not preserve the desired harmonic rank. Neither a fixed metric obtained merely by exhaustion nor an infinite matrix inverse is used here. The finite quotient flags and their product-continuous, nonuniform local estimates are the proposed additional operation. Their purpose is to make the finite source matching act simultaneously on countably many bands without a cutoff-uniform gap, with a triangular lift and stage-prefix growth estimates.

The primary Huang counting theorem requires a unique tangent cone at infinity; no such hypothesis is asserted here. Xu's three-circles propagation requires a degree outside the relevant union of tangent-cone spectral degrees, whereas these deliberately crossing high bands do not supply such a gap. Those results are not contradicted by removing their hypotheses informally. The source companion's finite-rank/finite-degree restrictions are likewise not promoted to an infinite-cutoff theorem.

This is an author-proof nominee only. It has no independent correctness or substantial-contribution disposition, no formal-support claim, and no acceptance/count implication. The main interfaces requiring adversarial review are: local whole-ball freezing uniformly over the scheduled pasts; inclusion of the terminal graph limits; the quotient's preservation of the signed coefficient; the two-neighbor scheduling bounds and product continuity; and the all-prefix growth estimate. They are argued above rather than listed as additional hypotheses. The read and search limitations are recorded separately and remain limitations of this research packet.
