# Quantitative interior repair: prefreeze derivation

PREFREEZE. These are feasibility calculations, not a frozen theorem, an author-proof nominee, a correctness grade, or a contribution grade. Source178 and its operative upstream proofs at the instructed pin are assumed true. The calculations below began after full canonical reading and the operative primary readings enumerated in the reading record; the final Tropp and late history reads preceded this extended write-up. No claim of literature novelty is made for the identities or estimates retained here.

## 1. The full prospective target, unchanged and not frozen

For every fixed integer d >= 3, there would be constants c_d > 0, n_d, and k_d and a deterministic algorithm which, for every even integer n >= n_d, outputs the full adjacency matrix of a simple nonbipartite d-regular graph on n vertices in at most n^{k_d} bit operations, and every eigenvalue on the orthogonal complement of the constant vector would satisfy

    |lambda| <= 2 sqrt(d-1) - c_d n^{-3/5}.

This is the full target evaluated here. It is not asserted, restricted to a subsequence, made conditional, or renamed as a successful result. Neither logarithmic girth (already developed in original structural r19) nor a routine quantitative extraction from the source is nominated. The target preserves every size, every fixed degree, simplicity, both spectral edges, and actual deterministic adjacency output. The work below does not close it.

## 2. A margin already paid by the source

Write q=d-1, s=2 sqrt(q), a=10^{-4}, e=n^{-2/3+a}, M=n^{1/3+10a}, and W=n^{-2/3+100a}; ceilings and fixed factors do not change these estimates. Fix one sign sigma. In the original eigenbasis let D_B be the positive bulk precision, R=D_B^{-1}, and U_B,U_E the bulk and near rows of the switch incidence matrix. Let C be the direct sum of sigma F, F=[[0,1],[1,0]]. The source proves that

    S=C^{-1}+U_B^T R U_B

has the prescribed inertia and bounded inverse, that the updated bulk is positive, and that the exact near Schur complement is at least c e I. It also proves

    max_p (R^2)_{pp} <= C W^{-1/2},
    ||U_E U_E^T|| <= C M/n.

Woodbury gives, for D'_B=D_B+U_B C U_B^T,

    (D'_B)^{-1}=R-R U_B S^{-1} U_B^T R,
    ||(D'_B)^{-1}|| <= C(W^{-1}+M W^{-1/2}).

Each column of U_B is a difference of two projected coordinate vectors; summing their squared R-images gives ||R U_B||^2 <= C M W^{-1/2}. The elimination map is

    L=(D'_B)^{-1} U_B C U_E^T=R U_B S^{-1} U_E^T,
    ||L|| <= C M/(sqrt(n) W^{1/4})=n^{-15a+o(1)}.

The bulk inverse is O(n^{2/3-40a}), whereas 1/e=n^{2/3-a}. Completing the square in the full precision form gives the sum of the near Schur form in z and the bulk form in y+Lz. Since ||L||=o(1) and the bulk gap is much larger than e, the full form is at least c' e (||y||^2+||z||^2). Do this for both signs. Thus the source's actual operations already yield a c_d n^{-2/3+a} interior margin. To make the algorithm output such a seed, strengthen its final acceptance test to B^T(r^2 I-A^2)B positive definite, with a rational r lying inside the proved inverse-polynomial margin and B having columns e_i-e_n. A good seed exists by the same estimates, the enumeration size is unchanged, and rational precision/inertia remain polynomial. This does not assert that the first seed passing the source's weaker strict-window test automatically has the stronger margin. This calculation closes the distinction between Schur positivity and a full spectral margin; it is an algebraic consequence and not a substantial nominee.

## 3. General scales and why changing exponents alone is inadequate

Return to the pre-repair graph supplied by the source. Its signed slacks x_i^sigma=s-sigma lambda_i obey x_i>-e/20 and

    sum_{x_i^sigma <= w} |v_i(p)|^2 <= C w^{3/2}   (w >= 2e).

For a prospective margin delta=n^{-c}, take a near cutoff W=n^{-w} much larger than delta, and M=n^m switches. All projectors exclude the constant vector. Dyadic summation of the displayed mass estimate gives, uniformly in p,

    P_E(p,p) <= C W^{3/2},
    R(p,p) <= C,   (R^2)(p,p) <= C W^{-1/2},
    Tr R^2 <= C n W^{-1/2},   ||R|| <= 1/W.

The R(p,p) estimate follows by summing C(2^j W)^{1/2}; the R^2 estimate follows by summing C(2^j W)^{-1/2}. The excluded negative slacks are in E. This use of the mass bound does not assume a new local law. A cutoff avoiding the finite spectrum can be selected within [W,2W].

The source tilt over all modes with x_i^tau < t_tau, t_tau in [2delta,3delta], requires a normalizing size J >= C n delta^{3/2}. Its useful mean bias per repaired mode is of order 1/(Jn), hence total bias M/(n^2 delta^{3/2}). Making it comparable to delta requires

    m >= 2 - (5/2)c.

The source's Frobenius-only near and bulk certificates would require

    sqrt(M) W^{3/2}=o(delta),
    M^2/(n^{3/2} W^{1/4})=o(delta).

Equivalently w>(m+2c)/3 and w<6-8m-4c. Even before conditioning errors, these require c>64/97 when m is minimal. At c=3/5 they cannot both hold. This is a limitation of those simultaneous estimates, not a graph impossibility result. At the source's literal exceptional fraction n^{-1/10}, the conditioning estimate M n^{-1/10} W^{3/2} is another cost. Merely retuning the source's small constants therefore does not establish the full prospective target.

The concrete scales used below are

    delta=n^{-3/5},  W=n^{-49/100},  M=ceil(K sqrt(n)),
    J=C_J n delta^{3/2}=C_J n^{1/10}.

C_J is a sufficiently large fixed constant depending on d and the local-mass constant; then K is a sufficiently large fixed constant compared with C_J. The tilt remains bounded and positive, and its mean bias can exceed the required fixed multiple of delta. Both constants are independent of n. This is not yet a graph construction.

## 4. An exact mean identity before admissibility restrictions

For an oriented edge g=(u,v), write z_i(g)=(v_i(u),v_i(v))^T. Under the uniform oriented-edge law,

    E z_i=0,
    E z_i z_j^T=1_{i=j} M_i/n,
    M_i=[[1,lambda_i/d],[lambda_i/d,1]].

For two independent oriented edges g,j set U=[e_u-e_x,e_v-e_y] and

    K_sigma=(1/(d-2))*[[-s,sigma d],[sigma d,-s]],
    B_sigma=U K_sigma U^T.

Use the source's two-sign density, with the larger sets T_tau just specified:

    f(g,j)=1-(2n/(B_* J)) sum_tau sum_{i in T_tau}
                       z_i(g)^T K_tau z_i(j).

Cauchy--Schwarz and the local-mass bound make |f-1| <= C n delta^{3/2}/J. Choosing C_J large makes, for example, 1/2 <= f <= 3/2. Each marginal remains exactly uniform because every z_i has mean zero. The sets T_+ and T_- are disjoint for large n.

For every pair of nonconstant eigenvectors, not only the near ones, direct expansion gives

    <v_i,E_f B_sigma v_j> = 1_{i=j} [
      -4 x_i^sigma/((d-2)n)
      + (4/(B_*Jn)) sum_tau 1_{i in T_tau}
                    Tr(K_sigma M_i K_tau M_i) ].

The terms with both z-factors from the same edge vanish against the other edge's mean; the two mixed terms use the displayed orthogonality twice. There is no eigenvalue-spacing assumption. The constant vector is annihilated by every U. Consequently E_f B_sigma commutes with A, and in particular

    P_E (E_f B_sigma) R = R (E_f B_sigma) P_E = 0.       (A)

For the same-sign modes in T_sigma the trace in the positive correction is bounded below by a positive d-dependent constant: M_i is positive definite with eigenvalues uniformly bounded away from zero near sigma s, and Tr(K_sigma M_i K_sigma M_i) is the squared Frobenius norm of M_i^{1/2} K_sigma M_i^{1/2}. The mean near precision is therefore at least c delta after K is chosen large enough; outside T_sigma the original slack is at least 2delta and its relative baseline loss is O(M/n)=o(1). The opposite-sign tilt does not meet this near subspace.

Identity (A) is exact for this unrestricted tilted law. It is generally false after rejecting atypical edges, close endpoints, or collisions. It cannot silently be reused for the eventual graph-realizable law.

## 5. Near concentration improves the first source estimate

For independent draws from f, put H_r=P_E B_r P_E. Local mass implies

    ||H_r|| <= C W^{3/2},
    E(B_r P_E B_r) <= C W^{3/2}/n * I.

Indeed U_r^T P_E U_r <= C W^{3/2} I, ||K_sigma|| is fixed, and E U_r U_r^T <= C/n I by bounded density (in fact the marginals are uniform). Thus the variance of H_r-EH_r is bounded by C W^{3/2}/n. The bounded matrix Bernstein inequality, applied to both signs of the centered sum, gives with probability 1-n^{-D}, for any fixed D after enlarging constants,

    ||sum_r(H_r-EH_r)||
       <= C_D [sqrt(M W^{3/2} log(n)/n)+W^{3/2} log(n)].

The actual theorem and proof mechanism used here are Tropp's Theorem 6.1, Lemma 6.7, and the cgf/trace-Laplace steps in Sections 3.5-3.6 of arXiv:1004.4389v6. This is a standard primary operation, not a discovery claim. At the concrete scales the leading power is n^{-247/400}=n^{-0.6175}, which is o(delta). The source's weaker pairwise/Frobenius estimate was not an inherent obstruction.

This fully independent probability calculation by itself does not give a polynomial deterministic search. That distinction is retained below.

## 6. The first off-diagonal Schur correction is a centered kernel

For distinct draws define Y_rs=P_E B_r R B_s P_E and Z=sum_{r!=s}Y_rs. By (A), E(Y_rs | B_r)=E(Y_rs | B_s)=0. Let A_0=E(B_r P_E B_r), a positive matrix bounded by C W^{3/2}/n I. Independence and cyclicity of trace give

    E ||Y_rs||_F^2 = Tr(R A_0 R A_0)
                  <= C W^3/n^2 * Tr(R^2)
                  <= C W^{5/2}/n.

In the second moment of Z, terms indexed by different unordered pairs vanish: when there is a singly occurring index, condition on the others and use (A). The two orders of the same pair are bounded by Cauchy--Schwarz. Four-wise independent draws suffice for this calculation. Therefore

    E ||Z||_F^2 <= C M^2 W^{5/2}/n,
    (E ||Z||_F^2)^{1/2} <= C M W^{5/4}/sqrt(n)
                          =n^{-49/80+o(1)}=n^{-0.6125+o(1)}.

Markov gives ||Z||=o(delta) with probability tending to one, with a small power to spare. This controls the FIRST off-diagonal inverse correction, not the full inverse or the diagonal blocks.

## 7. A multiscale bound for the off-diagonal higher remainder

Let Delta_off be the 2M by 2M block matrix with blocks U_r^T R U_s for r!=s and zero diagonal. Let U_E denote the horizontal concatenation of P_E U_r. Set

    T=Delta_off K U_E^T,
    T_r=sum_{s!=r} U_r^T R B_s P_E.

An immediate trace bound loses too much: E||T||_F^2 <= C M^2 W/n, of power n^{-0.49}. Even though ET^T T <= C M^2/(n^2 sqrt(W)) I on E, this expectation is not a bound on the realized operator norm. Here is a stronger integrated estimate, still for independent unrestricted draws.

For two disjoint index sets A,B of comparable size h, define Q_B=R sum_{s in B} B_s P_E. Identity (A) centers every summand. The bounds above imply

    ||R B_s P_E|| <= C sqrt(W),
    max(||E P_E B_s R^2 B_s P_E||,
        ||E R B_s P_E B_s R||) <= C/(n sqrt(W)).

For the first inequality use ||R U_s||<=C W^{-1/4} and ||U_s^T P_E||<=C W^{3/4}. The first variance bound uses U_s^T R^2 U_s<=C W^{-1/2}I; the second uses A_0<=C W^{3/2}/n I and ||R||<=1/W. Matrix Bernstein, using self-adjoint dilation, gives

    ||Q_B||^2 <= C_D log^2(n) [h/(n sqrt(W))+W].

A better coordinate-row bound is essential. Positivity and R(p,p)<=C give |R(p,q)|<=C, hence

    ||e_p^T R B_s P_E|| <= C W^{3/4},
    E||e_p^T R B_s P_E||^2 <= C W/n.

Vector Bernstein (the same rectangular dilation) and a union bound over p give

    max_p ||e_p^T Q_B||^2
       <= C_D log^2(n) [h W/n+W^{3/2}].

Condition on the draws in B. The draws in A are independent of Q_B. The rectangular block V_AB with rows U_r^T Q_B, r in A, satisfies

    E(V_AB^T V_AB | Q_B) <= C h/n * Q_B^T Q_B.

Every positive summand Q_B^T U_r U_r^T Q_B is bounded by a constant times the maximum coordinate-row squared norm. Applying bounded Bernstein to the centered sum, with variance bounded by its maximum-summand size times its mean, and using sqrt(ab)<=a+b, proves

    ||V_AB||^2 <= C_D log^C(n)
             [h^2/(n^2 sqrt(W)) + h W/n + W^{3/2}].       (B)

The bound holds simultaneously for polynomially many specified disjoint pairs of groups, by a union bound; it does not assert independence between all those events.

Partition the M indices by a balanced binary tree. Each ordered pair r!=s lies in exactly one pair of sibling groups at its first separating level. Retain coarse levels down to group size H=ceil(n^{3/8}); collect all remaining pairs within groups of size O(H) in T_fine. At a coarse level of group size h there are O(M/h) blocks V_AB stacked in the row direction. Its squared operator norm is at most the sum of the squared block norms, so (B) yields

    C log^C(n) [M h/(n^2 sqrt(W)) + M W/n + (M/h)W^{3/2}].

The triangle inequality across O(log n) levels only changes logarithmic factors. For the fine part, conditional centering of distinct s at a fixed row r and the trace calculation give

    E||T_fine||_F^2 <= C M H W/n.

Thus, outside an event of probability tending to zero, the coarse part is bounded by

    ||T_coarse||^2 <= C log^C(n)
        [M^2/(n^2 sqrt(W)) + M W/n + (M/H)W^{3/2}],

while Markov bounds ||T_fine||^2 by n^epsilon M H W/n for any fixed epsilon>0. At the concrete scales the four powers are respectively

    -0.755, -0.99, -0.610, -0.615+epsilon.

Take 0<epsilon<0.01. Consequently ||T||^2=o(delta). The argument does not need a conjectured matrix concentration inequality for a dependent cubic array: disjoint-block conditioning, ordinary Bernstein, and a fine-scale second moment suffice.

This is a durable feasibility improvement over the source's all-pairs Frobenius estimate. It is not a completed graph theorem. In the exact identity

    S^{-1}=K-K Delta K+K Delta S^{-1} Delta K,

it bounds the off-diagonal contribution to the last term ONLY if S^{-1} is uniformly bounded, the required inertia is correct, and the diagonal-error terms are also controlled. Those conditions have not been proved at these scales. In particular, a small near sandwich is not a proof that the bulk stays positive.

## 8. What the strongest integration still does not pay

### 8.1 Bulk inertia and diagonal blocks

The ideal block S_0=K^{-1} has one positive and one negative eigenvalue per switch. Write Delta=S-S_0. Its diagonal includes the errors of the two original edge blocks and their within-draw cross blocks; Delta_off is the inter-draw part above. We need a graph-realizable collection for which S has the same inertia as C^{-1}, ||S^{-1}||=O(1), and the FULL near correction, including diagonal and mixed terms, is o(delta) or controlled relative to the positive slack.

A crude global bound ||Delta_off||_F has size M/(sqrt(n)W^{1/4})=n^{0.1225}, so it gives no inertia information. The coherent covariance scale M/(nW)=n^{-0.01} is favorable, but it is not a proof of an off-diagonal Gram norm bound: rare close endpoints and strongly correlated Green entries have to be handled. Treating the cubic sandwich estimates as a substitute for inertia would be invalid.

The source's proven typical-block error n^{-0.024} (the repair algorithm accepts a slightly looser error) gives a near error of size at most n^{-0.024} M/n=n^{-0.524}, which is larger than delta. Its proof uses an n^{-0.04+o(1)} short-path remainder and a low-rank frozen-boundary correction. The latter has a useful total squared-row budget O(l_0 polylog n), but the literal typical-edge conclusion alone does not pay the stronger weighted requirement. Increasing its exponent without redoing the actual path and boundary accounting is not legitimate.

### 8.2 Admissibility restriction is a mathematical operation

The source restricts to typical edges at cost O(n^{-0.1}). Its original bound for the resulting near-mean error is

    C M n^{-0.1} W^{3/2}=n^{-0.335+o(1)},

far larger than delta here. Moreover restriction destroys (A); the zero conditional means used in Sections 6-7 are then no longer exact. Restoring them or bounding all leakage terms is necessary.

There is a stronger compatible reduction than this crude estimate. Let D_E have diagonal delta+max(x_i,0) on E, and let Q_E=P_E D_E^{-1/2}. Dyadic mass summation gives max_p ||e_p^T Q_E||^2<=C sqrt(W); the contribution below delta is O(sqrt(delta)), including the original O(e) negative slacks. If a bad oriented-edge set has incident vertex set of size b, then bounded density and uniform edge marginals give

    ||D_E^{-1/2} E[P_E B P_E 1_bad] D_E^{-1/2}||
         <= C [b sqrt(W)/n + b/(n^2 delta)].

The estimate follows by bounding the absolute quadratic form of B by C U U^T, summing the at most O(b) bad edges, and using the coordinate-row bound; either of the two edges can be bad. The second term comes from the other edge when just one edge is bad. At the concrete scales n delta sqrt(W) grows, so that term is smaller than the first. Multiplying by M gives O(p b sqrt(W)), p=M/n. Thus a geometrically specified bad set of O(n^{2/3} polylog n) vertices would cost n^{-47/600+o(1)}=o(1) in this relative norm (the small source l_0 exponent is harmless). This shows why a uniform delta-norm estimate is unnecessarily pessimistic. It does NOT establish the needed size and weighted control for every source atypical set, nor control all leakage in (A), nor the diagonal inverse errors. The supplied fraction n^{-0.1} permits b=O(n^{0.9}), for which the relative estimate still fails.

One possible paid input is the frozen correction's trace budget; one still unpaid input is a sufficiently sharp average/weighted endpoint-block error, including the actual nonbacktracking remainder, at the enlarged near window. No such estimate is claimed from the name 'tree-like'.

### 8.3 Collisions and deleting switches

For M=K sqrt(n), the expected number of shared-endpoint or forbidden short-incidence pairs is O(K^2), not o(1). Thus the source's o(1) collision union bound cannot be quoted unchanged. Bounded-density independent draws do imply that, with probability tending to one, deleting at most n^eta offending switches makes the elementary switches vertex-disjoint and removes a fixed finite set of adjacency obstructions, for any fixed eta>0: the number of pair obstructions has bounded expectation, and a switch contains an internally degenerate or adjacent-endpoint obstruction with probability O(1/n). Delete an incident switch for each obstruction. Taking eta<0.1 makes their direct near update at most C n^eta W^{3/2}=o(delta).

This does not close the construction. Deletion changes S, its diagonal blocks, the whole inverse, and all previous cancellations. The full coupled inertia and remainder estimates must survive the deletion, or be established on the resulting law. An estimate for the linear near update is insufficient. Graph-distance exclusion at a growing radius carries an additional q^r factor and has not been smuggled into the constant-radius count.

### 8.4 Finite deterministic realization and bit complexity

The source's rational spectral functions, avoiding cutoffs, and exact quadratic-field/rational positivity tests remain compatible with any fixed inverse-polynomial windows considered here. Computing or certifying a candidate graph is not the same as finding one in polynomial time.

The centered second moment in Section 6 needs only four-wise independence. Other calculations in Section 7 used full-independence Bernstein, so the source's pairwise-independent affine seeds do not establish them. A fixed high even-moment replacement, together with a fixed-wise independent polynomial over a polynomial-size finite field, could still permit polynomial enumeration: a fixed number of field coefficients gives n^{O(1)} seeds. Such a replacement must prove all relevant certificates, including the nonlinear inertia and conditioning effects, on that support. It is not supplied here. Enumerating all independent switch sequences is exponential and is not offered as the target algorithm.

## 9. Outcome

The stronger attempt did not stop at the original Frobenius obstruction: the source margin was extracted, the larger tilt's mean was computed on the full eigenbasis, the first off-diagonal correction was centered exactly, ordinary matrix concentration improved the near fluctuation, and a coarse/fine partition controlled the unconditioned off-diagonal higher remainder. The unresolved operation is their simultaneous compatibility with admissible-edge diagonal control, bulk inertia, and a polynomial finite search. The target in Section 1 remains unchanged and unproved. No exact theorem was frozen and no author-proof nominee is submitted. These notes make no general impossibility or exhaustive priority claim.
