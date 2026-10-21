# Weighted binary-capacity exploration: strongest integrated reduction

PREFREEZE. No theorem frozen, no full author-proof or supporting nominee, no independent grades. These are research calculations, not a manuscript or a new-to-literature claim. The desired algorithm in note01 has NOT been proved. This round develops Source114, with its Source115 counting companion as a transitive input. It does not revisit the paid r153 family.

## 1. Exact problem interface and already available operations

Let r1,r2 be arbitrary normalized nondecreasing integral submodular functions on E=[n], with r1(E)=r2(E)=R, supplied by exact rank-value oracles; R is binary. Write P=B(r1) intersect B(r2). For each e let a_e(0),...,a_e(R) be positive rational numbers with log-concave successive values, accessed by an exact value oracle. A supplied integer L bounds the binary length of each numerator and denominator. The exploratory sum is

    Z_a = sum_{x in P intersect Z^n} product_e a_e(x_e).

The question concerns a single algorithm polynomial in n, the binary encoding of R and accuracies, L, epsilon^-1 and log(delta^-1), with bounds on EVERY execution. L is a numeric bit-length bound, not merely log L. No representation by exponentially long weight tables is presumed. No frozen theorem is being weakened to this question; it was the initial weighted exploration. Feasibility of P, the R=0 singleton and n=0 case are already paid. Positive weights mean exactly the same zero test as in Source114. Zero weights with interval support were not developed as an extra claimed scope.

For analysis divide each a_e by 2^L. This known scaling has polynomial bit length. The normalized weights satisfy

    exp(-A) <= a_e(k) <= 1,   A=2L log 2.

Restoring the product scaling costs nL bits. Extend log a_e linearly between integer points on [0,R]; it is a concave function taking values in [-A,0]. All subsequent uses of concavity refer to this specified interpolation.

The actual Source114 introduction/main theorem and ALL seven mathematical sections were read. Its binary compression, integrality, tight-set chains, exact rank penalties, balanced summation, source homothety, tree coordinates, regularization, paired factorial lifts, complete capped counting and evaluation arguments are credited, not audited. The actual matroid companion's statement, paired reduction, quadratic proofs and complete transport construction were read. The cell-bounded companion's complete integer-signature, binary-signature and transport/variance/trace proofs were read, including the full-domain and two-lift clauses. Merely retaining all companion files does not imply reading them all.

Chen–Liu, arXiv2610.06724v1, proposition integer-weight-intersection, already counts products of arbitrary log-M-concave integer weights with unary capacities, and explicitly states the separable log-concave specialization. Its actual reflection, polarization and factorial proof is paid. Its homogeneous convolution proof, curvature/Bochner proof, field optimization, limiting induced chain and bit implementation were read. Branden–Huh arXiv1902.03719v8 supplies the actual normalized-coefficient and polarization proofs; their selected internal proof chain was read, with transitive limits in note03. Thus separable weights, fractional powers, weighted unary counting and clone multiplicity cancellation are NOT novel residuals.

## 2. Weighted signatures and root-direction interpolation are paid

Here is an explicit compatibility check with the pinned integer proof, beyond assuming ordinary log-concavity suffices. For a physical coordinate e fed by a group G_e of count coordinates in one consistent orientation, multiply the source rank factor by a_e of that grouped physical value. In a normalized two-addition or two-removal matrix, the multiplier is one between distinct groups. Within G_e it is

    rho_e = a_e(v_e) a_e(v_e+2 sigma) / a_e(v_e+sigma)^2 <= 1.

Before box-boundary diagonal corrections, the source rank normalization within G_e is a constant q_e in [0,1]: its interchangeable copies are either all parallel nonloops (q_e=exp(-2H)), or the relevant two-copy increments add (q_e=1). The source parallel-class proof includes loops and reflected removals. Interchangeability implies that a group with two independent copies cannot have just one copy parallel to another retained group. Consequently

    J-Q_new = (J-Q_rank) + sum_e q_e(1-rho_e) 1_{G_e}1_{G_e}^T >= 0.

Discarding invalid single steps and setting invalid repeated-step diagonals to zero preserves this inequality. It also holds at every nonnegative power. For one count coordinate per physical coordinate this reduces to adding a nonnegative diagonal. Factors for the two rank systems live on disjoint count sets, as in the source difference-pair encoding, so their complements form a direct sum. This does NOT assert closure under products of arbitrary normalized-signature factors on overlapping coordinates.

To handle weights zero outside [0,R], work first on each finite proof box with positive log-concave extensions: to the left use a linear log slope at least H and at least the first interior slope; to the right use a slope at most -H and at most the last interior slope. Let H tend to infinity after the finite balanced sums. The interior values stay fixed and the outside values tend to zero. The source global interpolation before taking limits prevents internal support gaps. This is a proof device, not a large algorithmic table.

It follows by the source difference-pair encoding and balanced summation that

    Y_a(d) = sum_{x1 in B(r1), x2 in B(r2), x1-x2=d} a(x1)

is log-concave along every integer line d0+t(e_j-e_k), with interval positive support. All sums here are over integer points. The same conclusion holds with either rank replaced by an expanded integral submodular rank and a(x1) still zero outside [0,R]^n. No claim is made that the hard common-base generating polynomial is Lorentzian; i29's actual two-common-base example rules out that shortcut.

Use the Source114 partitions and scales with

    N=10^10+n+ell+L+ceil(epsilon^-1), K=N^5,
    S=N^5000, W=N^20000, T=W/N^300,
    h=S/N^50, theta=N^-200.

This is feasibility bookkeeping, not frozen constants for an algorithm. Every source geometric statement remains applicable to these larger scales. For any integral difference with zero superblock sums and l1 norm <=S/2, original geometric feasibility and integrality give at least one pair; its normalized weight is at least exp(-nA). The coarse point count gives Y_a<=exp(K). Thus log Y_a lies in [-nA,K] throughout the source positive region. Replace K by K+nA in the source secant estimate. Since nA<<K, all displayed small-star shift and tail comparisons retain the same ample N^-8 accuracy budget after increasing harmless numeric constants. The identical argument applies to expanded ranks, keeping weights zero outside the original first-system box.

This pays the full return-free discrete shift interpolation required here; an assertion that weighted endpoints automatically destroy the source shift comparison would be wrong.

## 3. Weighted expansion: a direct cell argument closes the steep-weight issue

Let B_i^+=B(ri)+Delta_i be exactly the source expansions. Define Z_a^+ by counting common expanded integer points, weighting by a(x) and declaring a(x)=0 outside [0,R]^n. Then Z_a<=Z_a^+.

Apply the source refinement independently to the two systems at each common superblock-total vector. Fix one pair of terminal slices, with witnesses a1*,a2*. The source supplies |ai*-c|_infty<=N^60 S and slack >=S on every rank inequality cutting a terminal part. Denote a pair of integer cell anchors by p=(p1,p2). Cells use the source free coordinates, retaining all but one coordinate per terminal part; each cell has measure one and physical sup displacement <=2n. In dimension zero use measure one.

For z in an expanded anchored cell, put H(z)=(1-theta)z+theta a*, and let y be its containing cell's anchor. The SOURCE proof already shows y belongs to the corresponding ORIGINAL slices, and H is injective with Jacobian (1-theta)^d, d<=2n. Write

    y_i = (1-theta)p_i + theta ai* + delta_i,
    |delta_i|_infty <= 4n.                                  (1)

If a terminal part is a singleton {e}, its physical coordinate is fixed throughout the cell, so delta_ie=0 and p_ie=y_ie=ai*_e. If its part has at least two elements, both {e} and E minus {e} cut that part. The source slack implies

    S <= ai*_e <= R-S.

For the first system, assuming a(p1)>0, set b_e=a1*_e+delta_1e/theta on the variable coordinates, and b_e=p_1e on fixed singleton coordinates. Since theta S>=4n, every b_e lies in [0,R]. Equation (1) says y1=(1-theta)p1+theta b. Concavity of the interpolated log weight now gives

    log a(y1) >= (1-theta)log a(p1)+theta log a(b)
               >= log a(p1)-theta nA.                       (2)

No Lipschitz estimate is used; b is allowed to depend on the cell point. Thus steep but bounded positive log weights are covered by the SAME source homothety. Anchors with zero weight contribute nothing.

The full-star weight is omega(d)=exp(-sum_{nonroot j}|d_j|/h). Applying (1) to the two systems and the triangle inequality gives

    omega(y1-y2) >= omega(p1-p2)
       exp[-theta (2n N^60 S)/h - 8n^2/h].                   (3)

Using piecewise CONSTANT weights on the cells, integrate (2),(3) over the expanded union. The image under H lies in the original union. Hence each pair of terminal slices has expanded weighted mass at most its original mass times exp(E), where

    E = theta nA + theta (2n N^60 S)/h
        +8n^2/h - d log(1-theta).                           (4)

All terms are negligible compared with N^-8 at the displayed scales. This comparison remains valid if the expanded first-system anchors outside [0,R]^n are omitted; their weight is zero. Fixed coordinates and zero-dimensional slices were handled above, not discarded.

Sum over the source subdivisions and common totals, then apply the weighted shift-average comparison of section2. This gives a small relative weighted expansion error with the same structure as the source result. This is a fully derived COMPATIBLE COMPOSITION of source geometry and elementary concavity, not a new substantial nominee. It rules out stopping at a mere steep-weight objection.

## 4. What remains when forming the port weights

The source tree-coordinate map is exact integral linear algebra, with coefficients at most 10(n+1), and keeps lattice multiplicity one. Inserting a(X1(u,z)) into the discrete port proxy preserves its lower comparison on original pairs. On violations beyond T, weights at most one give the same tail bound exp(K-lambda T), now divided by Z_a>=exp(-nA); increasing the coarse exponent budget pays this as well. Its upper comparison uses section3. Thus the DISCRETE weighted proxy is compatible at this stage.

The original next step replaces the free sum by a positive integral I_G, using a tiny joint Lipschitz bound L0=N^330/W. It then smooths over b0=W/N^400 and adds curvature alpha=N^-100/W^2. The actual source proof controls both signatures at EVERY annealing power, on the ENTIRE enlarged box slice, via

    error <= s [10 A3 +100(A2+alpha+4A3)^2
                        +10(A2+alpha)/M^2],
    2n error < s alpha/2.

Its pointwise mass error uses L0 b0<<1; the quadratic mass loss uses alpha times the squared port range. Those two requirements concern one common positive model and cannot be checked on different substitutes.

With the new weights, interpolated -log a(X1) is convex on its physical box. Marginalization would preserve continuous log-concavity. However, literal insertion also imposes a hard physical box and can make auxiliary port integrals vanish. Positive convex extensions are possible, but their slopes need not have the source tiny L0; nor has a relative comparison for their smoothing on ALL auxiliary profiles been established. Replacing an exact rational weight by an interpolated real-log integrand also needs a bounded evaluator with proved mass and encoding bounds. Ordinary log-concavity alone does not establish the source integer signatures.

For a precise local illustration, let F(z)=2^{-(z1-z3)^2} on a box allowing all two-step changes. It is positive and continuously log-concave. Its normalized addition matrix at any display is

           [1/4  1  4  ]
    Q =    [1    1  1  ].
           [4    1  1/4]

The antisymmetric direction (1,0,-1) has eigenvalue -15/4. On span{(1,0,1),(0,1,0)} its quadratic matrix is [[17/2,2],[2,1]], positive definite (determinant9/2). Therefore Q has TWO positive eigenvalues. Positive diagonal congruence transfers this to the unnormalized integer test. This is an exact illustration of why generic mixed-sign affine log-concavity is insufficient; it is NOT claimed to be an attainable obstruction for every refined source port construction, and NOT evidence of a new contribution.

The actual cell-bounded companion offers a stronger alternate operation than generic smoothness: it imposes nonroot equations as limits of positive laminar factors and sums all large cell pairs at balance BEFORE any signature claim. Unary log-concave entry weights fit its laminar model. For arbitrary submodular constraints the retained port-total equations and rank factors are not automatically a common laminar system. For example the lifted relation u_D=K_D-x(D) makes an across-part move alter two physical coordinates and two port coordinates; it is not simply a grouped argument of a single base rank. I have not constructed an exact positive paired model that both retains those port equations and has the full signature/evaluation contract. I do not infer impossibility from this observation, and I do not restrict the original arbitrary ranks to partition ranks as a substitute.

## 5. The primary clone route can be compressed exactly, but time is still unpaid

To test the strongest primary composition rather than dismiss unary encoding, set capacities c_i (e.g. R for each coordinate), C=sum c_i, and original integer weights mu(x)=1_{B(r1)}a(x), nu(x)=1_{B(r2)}. Both are log-M-concave by the actual primary exchange argument. The primary lifted subset weights are

    muhat(S)=mu(x) product_i (c_i-x_i)!/c_i!,
    nuhat(T)=nu(c-y) product_i (c_i-y_i)!/c_i!,

where x_i=|S intersect U_i|, y_i=|T intersect U_i|. In its soft pair law choose common scalar overlap penalty t and clone-symmetric fields z_i. Also retain h_i=|S intersect T intersect U_i|. Feasibility is

    max(0,x_i+y_i-c_i)<=h_i<=min(x_i,y_i),
    sum x_i=R, sum y_i=C-R.

All labeled pairs in an orbit have the same weight. The orbit's unnormalized mass is exactly

 mu(x) nu(c-y) product_i [
   c_i! / (h_i! (x_i-h_i)! (y_i-h_i)! (c_i-x_i-y_i+h_i)!)
   * (c_i-x_i)! (c_i-y_i)!/(c_i!)^2
   * t^{h_i} z_i^{x_i+y_i} ].                              (5)

For complement pairs y=c-x,h=0, the bracket becomes z_i^{c_i}/c_i!. Thus summing these orbits returns Z_a times the known product z_i^{c_i}/c_i!, with NO binomial multiplicity left. Equation (5) also retains all overlap orbits, rather than replacing them by the hard-intersection support.

The source generator can be lumped, since simultaneous permutations inside each U_i preserve its rates. Here is the exact S-update formula. A deletion in group i from membership type (S=1,T=b) has multiplicity m_i^{1b}, where (m^{11},m^{10},m^{01},m^{00})=(h,x-h,y-h,c-x-y+h). Delete it and write x'=x-e_i and m' for the resulting four counts. The conditional reinsertion denominator is

    D(x')=sum_j (c_j-x'_j) z_j muhat(x'+e_j).

The aggregate rate for reinserting into group j with T-bit b' is

    m_i^{1b} t^{-b}
       * m_j'^{0b'} z_j muhat(x'+e_j)/D(x').                (6)

Update h_i by -b and h_j by +b'; y stays fixed. Include same-group returns, and discard orbit-self terms only when forming the off-diagonal generator. The T-update is symmetric with its own lifted weight. Each orbit has O(n^2) move descriptions. Consecutive factorial ratios simplify to products/quotients of numbers <=C; exact rank membership and positive weight ratios have binary-size queries. One need not enumerate C labels merely to describe or update the orbit.

But this is NOT a poly(log R) mixing proof. The actual primary field theorem chooses t=1/(256 C^2), coefficient-gap B=2C+ceil(log2(range(muhat)range(nuhat))), and uses clone-count noise/gradient and rate bounds. Lumping preserves the continuous-time Poincare inequality, but the exhibited uniformization has total rate at most C/t; the original iteration and field-encoding guarantees still involve C. Symmetrizing fields does not by itself improve those estimates. The orbit partition function (5) also cannot be naively evaluated using all factorials of binary-large arguments within polynomial output space. Ratios can be short while normalizers are not. A capacity-independent multiscale jump simulation or a different convergence/field analysis was NOT derived.

## 6. Exact remaining obligation and disposition

The strongest composition reached weighted difference interpolation, a full weighted cell homothety with explicit error (4), and the discrete weighted port proxy; independently it reached the exact orbit law (5) and lumped rates (6) for the primary algorithm. These are paid reductions and explanatory calculations, not submissions.

What is unpaid is a SINGLE binary-size positive compressed model for the weighted target that simultaneously (i) approximates its whole mass relatively, (ii) supplies both full-domain integer signatures at all powers or an alternative proved primary curvature contract, and (iii) has bounded evaluation/simulation cost and precision polynomial in the ORIGINAL binary input on every execution. The demonstrated homothety is only a mass comparison and cannot certify those remaining algebraic/evaluation properties. The exact orbit model is only a state-description compression and cannot certify those time bounds.

No viable full theorem was obtained, so no freeze occurred and there is no nominee. Neither the matrix example, an unsupported signature assumption, a unary restriction, a partition-rank specialization, an entropy/projection relabeling, nor a conditional algorithm is submitted instead. No universal impossibility, exhaustive search, priority or current-open assertion is made. All protected original scopes and dispositions stay unchanged; parent alone integrates and independently reviews/counts.

## 7. Late original r57 read: the weighted binary-table interface is already paid

Chronology matters: the second primitive-alias scan, after the calculations above and the finite diagnostic, found the actual completed r57 `weighted-interface.md`. I then read its ENTIRE proof and i152's W152 scope, and subsequently the ENTIRE Source115 `scales.tex` and `evaluation.tex` bodies. This is a late strengthening of the comparison, not a pre-existing clearance claim. The old I152 large-cell objection is not an unpaid target: r57 repairs it at the unchanged W152 scope. No table-specialized result is submitted here.

The actual r57 operation first approximates log activities with precision inverse in the binary-encoded total capacity, then uses exact minimum-cost-flow duality to write the objective gap as a sum of nonnegative reduced-cost terms on the physical box. Truncating each term at K=O(log(number of tables)+log(delta^-1)) retains a COMMON optimum and loses at most delta relative mass. Retightening preserves jointly feasible endpoints. The maximum-capacity forest gives |r_e|b_e<=K and a uniform bound |g|<=G=32d^2 K even on unbalanced auxiliary profiles. This pays a polynomial-range convex positive model P=D+g+G, with bin-Lipschitz bound <=1/8, both laminar integer signatures at all powers, both factorial lifts, contamination, and finite-bit capped evaluation/annealing. The offset -C* is retained as a compact log normalizer. Its sampler estimates ORIGINAL child weights, including translation constants, and has a capped binary interval self-reduction. All of those are credited source/classical compositions.

This construction is compatible with more of the present reduction than a naive weight insertion suggests. For an affine physical weight, multiplication by an exponential tilt does not alter any normalized two-step signature at all: the same linear exponent cancels between numerator and denominator. More generally, the unary log-concave factors already covered in section2 are admitted in the Source115 laminar integer model. The initial difficulty is consequently neither arbitrary activities, unary weighting, positivity by itself, weighted self-reduction, nor the existence of huge numerical capacities.

Our original value-oracle formulation has log range <=nA from the start, so r57's mass normalization and global physical-range role is ALREADY paid without reduced-cost localization. This does not provide the all-auxiliary-profile Lipschitz and signature contract. To make that distinction explicit, write phi=-log a_e on [0,R]. For R>0 and 0<rho<1/2, convexity and range [0,A] imply that every subgradient at x in [rho R,(1-rho)R] lies in [-A/(rho R),A/(rho R)]. Indeed the left and right secant bounds are (phi(x)-phi(0))/x and (phi(R)-phi(x))/(R-x). Extending this restricted convex function by supporting affine rays therefore has a controlled slope and range on a fixed multiple of the physical interval. This is a viable local numerical operation, not evidence that the full target closes.

To apply it one must still account for the removed endpoint strips, while retaining the SAME full port model. A rank fiber may lie wholly at a physical endpoint, so discarding these strips is not a uniform relative-mass argument. The cell homothety in section3 avoids discarding them: it moves toward slice-specific interior witnesses and bounds the weight ratio directly by theta nA. But it is not a single auxiliary-profile change of variables preserving the port equations and their normalized signature matrices. Conversely the source115 forest/laminar representation gives exactly such integer signatures for its own incidence equations; replacing those by arbitrary submodular rank constraints has not been justified by the forest lemma or by affine tilt invariance. Thus the compatible pieces have been combined as far as their proved interfaces permit; no incompatibility theorem is asserted.

The primary clone calculation in section5 remains a separate exact representation of this SAME family, not a second research direction. Its numerical-capacity rate/field bounds are unchanged by the newly read r57 construction. A full transfer would need to connect one of these representations to a binary-size evaluator AND a proved full-domain transport contract, with a common error budget. No such connection was obtained. The final disposition remains PREFREEZE/no nominee; the paid table result, the weighted homothety and the orbit identities are not renamed as substantial findings.
