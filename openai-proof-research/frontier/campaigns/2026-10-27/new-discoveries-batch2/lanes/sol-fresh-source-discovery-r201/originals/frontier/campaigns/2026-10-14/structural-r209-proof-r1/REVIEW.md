# Independent mathematical correctness review — T333Q209, round 1

Verdict: **PASS at the entire unchanged frozen scope, relative to the stipulated Source333 truth and operative construction.** The submitted proof establishes the stated smooth embedding existence and finite-input square-root estimate for each fixed output order, and the exact C1 obstruction and optimality assertion. I found no essential change required in the statement or proof. This is a mathematical correctness verdict only; it makes no contribution, acceptance, or count decision.

This verdict concerns the actual original FROZEN-STATEMENT.md (SHA256 `9008ac4ac426a6ff7f4419aaab3f6dcd0e48b73b3186f53b0122b3ab3248091a`) and AUTHOR-PROOF.md (SHA256 `57ae02af6e6441b170e4a1173bb97b043b952476172277639e37a345666632c5`) in `frontier/campaigns/2026-10-14/fresh-structural-discovery-r209/`. Both were read completely, together with the complete original DERIVATIONS.md, READING-AND-COMPARISON.md, FINAL.md, and REPORT.md. No original was modified, narrowed, or replaced. No author calculation script, artifact test, prior review, or parent assessment supplied mathematical evidence.

The proof dependency is the actual small-mode and smoothing construction in Source333 at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, not merely its headline theorem or its proposition initialized at R=440. All nine included source sections were read completely after authentication. The source is paid true input: below I check its applicability and the author's additional deductions, not its internal truth. Reading extents, primary versions, omissions, and artifact procedures are recorded separately in READING-LIMITS.md and private records.

**1. Exact quantifiers and global linear calculation.**

The claim reviewed is: for every integer m>=2, with k=max(10,2m+2) and r=88k+54, there are C_m,eta_m>0 depending only on m and the fixed conventions, such that every smooth symmetric h with ||h||_Cr<eta_m and g0+h positive definite has a smooth embedding F into Euclidean R4 with exact induced metric g0+h and ||F-F0||_Cm<=C_m||h||_Cr^(1/2). All perturbations in this finite-norm ball are included, without a higher-derivative bound. The h=0 case and all the excluded stronger assertions are addressed below.

The global frame has derivatives n1_x=e1, e1_x=-n1, n2_y=e2, e2_y=-n2, with the other coordinate derivatives zero. Differentiating U=u1 e1+u2 e2+v1 n1+v2 n2 gives its e1 component in U_x as u1_x+v1, its e2 component in U_y as u2_y+v2, and the cross components e2·U_x=u2_x, e1·U_y=u1_y. Thus all three entries of (1.1) have the displayed signs and factors. The tensor B in the proof is the symmetric polarization of the metric quadratic term, not the geometric second form. With that convention gamma(F0+U)=g0+LU+B(U,U) exactly.

Periodicity implies av(u2_x+u1_y)=0. Conversely, for A12 of zero mean, the Fourier multiplier Delta^-1 with its constant mode set to zero yields u1_y+u2_x=Delta Delta^-1 A12=A12. Choosing v1=A11/2-u1_x and v2=A22/2-u2_y also gives the two diagonal entries. Diagonal constant modes present no obstruction. Reality and periodicity are preserved by these multipliers. Therefore range(L)=ker(ell), with precisely the one real scalar obstruction ell(A)=av A12.

The asserted C^s loss of four is conservative and valid for every integer s>=0. For a nonzero integer frequency n=(p,q), integrate by parts s+4 times in a coordinate whose frequency has magnitude at least |n|/sqrt(2). The corresponding coefficient is bounded by C_s||A||_(C^(s+4))|n|^(-s-4). All scalar multipliers used in P have bounded magnitude on nonzero integer frequencies: the double derivative of Delta^-1 has order zero, and the single derivative has smaller order. Taking any derivative through s leaves an absolutely summable |n|^-4 majorant in two dimensions. The zero frequencies and the derivatives of the fixed smooth frame only change C_s. Applying this separately at every order proves smoothness on smooth inputs. It does not assert boundedness of a Calderon-Zygmund operator on C0 without loss.

A possible open-domain inverse is irrelevant to this compact range calculation. On R2, a mixed equation can be solved by an indefinite integral which need not be periodic. On T2, the mean of that derivative is zero. The argument neither imports an open-domain transversal nor assumes a full inverse of L.

**2. Moving-frame bending modes and the uniform scalar denominator.**

For V(phi)=phi_x e1-phi_y e2-phi_xx n1+phi_yy n2, the diagonal L-entries vanish by cancellation and the mixed entry is -phi_xy+phi_xy=0. I independently differentiated the actual ambient field, including derivatives of the frame. For phi=cos(px+qy), the components in the order (n1,e1,n2,e2) are exactly

    V_x=(p(1-p^2)sin(theta), 0, p q^2 sin(theta), p q cos(theta)),
    V_y=(-p^2 q sin(theta), -p q cos(theta), q(q^2-1)sin(theta), 0).

Their dot product is pq[p^2(p^2-1)+q^2(q^2-1)]sin^2(theta). For the nonconstant modes used here its average is half that coefficient. For (p,q)=(2,1) the value is 12; for (2,-1) it is -12. Division of the fields by sqrt(12) gives +1 and -1, respectively.

For the cross polarization, the above components are taken in the same pointwise orthonormal frame. Each term is a constant times products of sine or cosine at the two frequencies (2,1) and (2,-1). Their sums and differences have nonzero frequencies (4,0) and (0,2), so every such product has zero torus average. There is no unaccounted moving-frame frequency: its effect has already entered the derivative components before the dot product.

For |c|<=1, a=sqrt(1+c/2), b=sqrt(1-c/2) both lie in [1/sqrt(2),sqrt(3/2)]. Consequently ell(Q(aV++bV-))=a^2-b^2=c and the derivative in the V+ direction is 2a>=sqrt(2). This includes c=0 and both endpoints c=+/-1. The amplitudes are spatial constants and smooth functions of c on an open interval containing [-1,1]; all spatial derivatives of W1 therefore have uniform bounds. No division by the possibly zero requested shear occurs.

**3. Triangular finite cancellation, including observation order zero.**

The degree-j quadratic coefficient uses indices a+b=j with a,b>=1, hence only fields already available through j-1. Changing the provisional W_(j-1) by beta_j V+ changes its linear image by zero. The first affected quadratic coefficient is degree j, and its change there is precisely 2 beta_j B(W1,V+). Its self-interaction first occurs at 2j-2>=j+1 for j>=3. Thus no coefficient already canceled is changed. Dividing -ell(Zj) by 2a makes Zj' mean-free, and Wj=-P(Zj') cancels its entire tensor. WJ can remain provisional: there is no degree J+1 cancellation requirement. For J=2 the initial equation alone suffices.

Here is a precise version of the proof's derivative induction, to resolve the potentially misleading provisional/finalized issue. For j>=2, first prove a provisional bound at observation s with input order at most s+6j-1; after its one scalar adjustment, prove a finalized bound with input order s+6j. W1 has uniformly bounded derivatives with only the C0 hypothesis. Provisional W2 actually needs s+4, which is within s+11. For provisional Wj, P costs four derivatives and B costs one further derivative of its fields. Each finalized lower index i<=j-1 is needed through s+5 and uses at most s+5+6i<=s+6j-1 input derivatives. The scalar beta_j needed when producing that provisional Wj is also bounded under this hypothesis: it uses only C1 norms of lower fields, and the current provisional W_(j-1) uses at most 1+6(j-1)-1=6j-6 derivatives at C1.

Finally, to finalize Wj at the next step, its new scalar beta_(j+1) uses its provisional C1 norm, which needs at most 6j input derivatives. All other fields in that scalar cost no more. At output s=0 the extra derivative is exactly accommodated by the reserved sixth derivative. For s>=1, 6j<=s+6j already. The added field is a scalar times the fixed V+, so no further derivatives of H arise on spatial differentiation. The denominator is uniformly >=sqrt(2). Finite products and sums now give the claimed constants C_(s,J), uniform on ||H||_(C^(s+6j))<=1. This just unpacks the submitted induction; it is not a new cancellation scheme or a repair.

With r=R+2+6J, taking s=R+2 controls every finalized coefficient needed for Fapp, and taking s=R+1 controls every residual product. The exact polynomial expansion has remainder degrees J+1 through 2J; all its coefficients are uniformly bounded in CR. For 0<epsilon<=1, finite summation proves all three estimates (3.8). In particular no estimate for derivatives beyond r is used to bound the approximate map through R+2 or the residual through R.

For the actual choices R=40(k+1), J=8k+2,

    R+2+6J = 40k+40+2+48k+12 = 88k+54.

For the smallest permitted k=10, these values are R=440, J=82, r=934. They are finite for every m. Nothing here assumes convergence of the polynomial ansatz as J tends to infinity.

**4. Entire normalized input ball and geometry.**

For h!=0, epsilon=||h||_Cr^(1/2)>0 and H_initial=h/epsilon^2 give ||H_initial||_Cr=1. In particular |ell(H_initial)|<=1. Every estimate in the finite recursion is uniform over this entire unit ball, even if all norms above r are arbitrarily large. The maps and residuals remain smooth because h is smooth and only finitely many smooth/Fourier operations are made. Fapp-F0=O(epsilon) in C^(R+2), and gamma(Fapp)-(g0+h)=O(epsilon^(8k+3)) in CR, with constants depending only on m and fixed data.

At F0 the induced metric is the identity and the geometric second form has B_11=-n1, B_12=0, B_22=-n2. For Y=a partial_x+b partial_y,

    B_F0(Y,Y)=-a^2 n1-b^2 n2,
    |B_F0(Y,Y)|=sqrt(a^4+b^4)>=1/sqrt(2) if a^2+b^2=1.

Thus not only is the second-form tensor nowhere zero, but every nonzero transverse line is good at F0. Uniform metric and second-form margins persist under sufficiently small C2 changes, by the normal-projection formula and compactness of the base. Source preliminaries.tex, Lemma phase-data, therefore applies at F0 with positive reference g0. Fix its finite phase charts, cutoffs, coefficient forms, and good combinations once. Shrink to nested C2 neighborhoods of F0 and concentric C0 tensor balls around g0. All choices are independent of the eventual h.

The compact low-jet hypothesis in the small-increment proposition is satisfied by a fixed compact subset of the finite-dimensional 2-jet bundle over the compact base. This does not require, or falsely assert, compactness of an infinite-dimensional C2 ball. Positive lower bounds for the metric, good transverse second forms, inverse coframes, and square-root arguments can all be fixed. Coordinate norm changes to the source's finite atlas have fixed constants in each finite order and do not alter the finite derivative count or the allowed dependence on m.

The source's small-increment hypothesis is a tensor in its smaller positive ball; it is not merely a small arbitrary signed tensor. Initialization and the reference subtraction below provide exactly this positive tensor. Each constructed local summand has the stated phase support or pairwise-intersection support, so extension by zero is smooth. Smoothing need not preserve positivity by itself: the small C0 smoothing tail, followed by a small reference subtraction, supplies the required positivity. No assertion of exterior equality or relative support for the full exact correction is used.

**5. Fixed-reference identity and initialization.**

For clarity write D for the normalized CURRENT defect, D=delta^-2(g-gamma(G)); this is the H of proof Section 4, not H_initial. Let D_s=S_sD, G_s=S_sG and a'=(delta'/delta)^2. The source small increment is applied at G_s to D_s-a'g0. Its error definition gives

    gamma(G_s+U)-gamma(G_s)=delta^2 D_s-delta'^2 g0+E.

Direct expansion of the quadratic metric shows

    gamma(G+U)-gamma(G)
      =gamma(G_s+U)-gamma(G_s)+C(G-G_s,U).

Using g-gamma(G)=delta^2D and defining D'=delta'^-2(g-gamma(G+U)) gives

    delta'^2(D'-g0)=delta^2(D-D_s)-E-C(G-G_s,U).

This is exactly (4.5), with the signs and factor in C correct. In particular the quadratic U term cancels in comparing the two increments, and there is no squared smoothing tail. The target g has canceled, rather than becoming a coefficient requiring uncontrolled derivatives. Only the fixed tensor g0 is differentiated when estimating the reference term. The source proof of its exact-step lemma can consequently be applied with these definitions, after checking the hypotheses already described. This use of the source proof is essential; merely citing its fixed-target existence proposition would not supply the claimed uniformity.

For initialization put e=gamma(f)-g, t0=epsilon^4, delta0=epsilon^(4k), and G0=sqrt(1-delta0^2)f. Quadratic homogeneity gives

    g-gamma(G0)=delta0^2 g-(1-delta0^2)e,
    D0=g+(1-delta0^-2)e.

This proves (4.8) independently. Since J+1=8k+3, ||D0-g||_CR<=A epsilon^3 for 0<epsilon<1. The sign of e is immaterial to this bound. Together with ||g-g0||_C0<=A epsilon^2 it puts D0 in the fixed positive C0 ball, while ||D0||_CR is uniformly bounded. Also ||G0||_(C^(R+2)) is uniformly bounded. Consequently the positive-order terms in S_R(t0;G0,D0) vanish uniformly as t0 tends to zero. Choose one B sufficiently large for the baseline and these initial finite bounds; S_R<=B/2 holds with an epsilon threshold independent of every higher derivative.

The initial displacement is bounded by

    ||G0-f||_Cm <= ||f||_Cm delta0^2/(1+sqrt(1-delta0^2))
                  <= A epsilon^(8k) <= epsilon^3/4

after a uniform reduction of epsilon. Here m<=R+2. There is no unprescribed high norm in this step. The bridge hypotheses (4.2) hold for the approximate maps with one A depending only on m and the conventions: f and g have the stated finite bounds, g-g0 has C0 size O(epsilon^2), and e has CR size O(epsilon^(J+1)).

**6. Smoothing, actual finite input dependence, and all six powers.**

For a fixed block k, take r=q=40(k+1), tau=t^(6/5), s=t^(11/10), delta=t^k. Then 0<tau<=s<=t<=1, tau/s=t^(1/10)->0 and delta/tau=t^(k-6/5)->0. The unperturbed case of Source333 small-modes.tex, Proposition small-increment, is the applicable case: there are no polynomial perturbation operators P_i. It permits arbitrary finite q and yields U=O_tau(delta tau) and E=O_tau(delta(tau/s)^q+delta^3/tau).

It would be an error to assume that q mode corrections require only r unsmoothed derivatives. The source does not make that claim, and the author does not need it. Its exact finite-order smoothing lemma supplies every required finite *weighted smoothed* derivative from the controlled finite bound S_r<=B. For any fixed d,

    |j^2 G_s|_(d,s)+|D_s|_(d,s) <= C_(d,r) B.

A derivative of the smoothing kernel pays for an arbitrarily high fixed smoothed observation order. Required orders may increase with q and the desired output norm, but the constants at those orders depend only on d,r,B and fixed geometry, not on true-input derivatives above r+2,r. Subtracting a'g0 preserves this property. Domain restrictions on the finite substitution formulas use finitely many orders for fixed q. Once their low-order tensor arguments stay in the positive domain, higher output estimates follow from the same finite smooth formulas, with larger constants and without a new infinite family of domain thresholds. This resolves a possible incorrect reading of the all-order notation.

The source tail bound follows by splitting derivatives at r. For j<=r the contribution is bounded by

    C B t^-r s^(r-j) tau^j <= C B(s/t)^r.

For j>r, boundedness of smoothing in the original norm gives at most C_d(tau/t)^j S_d<=C_d(tau/t)^r S_d. Thus the true high norms enter only through the linear tail term S_d(tau/t)^r. The usual weighted product rule gives |AB|_(d,tau)<=C_d|A|_(d,tau)|B|_(d,tau). Also |dU|_(d,tau)<=C_(d,k)delta, using the increment bound at d+1. In the cross term C(G-G_s,U), the second factor has a uniform smoothed-input bound. Multiplication therefore preserves linear dependence on the uncontrolled S_d; it does not produce S_d squared. This is the substantive content of using the exact identity rather than estimating separately two full metric errors.

For delta'=tau^(k+1), direct exponent subtraction gives, in the order of the proof's table,

    (13k+8)/5, (3k-18)/5, (18k+8)/5,
    (38k+28)/5, (13k+8)/5, (33k+28)/5.

For example the first is k+q/10-12(k+1)/5 and the second is 3k-6/5-12(k+1)/5. The other four are 2k+r/10-12(k+1)/5, 2k+r/5-12(k+1)/5, k+r/10-12(k+1)/5, and k+r/5-12(k+1)/5. Substituting r=q=40(k+1) gives exactly the six displayed values. Their least value for k>=10 is at least 12/5, so they can all be weakened to exponent 1/5.

For the same-block choice delta'=tau^k, division loses 12/5 fewer powers. Thus the corresponding exponents are

    (13k+20)/5, (3k-6)/5, (18k+20)/5,
    (38k+40)/5, (13k+20)/5, (33k+40)/5.

They too are positive, and all transition estimates are the more demanding ones. The two ratios delta'/delta are t^(k/5) and t^((k+6)/5), respectively, so the positive input remains in its permitted ball in either case.

For the map part, positive inherited weighted orders gain tau/t=t^(1/5), while |j^2U|_(d,tau)<=C_(d,k)delta/tau (apply the increment estimate at d+2). For the fixed reference, |g0|_(d,tau)<=||g0||_C0+C_d tau. In the stipulated global tensor coordinates g0 even has constant entries; in any fixed atlas its derivatives are still fixed. Hence

    |D'-g0|_(d,tau)<=C_(d,k)t^(1/5)(1+S_d),
    S_d(tau;G',D')<=||G||_C2+||g0||_C0
                       +C_(d,k)t^(1/5)(1+S_d).

The constants may grow with d and k. They are not asserted uniform in all observation orders, and that stronger assertion is unnecessary. This proves the author's recurrence with the stated finite-input independence.

**7. Controlled-order invariance, finite waits, and no next-block circularity.**

Choose the fixed nested geometric neighborhoods first and B large enough that ||G||_C2+||g0||_C0<B/4 throughout the neighborhood in which the construction will remain. At order r(k), with S_r<=B, the recurrence preserves S_r<=B by taking t below a fixed k-dependent threshold, for example one making C_(r,k)t^(1/5)(1+B)<=B/2. The C0 defect recurrence similarly preserves the chosen smaller tensor neighborhood. The smoothing tail puts G_s in the larger admissible geometric neighborhood, and the small C2 increment keeps the interpolation segment there. These thresholds only use the controlled B and fixed geometry, k, and finitely many required orders.

To justify retention in the geometric neighborhood without circularity, use the displacement invariant simultaneously. Set d_k=floor(k/2). The one-step increment satisfies

    ||U||_(C^d_k)<=C_k t^e(k),
    e(k)=k+(6/5)(1-d_k)>1.

At the initial k>=10 and t0=epsilon^4, it is enough that C_k epsilon^[4(e(k)-1)-3]<=1. The smallest relevant even case k=10 has e(k)=26/5, so 4(e(k)-1)=84/5>3; odd k has a larger margin. Thus the initial bound ||U||_(C^d_k)<=epsilon^3 t has a uniform epsilon threshold. Within that block it continues to hold as t decreases. For each later fixed epsilon,k the analogous threshold is strictly positive, though it need not have a uniform lower bound over k. Both choices of delta' can be included in each threshold.

The scale sequence is t_n=t0^((6/5)^n). For example t_(n+1)/t_n<=t0^(1/5), so sum t_n<=t0/(1-t0^(1/5))<1/4 for sufficiently small t0. The initial displacement is <=epsilon^3/4. Since d_k>=d_k0>=m>=2, all increments are bounded in both Cm and C2 by epsilon^3 t_n. Their partial sums therefore stay within epsilon^3/2 of f. Combining this with ||f-F0||_C2<=A epsilon retains every finite-stage map in the fixed smaller C2 neighborhood, and hence preserves the baseline and all geometric margins. This is a simultaneous induction on the finite stages, not an assumption about an already existing limit.

The only remaining issue is whether a block could last forever because of uncontrolled high derivatives. Hold k fixed and observe any fixed order d. Under the already established S_r bound, the recurrence applies to x_n=S_d(t_n;G_n,D_n) even when x_n is very large:

    x_(n+1)<=B/4+c_n(1+x_n),  c_n=C_(d,k)t_n^(1/5)->0.

Every x_n is finite because all inputs and each finite correction are smooth. Once c_n<=1/4, iteration bounds x_n by a finite constant depending on its current finite value and B; then c_n->0 gives limsup x_n<=B/4. Thus x_n<=B eventually. No uniform initial high-norm bound is needed for this eventual assertion.

For the transition apply this **old block k** recurrence at d=r(k+1). Wait until x_n<=B, until t is below the next block's known threshold (including its epsilon^3 t displacement threshold), and until C_(r(k+1),k)t^(1/5)(1+B)<=B/2. These conditions hold after finitely many same-block steps. Now take delta'=tau^(k+1). The old recurrence, already checked for this smaller delta', gives the new S_(r(k+1))<3B/4. The new scale tau<t meets the next block's threshold. Its normalized defect is exactly the one corresponding to tau^(k+1), so there is no additional uncontrolled renormalization. This establishes the next block's hypotheses before using them. Each block has finite length, and k tends to infinity.

Higher smooth data can determine the waiting times; constants C_(d,k) and future thresholds may also grow with order. None is included in an infinite minimum restricting the initial epsilon. The initial epsilon threshold uses only k0, A, B, fixed geometry, and finitely many inequalities. This resolves the main uniformity concern in the frozen finite-norm-ball assertion.

**8. A single smooth limit, exactness, estimate, and global injectivity.**

For a fixed m and a fixed smooth input, the schedule just constructed gives one sequence of maps. Every fixed spatial observation order d is eventually below floor(k/2), so the tail of that same sequence is absolutely summable in Cd. Its finite initial segment consists of smooth maps and does not matter for convergence. The Cd limits coincide with the unique C0 limit; uniform derivative convergence on charts gives one smooth spatial map F. This is not a separate choice of limit for each d.

The unnormalized defects are delta_n^2 D_n, with D_n staying in a fixed C0 neighborhood of g0 and delta_n=t_n^k_n->0. Since G_n->F in C1, the induced-metric map is continuous in C1 and gamma(F)=g. Positive definiteness of g gives rank two. Summing the initial scaling error and all increments yields ||F-f||_Cm<=epsilon^3/2, stronger than the bridge's epsilon^3 assertion. Thus ||F-F0||_Cm<=A_m epsilon+epsilon^3<=C_m epsilon, uniformly on the finite input ball. For h=0, F0 is itself the required smooth embedding.

Rank is not injectivity, and the proof separately supplies the needed argument. F0 is the product of the two unit-circle embeddings, hence a compact smooth embedding. In sufficiently small convex coordinate balls, choose and normalize an ambient linear projection so that the projected F0 derivative differs from the identity by less than 1/4. A sufficiently C1-close F then differs by less than 1/2. Integrating the derivative of projected F minus the identity along a segment gives

    |projected F(u)-projected F(v)| >= |u-v|/2.

This is stronger than merely knowing a pointwise nonsingular derivative, and gives injectivity on each such ball. A finite smaller-ball cover and a Lebesgue number treat nearby pairs. On the compact complement of a neighborhood of the diagonal, the continuous function |F0(p)-F0(q)| has a positive minimum; C0 closeness preserves separation. Thus F is globally injective, and compactness plus immersion makes it a smooth embedding. The smallness threshold for this openness statement depends only on F0 and fixed charts. It is compatible with the uniform estimate and can be included in eta_m.

For each m the choice of k0,r_m, admissible epsilon, and schedule is made separately. The proof does not claim that one realization satisfies the quantitative estimates for all different m. Within a single fixed-m construction it does correctly obtain all spatial differentiability orders of its one realization.

**9. Exact mixed-shear identity and optimal exponent.**

Let |t|<1 and let any C1 map F induce the specified constant tensor g0+h_t. With U=F-F0, the mixed entry is

    t=<e1,U_y>+<e2,U_x>+<U_x,U_y>.

The first term integrates to zero in y at each x because e1 is y-independent and U is periodic; the second integrates to zero in x for the corresponding reason. C1 regularity suffices for these one-variable integrals and Fubini. The torus coordinate area is (2pi)^2=4pi^2, hence

    integral <U_x,U_y> = 4pi^2 t.

It follows that

    8pi^2 |t| <= integral (|U_x|^2+|U_y|^2).

Also |t|<=sup|U_x| sup|U_y|<=||U||_C1^2 with the exact Euclidean-vector maximum norm stipulated in the statement. Thus the norm constant is exactly 1. No second derivative, smallness, injectivity, or parameter dependence of F is required.

The eigenvalues of g0+h_t are 1+t and 1-t, so the strict positive-definiteness range is exactly |t|<1. For every finite nonnegative integer r the tensor norm is ||h_t||_Cr=|t|, since its nonzero entries are constant. For any alpha>1/2 and fixed C,eta,r, choose 0<|t|<min(eta,1) with C|t|^(alpha-1/2)<1. Then every realizing map violates the proposed stronger C1 upper estimate. The quantifiers in the claimed impossibility, including arbitrary finite r and arbitrary constants, are therefore correct. At t=0 the stated lower bounds reduce to zero and remain valid.

**10. Actual source coverage and auxiliary claims.**

The source's phase-data lemma requires a nowhere-zero vector-valued second form, not a free map. Its small-increment proposition is local in finitely many good phases, uses positive tensor square roots with fixed margins, preserves the indicated local supports, and has constants depending on finitely many weighted inputs. Its exact construction smooths only inputs used to make an increment, adds that increment to the unsmoothed map, and obtains an all-order recurrence from finite controlled input. The author's application matches each of these features. The source's changing-family polynomial phase-data lemma is not needed at this fixed F0; the simpler fixed-neighborhood phase-data lemma suffices and avoids unnecessary epsilon-dependent geometry.

I also read the source's velocity-loop, primitive-realization, geometry-preservation and global-construction bodies in full. They support the packet's explanatory statements: positive primitive additions are assembled finitely, exact intermediate metrics are retained, a preferred normal section and nonzero second form are propagated, and exterior C2 closeness is available rather than exact exterior equality. A preferred normal section is not a global normal frame on an arbitrary nonorientable surface. All these compatible operations are paid input. The quantitative proof here uses the small-mode/exact-correction subconstruction directly and does not need to rerun the large primitive additions, phase-Hessian preparation, finite-point spherical preparation, or normal-turn argument.

The prefreeze notes describe a possible parameter-family direction as prospective, expressly with missing mixed-derivative/schedule requirements at that stage. They do not assert that direction as a theorem or use it to prove the frozen target. Their finite-budget and fixed-reference feasibility calculations agree with the final proof. Their formal-support limitation agrees with the actual comparator. There is no extra auxiliary mathematical assertion in the submitted prose that silently supplies an unproved endpoint.

**11. Primary and original-history comparisons: dependencies distinguished from context.**

The exact admitted r107 original spans were read and matched byte-for-byte against the two admitted copies. Its scope expressly excludes prescribed-map approximation and quantitative uniformity. Sections 2–6 contain the compact C1 embedding openness argument, construction of an oblique tubular projection, transversality of the source velocity plane, C0 convergence from the mean-zero periodic primitive, injectivity after projection, and finite global assembly. These are paid prior mechanisms. T333Q209 directly proves the compact embedding openness it needs; it does not rely on an unverified uniform quantitative strengthening of r107. The stronger primitive embedding mechanism is credited in the comparison but is not required by this near-F0 completion.

Nash's 1956 Part A (printed pp21–30) supplies smoothing precedents; the actual nonsingular algebraic perturbation system on pp31–33 and Theorem 1 on p52 require a nonsingular full linear solve. At F0 the mixed second derivative vanishes, and the independently proved mean obstruction excludes a full global linear inverse. Nothing in the cited Nash interface removes that obstruction. The proof does not invoke Nash's theorem as a black box to complete this particular nonfree metric map.

Kallen's 1978 Lemmas 2.2–2.3 and the complete Lemma 3.3 finite substitution discussion provide actual positive-decomposition and finite-correction precedents. The extracted exponents are imperfect in places, so I do not use them for any numerical estimate of T333Q209. Those numerical estimates were checked independently above, and the operative exact correction is the stipulated source construction. Kallen's low-regularity, sufficiently-high-dimension theorem is not silently being used as a smooth R4 endpoint.

Moser's 1966 Chapter I Section 5 hypotheses were visually read at printed pp283–285. They require approximate solutions to the full linearized equation for arbitrary sufficiently controlled right-hand sides and for nearby base points, with a stated approximation rate and norm bounds. The mean functional at F0 prevents even arbitrarily accurate C0 approximations to a right-hand side with nonzero mean mixed entry. Thus these hypotheses do not themselves supply the missing scalar. The auxiliary footnote permitting a known linearization at a solution is not an assumption made here. The author uses the actual source nonlinear construction instead. No missing OCR equation from Moser is treated as proved or as an input.

Gromov's October 9, 2015 manuscript pp38–42 and 44–46 distinguishes algebraic/free-map inversion, generic differential inversion, and the perturbation theorem requiring an infinitesimal inverse on an appropriate open set. A generic statement does not establish that this fixed singular torus belongs to that set. The source's generic/open-domain comparisons therefore do not contradict the concrete range calculation, nor are they required for completion.

De Leo's four-page arXiv copy (header 0905.0928v1, May 6, 2009; internal date February 5, 2020) was read completely. Its product example is on R2 and reduces to the same mixed derivative equation. That equation has an unrestricted smooth primitive there; periodic solvability instead requires zero mean. I do not import its general transversal argument into a compact problem, or use an unexamined global-solvability claim to bridge the obstruction.

De Leo's 2019 journal paper, pp919–932, was read completely. Example 2 on p921 calls the product torus full 2-rank. Definition 10 on p929 imposes an additional open differential relation for the inverse domain, and Theorems 7–8/Corollary 2 use that domain and their dimensional restrictions. Merely being the full-rank example is not their hypothesis of infinitesimal invertibility. The mean obstruction gives a direct reason that no asserted full inverse can hold at this F0. The author does not need a claim about generic perturbations of F0 or a full classification of other inverse domains.

Ekeland–Sere's 2021 paper, printed pp3324–3329, states exact right-inverse or Galerkin right-inverse assumptions with singular estimates before its Theorem 3. Permitting a negative power of a parameter in an inverse bound does not provide an inverse where none is established. No such family is assumed by T333Q209. The primary serves as a comparison, not an unstated completion lemma.

Hamilton's inaccessible body, the unread Gromov book, D'Ambra–Loi, and other contextual bibliography entries are not required proof dependencies. Their absence limits any literature assessment; it does not invalidate the explicitly verified source-based construction, and it provides no novelty evidence. I give no exhaustive literature or original-history clearance and no contribution verdict. These distinctions resolve the apparent gap between named classical methods and the actual hypotheses needed here, without treating a source stipulation as permission to ignore an application mismatch.

**12. Excluded stronger scopes, remaining objections, and final disposition.**

There is no continuous or smooth selection in the metric parameter, no simultaneous quantitative choice for all m, no finite-regularity extension, no relative prescribed jets or exterior equality, no equivariant assertion, and no normal-frame claim for arbitrary surfaces. Smooth input is used essentially to make every future observation norm finite. The construction stays on the given torus with the fixed Euclidean target metric. Its finite coefficients depend smoothly on a scalar mean where asserted, but no conclusion of smooth dependence of the infinite correction schedule or limit is drawn from that fact.

The pinned Lean comparator was authenticated using exact pinned GitHub metadata and read completely. Its endpoint theorem ends in `sorry`. The navigation page's statement that it proves the endpoint does not establish proof coverage. Neither that comparator nor any test is credited as a formal proof of Source333 or this target. No formalization was undertaken.

The substantive adversarial concerns were: moving-frame terms; loss of a derivative on finalizing a coefficient at s=0; uniformity across uncontrolled high norms; positivity after smoothing; a possible squared high-norm tail; dependence of all-order constants on observation order; an infinite family of initial thresholds; a circular next-block bound; and immersion versus global injectivity. Each is resolved above by an explicit calculation or by matching an actually read paid source operation to the precise hypotheses of this application. None remains an essential unmet obligation in the submitted proof. The comparison reading limits are real but do not hide an endpoint dependency.

Accordingly the **entire unchanged frozen statement and submitted proof PASS mathematical correctness review, relative to the stipulated upstream truth**. The originals require no essential mathematical repair for this verdict. Completion of this review returns to the parent; no contribution classification, acceptance, count, public action, or downstream work is supplied.
