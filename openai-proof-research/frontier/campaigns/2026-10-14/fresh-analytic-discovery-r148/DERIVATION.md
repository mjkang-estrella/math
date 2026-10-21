# Prefreeze derivation: exact extra-frequency data on a scalar invisible family

This is a research calculation, not an author proof of a nominee. No theorem was frozen. The attempted full target is simultaneous equality of the **entire** Dirichlet-to-Neumann operators at zero and at a prescribed negative spectral parameter -tau, tau>0, for two distinct real uniformly positive bounded scalar conductivities on B(0,3), both 1 in an outer collar, with the same known bulk density 1. There is no finite-voltage, approximate-equality, variable-density or singular-coefficient replacement. No literature-priority or current-open designation is asserted for this target.

The reduction below was developed after reading all five actual TeX bodies of the pinned rough Source365, including its scalarization, wall correction, frequency-ending, nested-charge and full boundary-map proofs. Their theorem and proof operations are stipulated true. The source is not being audited. Its smooth companion was read at its precise scalar statement and scalar-reduction proof; its internal global smooth-geometric proof is not imported. The completed r147 role verdicts supplied context only, not mathematical premises for this direction.

## 1. Credit the actual source operation

Let Omega=B(0,3). Fix the source's b, nested annular cells D_nu, surfaces Sigma_nu and probability measures mu_nu, with similarity ratio s=57/100. Let gamma be the source conductivity, 0<c<=gamma<=C, equal 1 outside the compact parent cell. Put

    a_gamma(u,v)=integral gamma grad u . grad v,
    L_gamma=-div(gamma grad),
    P f = the gamma-harmonic extension of f.

The source's finite-field scalarization preserves the **entire** normal functional for each of two inputs. Its proof uses exact divergence and symmetry constraints, a simultaneous coordinate change, symmetric constitutive correction, finite-depth laminate exhaustion and a Baire strong-continuity point. We do not downgrade that to approximate homogenization. Its branching block then supplies all zero-sum triples of surface currents. Constant voltage data modulo constants have dimension two; the source already passes from those two inputs to all separately constant block data.

The resulting source lemma supplies W_(nu,p), linear in a zero-sum triple p, with support in closure(D_nu), constant in the two children, and

    a_gamma(W_(nu,p),psi)=sum_(i=0,-,+) p_i average_(Sigma_(nu i)) psi,
    ||W_(nu,p)||_infinity <= K s^(-|nu|)|p|,
    ||grad W_(nu,p)||_2^2 <= K s^(-|nu|)|p|^2.             (1)

The parent term nu0 means nu. These are statements for every H1 test, with exact matching measures on shared surfaces. For every global harmonic u all surface averages equal one number ell(u). This is reciprocity with (1), not an assumption of unique continuation or of pointwise traces on the limiting set.

The actual source already constructs a nonzero bounded H1_0 potential w, with compact interior support, for which

    a_gamma(w,(u-ell(u))phi)=0                            (2)

for bounded harmonic u and smooth compactly supported phi. With rho=1+w and ||w||_infinity<1/2 it proves

    gamma_w=rho^2 gamma,
    P_w f=ell(Pf)+(Pf-ell(Pf))/rho,
    Lambda_(gamma_w)(0)=Lambda_gamma(0).                 (3)

We absorb the source's small scalar delta into w. Every global/dense-input passage in (3) is already paid by its proof. Finite disjoint insertion is also already its cor:localized. Neither is proposed as new.

## 2. Give the full signed-charge freedom its credit

The source need not be confined to its one left-minus-right charge. Let X={-,+}^N with fair Bernoulli measure beta, and let h in L-infinity(beta) have integral zero. For a cylinder [nu] put q_nu=integral_[nu] h d beta. Then

    q_empty=0, q_nu=q_(nu-)+q_(nu+),
    |q_nu|<=2^(-j)||h||_infinity for |nu|=j,
    sum_(|nu|=j)|q_nu|<=||h||_infinity.

At the root use p=(0,q_-,q_+); at every other vertex use p=(-q_nu,q_(nu-),q_(nu+)). Sum the corresponding W through depth N-1. Sources telescope to sum_(|nu|=N)q_nu mu_nu. Disjoint interiors at each depth and (1) give, after adjusting a fixed source constant,

    ||Z_j||_infinity <= K (2s)^(-j)||h||_infinity,
    ||grad Z_j||_2 <= K (2s)^(-j/2)||h||_infinity.        (4)

Since 2s>1, the series defines w_h in H1_0 intersect L-infinity. Its support remains in closure(D). Subtracting the value of a smooth test in each shrinking cell and using the common harmonic average proves (2), with error at most

    2 ||u||_infinity ||grad phi||_infinity diam(D) s^N ||h||_infinity.

Thus (3) holds for every h small enough in L-infinity. This extension uses exactly source linearity and its two geometric series; it is not a nonroutine result.

The map h -> w_h is injective. If h is nonzero, some cylinder integral q_nu is nonzero (otherwise conditional expectations on every finite cylinder sigma-algebra vanish, and martingale/elementary simple-function density gives h=0). Choose a smooth test eta equal 1 on closure(D_nu) and 0 near the other cells at that fixed depth. At all deeper levels the source pairing is q_nu. Passing to the H1 limit gives a_gamma(w_h,eta)=q_nu, hence w_h is nonzero. One can equivalently define the finite signed measure on the limiting Cantor set by the cylinder charges; no pointwise Sobolev multiplication on that set is needed here.

The map from L-infinity_0(beta) into H1_0 intersect L-infinity, with sum norm, is compact: each partial sum is finite rank and the operator-norm tail is bounded by the tails of (4). Consequently an infinite supply of charge parameters alone does not produce a uniform noncollapse bound when infinitely many new measurements are matched.

This pays the strongest obvious static-family enlargement before asking for an extra frequency. It is not submitted as a substitute theorem.

## 3. Exact spectral reduction for every negative parameter

For any fixed real a with 0<c_a<=a<=C_a, define its Dirichlet inverse R_a on L2 by

    R_a F in H1_0,  a_a(R_a F,v)=integral Fv  (v in H1_0).

It is bounded, positive and self-adjoint on L2. Poincare gives ||R_a||<=C_P^2/c_a. Let P_a=P_a(0). For real z<=0 the equation is L_a u=z u and the weak boundary form is

    <Lambda_a(z)f,g>=a_a(u,V)-z integral u V,

where V has trace g. The difference u-P_a f has zero trace. The weak equation gives

    u-P_a f=z R_a u,
    P_a(z)=(I-z R_a)^(-1)P_a.                           (5)

For z=-tau<=0, I+tau R_a is invertible on L2 with inverse norm at most 1. Its solution also belongs to H1 since u=P_a f-tau R_a u. Thus (5) is global on the negative axis, not just a small-z Neumann-series argument.

Test with P_a g. Harmonicity gives a_a(u-P_a f,P_a g)=0. Therefore

    Lambda_a(z)=Lambda_a(0)-z P_a^*(I-z R_a)^(-1)P_a.     (6)

All adjoints here use the real L2 pairing and the trace-space duality. This is the classical Poisson/Dirichlet-resolvent identity: Behrndt--Rohleder arXiv:1012.4657v2, Lemma2.4, gives its actual Green-identity and resolvent proof. That paper assumes Lipschitz leading coefficients for its larger inverse/spectral results. The short weak proof above establishes the needed identity directly for our bounded measurable scalar class; none of its unique-continuation or spectral-reconstruction conclusions is imported outside its hypotheses.

Let P_h be the exact static Poisson map in (3), and R_h=R_(gamma_(w_h)). The second-frequency target within this source family is now **equivalent** to the exact operator equation

    F_tau(h):=
      P_h^*(I+tau R_h)^(-1)P_h
      -P^*(I+tau R_gamma)^(-1)P = 0.                     (7)

The DN discrepancy is tau F_tau(h). This is an equation on all H1/2 boundary data. Nonzero h would ensure distinct coefficients, but no such solution of (7) has been obtained. More generally one may seek h1!=h2 with F_tau(h1)=F_tau(h2); failure to find a zero relative to h=0 would not rule out that larger possibility.

The functional ell(Pf) is bounded on H1/2: P maps into H1, restriction to the fixed interior root surface has a bounded trace, and its fixed probability density is bounded. Consequently formula (3), first proved for smooth f, extends as an L2 identity to all f by density. This justifies every operator in (7) without asserting that division by rho is a bounded multiplier on arbitrary H1 functions.

For |z| ||R_a||<1, (6) also yields the convergent operator Taylor expansion

    Lambda_a(z)=Lambda_a(0)
      -sum_(k>=0) z^(k+1) P_a^* R_a^k P_a.             (8)

The k=0 condition is a Gram form, not a boundary energy. Matching it is necessary for equality on a neighborhood of zero, but is **not necessary** for equality at one isolated prescribed -tau. A nonzero first derivative therefore cannot disprove the two-frequency target. Conversely, matching finitely many derivatives or matrix elements does not solve (7).

## 4. What the static cancellation does to the first frequency jet

Write u=P f, v=P g, alpha=ell(u), beta=ell(v), U=u-alpha, V=v-beta. Formula (3) and (8) give the full unit-density first-jet difference

    <[Lambda_h'(0)-Lambda_0'(0)]f,g>
      =-integral [(rho^(-2)-1) U V
                   +(rho^(-1)-1)(alpha V+beta U)].       (9)

These are volume products. Equation (2) instead pairs L_gamma w with (u-alpha)phi. Integrating (2) by parts does not replace that singular source by Lebesgue measure. Thus (9) is not killed by the supplied identity.

One might compensate the multiplication by changing the mass density to rho^2. This is outside the target, but its strongest first-jet effect can be computed exactly. For L_a u=z m u the same weak differentiation at z=0 gives Lambda'_(a,m)(0)=-P_a^* m P_a. Keeping a=gamma_h and setting m=rho^2 gives

    rho P_h f = P f+w alpha,
    <[Lambda'_(gamma_h,rho^2)(0)-Lambda'_(gamma,1)(0)]f,g>
      =-[alpha integral w v+beta integral w u
                         +alpha beta integral w^2].     (10)

The entire defect has rank at most two. This is ordinary Gram algebra once the exact source solution formula is credited. It is not substantial contribution evidence.

It vanishes exactly when the functional A(f)=integral w P f is

    A=-(integral w^2)/2 times ell.                       (11)

Indeed take g=1, noting ell(1)=1 and P1=1. The vanishing condition forces A to be proportional to ell, and f=g=1 fixes the proportionality. Conversely (11) makes (10) zero. In particular, if w is nonzero with integral w=0, the constant-voltage pair detects the compensated first derivative as -||w||_2^2. Such source potentials exist: the injective charge space is infinite dimensional, and integral w is a single linear functional. Scale a nonzero element of its kernel to preserve positivity.

This diagnostic does not establish injectivity of F_tau, or distinguish every source pair at every isolated tau. It only disproves automatic broadband preservation by this natural density compensation.

## 5. Test the stronger positive-ground-state composition

For any original coefficient a and tau>0, let H solve

    L_a H+tau H=0, H|boundary=1.

Weak comparison, interior Harnack and boundary regularity on the ball give 0<min H<=H<=1. In a common unit collar H is smooth. Set sigma=a H^2. For bounded weak tests and then by the appropriate energy/density extension, the product identity is

    integral a grad(Hv).grad(Hw)+tau H^2 v w
      =integral sigma grad v.grad w
                         +integral_boundary q_H f g,    (12)

where v,w have boundary values f,g and q_H=a partial_nu H is smooth in the collar. The last term follows by testing the H-equation against H v w; it includes the boundary term. It must not be dropped merely because H=1 on the boundary. For arbitrary solutions, density extends the boundary-operator identity

    Lambda_a(-tau)=Lambda_sigma(0)+M_(q_H).              (13)

This is the ordinary ground-state/conformal energy operation, compared with DKN2020 Proposition1.2's actual weak product proof and with the previously authored r29 ground-state discussion. Source's compact-source affine correction is already stronger than the harmonic-factor gauge in DKN, whose Remark1.3 rules out a nonconstant harmonic factor equal1 on the full boundary.

Evaluating (13) on 1 recovers q_H, since Lambda_sigma(0)1=0. Therefore equality of the full single-frequency maps is equivalent to BOTH equality of the normalized static maps and equality of q_H. This is a useful exact alternative to (7), not a theorem yielding nonuniqueness.

The inverse normalization is also explicit. Set k=H^(-1). Then a=sigma k^2 and

    L_sigma k=tau/k, k|boundary=1, q_H=-sigma partial_nu k. (14)

For positive uniformly elliptic sigma the positive solution k>=1 is unique: subtract two equations and test with their difference; the right side is -tau integral (k1-k2)^2/(k1 k2)<=0. Existence can be obtained by minimizing integral sigma|grad k|^2/2-tau log k over k>=1 with boundary1; the gradient term is coercive and -log grows subquadratically. Truncation/comparison and the bounded torsion supersolution yield an upper bound. Alternatively (14) is only needed for the k already produced by H. No new semilinear existence theorem is claimed.

Suppose one tries the source affine change k_new=c+(k-c)/rho while changing sigma to rho^2 sigma. Off the compact limiting source set, L_sigma rho=0, so the exact differential identity gives

    L_(rho^2 sigma) k_new=rho L_sigma k=tau rho/k.

To retain the same known mass in (14) one needs tau/k_new. The defect there is

    tau(rho/k-1/k_new)=tau c(rho-1)/(k k_new).            (15)

For c>0 and nontrivial rho this generally does not vanish even off the source. On the source set there is also the term -(k-c)L_sigma rho, and the harmonic cancellation (2) is not known for k solving (14). Thus the stronger ground-state route requires solving an additional exact nonlinear conormal constraint. This is a failure of that proposed intertwiner, not a no-go theorem for other constructions. Neither (15) nor the rank-two calculation proves that (7) is insoluble.

## 6. Infinitesimal and compactness routes were checked at their actual strength

The coefficient map h -> gamma(1+w_h)^2 is analytic into L-infinity near zero. Lax--Milgram resolvent inversion makes its DN map at -tau analytic into bounded trace operators. Its derivative in a charge direction eta is the usual weak Alessandrini formula

    d Lambda_(-tau)[eta](f,g)
      =2 integral gamma w_eta grad(P_gamma(-tau)f)
                                  .grad(P_gamma(-tau)g). (16)

To verify it, differentiate the solution weak equation. The solution variation has zero trace, so its contribution to the differentiated stationary boundary energy vanishes. At tau=0 the expression vanishes for every eta by exact static identity (3). At tau>0 the harmonic functions in (2) are replaced by resolvent-shifted functions. We have no all-input kernel/range theorem for (16) on the signed-charge space and no right inverse that could justify an implicit-function step. Counting charge parameters versus finitely many voltages would not establish one.

The infinite construction also does not remove a fixed macroscopic error by placing it deeper. A depth-j copy has diameter s^j, and the spectral term rescales to tau s^(2j). This makes its frequency error small. Its volume simultaneously scales as s^(3j); all depth-j cells have total volume (2s^3)^j |D|, tending to zero. Bounded coefficient changes confined there have L1 separation at most a fixed constant times that volume. Passing such approximations to a limit may erase the distinctness conclusion entirely.

This is not an obstruction to every possible diagonal construction. It specifies the missing **noncollapse plus exact operator matching** for that route. The compact signed-charge map in Section2 is why the parameter abundance alone is insufficient. We did not run finite numerical matching and mistake it for the full continuum equation.

## 7. Strongest primary comparison and outcome

The primary Green/resolvent calculation is already explicit in BR2012v2 Lemma2.4 and its proof. BR2020 Lemma3.3 restates it for an unbounded-domain setup and refers back to that proof. Its subsequent unitary-uniqueness theorem requires Lipschitz principal coefficients and an accumulating set of frequencies. It supplies neither a bounded-measurable two-frequency uniqueness theorem nor a contradiction to Source365. Its stronger scope was checked rather than inferred from the title.

GLKU2011, Proposition3.1's two-scale proof, Theorem4.1 and Corollary4.2's actual resolvent and outer-collar proofs, supply frequency-uniform **approximate** isotropic cloaking away from exceptional spectrum. Their Theorem4.3 explicitly allows loss of a uniform positive lower bound in the final approximation. This is credited as a stronger approximation route than a naive single-frequency small-ball estimate. It does not select two fixed nonsingular scalar coefficients with exact equality and a known unchanged unit density. No conversion of those limits into (7) was found. The primary's entire transitive Gamma-convergence and two-scale literature was not reread; no literature exhaustion claim follows.

The old I07 regularity/smoothing target and all supplied protected scopes remain unchanged. This round's full two-frequency attempt is unproved. Equations (3)--(16) are feasibility/reduction calculations, mostly classical/source compositions. They are not a frozen supporting replacement, not an independently reviewed mathematical result and not an acceptance candidate.

**PREFREEZE / NO NOMINEE.** What remains is an actual nontrivial solution of the full operator matching equation (7), or an alternative fully controlled construction paying the equivalent spectral/ground-state compatibility, while retaining fixed positive scalar ellipticity, the common unit density, an outer unit collar, and positive-volume distinctness. Neither feasibility nor a nonroutine successful operation has closed. The work does not show that the target is impossible, new to the world, or the only remaining direction.
