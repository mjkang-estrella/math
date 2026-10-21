# Integrated Source015 reduction and exact remaining work
Status: PREFREEZE / no nominee. No full author theorem is asserted, no statement frozen, no self-assigned correctness/contribution/acceptance gate. This is the unchanged r84 all-order primitive sextic direction, not a newly named conjecture. The aim of the sustained calculation was to go beyond its local Fourier identity, not to count an old parked quantifier.

## Same-packet arithmetic, with exact normalizations
Use notation M=O_K, O an order, D=Disc K, q=[M:O], Delta=Dq^2, X=Q=q sqrt(D), kappa=Res zeta_K(1). The full packet uses every invertible O-ideal class, every coordinate sign and orbit-volume weights. The actual primary ELMV packet proof and source prime/quartic models distinguish this one local homothety class from all proper O-modules.

The paired unfolding in feasibility.md is exact as an extended nonnegative integral. For a fixed nonzero product z=d ell in O^vee, it sums over maximal-order ideals b=(d)I^-1 with BOTH containment requirements imposed through the SAME local label. In local self-dual measure, the product-law density satisfies

  alpha_p(z):=sum_(b_p valuations) P_p(b_p,z)
       = |D|_p^(-1/2) c_p^(-1) f_p(z),
  c_p=product_(P|p)(1-NP^-1).

Here the action (x,y)->(a x,a^-1 y) has fiber measure dx/|Nx|; its maximal-unit coset has mass |D|_p^(1/2)c_p. The order-index contribution disappears because vol(O_p)vol(O_p^vee)=1. It remains in f_p. Global ideals parametrize the valuation assignments once, with the class and unit orbit already removed by unfolding, so there is no missing global coset multiplicity factor. The 32-fold exterior-square ambiguity in the quartic source is not imported into this simpler product representation. This is compatible classical disintegration, not an independent new method.

Let S contain p|Dq and p<=7. Outside S, O_p=M_p is unramified and z is integral. The paired condition is exactly that b_p divide (z)_p; its multiplicity is product_(P|p)(v_P(z)+1). Since q O^vee is contained in M^vee and D M^vee is contained in M, Dq z is integral. If z is in a fixed bounded real box, its integral norm is at most C(Dq)^6. Consequently the product of the good-prime multiplicities is at most

  exp(C log X/loglog X).

For compact marked primal/dual boxes away from coordinate hyperplanes, their logarithmic fiber integrals are uniformly bounded. Summing the exact local identities at S therefore gives the tube-event upper reduction

  mu_O(tube) <= exp(C log X/loglog X) kappa^-1 C_S
     sum_(z in K, Tr z=m, z integral outside S, z in the real slab)
                       product_(p in S) f_p(z),            (A)
  C_S=product_(p in S)c_p^-1.

The sqrt(D) from local disintegration cancels the global sqrt(D). C_S has logarithm O(log X/loglog X), and kappa^-1 is O(log(3D)) by the compatible source primitive-field residue argument. We can choose the marked vectors so that m is NONZERO: for a chosen nonzero v, avoid its orthogonal hyperplane as well as all coordinate hyperplanes when choosing the dual lattice vector. A finite compact cover then gives only finitely many nonzero m. This permits use of the nonzero-trace profile setup, without discarding any packet points.

The real slab has bounded coordinates and one partial sum in an interval of width O(exp(-t)). The unweighted order trace-slice count from r84 alone cannot bound the density-weighted sum in (A). A large density at sparse products is exactly what that replacement would ignore.

## Strong compatible profile reduction, with dimension-six budgets
The entire quartic local-fourier.tex (680 lines) and additive.tex (861 lines), and the complete exterior local disintegration/global-coset proof, were read. Its conductor-uniform inverse-support, boundary decay, scalar trace marginal, Poisson profiles, inverse-order congruences and adjugate polynomial method are all compatible candidates here. No failure of raw ideal coefficients or of independent-vector factorization excludes them.

The phase-free local calculation in local-shells.md supplies the relevant product-model shell data directly. For a global denominator profile h supported on S put H=Nh and G=product p^g, where p^g=[h_p:h_p intersect O_p]. Then

  G <= q <= HG.

Its inverse Fourier support gives, with an absolute fixed small-prime constant, a containing fractional ideal a_h with

  N(a_h)^-1 <= C D G^96.

Indeed at g>0 the local support loss 4(g+3) is at most 16g, and degree six multiplies that by six; the four small primes with g=0 contribute only a fixed constant. At the other primes the possible one-step boundary loss contributes T=product of the boundary prime-ideal norms. At a nonzero global point in a bounded box, the nonzero norm inequality therefore yields

  H <= C D G^96 T,    T <= (rad S)^6 <= C X^12.

Since D<=X^2 and G<=q<=X, only H<=X^111 can contribute for sufficiently large X. The number of these profiles is X^o(1) by Rankin and rad S<=C X^2. Each profile is Schwartz--Bruhat; Poisson is applied to this finite sum, not to an unproved absolutely convergent full nonscalar Fourier series. The scalar part is the actual trace marginal with coefficients p^-6k and is summable. None of this replaces the nonscalar sum by its absolute value before the inverse-shell split.

For a smooth real test with all five trace-plane scales >=X^-tau, the desired bound would follow from the nonscalar profile estimate

  sum_(H<=X^111) |sum_(A in K minus Q)
       phi_hat(A) product_(p in S) gamma_(p,h_p)(A)
       product_(p outside S) 1_(M_p)(A)| <= C X^-epsilon.  (B)

This is the exact prospective analytic interface; it is not declared proved here. The corresponding sufficient thin-slab inequality is

  sum_(Tr z=m, integral outside S) phi(z) product_S f_p(z)
       <= C (vol_5(support phi on Tr=m) + X^-epsilon),   (C)

uniformly in the primitive sextic field, order, compact box locations and stated shrinking scales. The five-dimensional volume uses any fixed deleted-coordinate parametrization. Bounded changes of coordinates cover each of the finitely many partial-sum cuts.

The source's three-way proof of (B) has a plausible dimension-six balance, substantially more specific than an unspecified Fourier bridge:

* Large D>=X^d. A nonscalar frequency generates K by primitivity. With norm-denominator H and |A|<=Y=X^w, clearing denominators gives D<=C(HY)^30, so H>=c X^(d/30-w). The ideal lattice has covolume sqrt(D)/H and first minimum >=c H^-1/6. Its count is bounded by sum_(k=0..5)Y^k H^(k/6)+Y^6 H/sqrt(D). Multiplication by the shell H^-1 saves a power with sufficiently small w/d.
* Small D and small G<=X^e. Since Delta=X^2, the deliberately weaker q>=X^(1/3) is available for d small. Thus H>=X^(1/3-e). Count the ORIGINAL inverse-support points by O(DG^96) and use the boundary saving (even its weaker square-root form). This gives exponent at most -1/6+(3/2)d+(289/2)e, after an X^o(1) cost. Subtract the separately bounded scalar series rather than discarding cancellation in a Fourier sum.
* Small D and large G. Shift A by an integral scalar separately at each p and put beta=(A+s)^-1. Let J=product p^j with p^j beta in O_p. The direct shell bound is H^-1 J^-1 (we may weaken it to H^-1 J^-1/2). Large J is small pointwise. For small J, discriminant divisibility of Z_p[p^j beta] inside O_p, together with disc(beta)=disc(A)/N(A+s)^10, gives
     |disc(A)| >= c Delta J^-30 H^-10,
  with only fixed small-prime constants, while |disc(A)|<=C Y^30. Hence H>=c X^(1/10-3(w+e2)) using only Delta>=X. One large Smith coordinate gives inverse congruence depth at least g/6-j; inversion permutes finite-algebra units. The large-prime numerator ell(adj(M_x)1) has degree at most five and is nonzero even for a residue algebra with nilpotents. Its zero count in a six-dimensional coordinate cube is O(L^6/p+L^5). Small-prime congruences require a fixed extra modulus because beta may have a bounded negative valuation. This is the same source inverse-order/adjugate operation, not a new obstruction or a new literature claim.

The finite diagnostic verifies rational slack for d=e=1/10000, e1=e/100, e2=e1/100, w=e2/1000, tau=w/100, epsilon=e2/4, including all six lower-dimensional lattice terms and a real Fourier tail using 1000 integrations by parts. Numerical slack does NOT prove (B): the uniform scalar removal and grouped congruence count must be assembled as actual estimates with their normalization, profile multiplicities and small-prime moduli in this six-dimensional product setting. That all-data assembly has not been completed as a full author proof in this packet. The budget removes an apparent exponent obstruction; it is not a theorem certificate.

## Compatibility with the dynamical endpoint and remaining scope
Source sextic conditioning.tex explicitly starts with arbitrary A-invariant probabilities converging to a probability, not a field-discriminant axiom. Its assembly needs a uniform cusp power bound, an O(r^6) ordinary-ball bound on limits, and the tube estimate throughout a growing interval with diverging endpoint ratio. Prime-companion weighted counts and the old I145/UI145 calculation (with primitivity paying no quadratic subfield and primitive generators) pay the ordinary estimates for order-local-type packets; a bounded third cusp moment gives the required uniform cusp power.

If (C) were supplied with a fixed positive tau,epsilon, choose
 T_-=log Delta/(loglog Delta)^(2/3),
 T_+=log Delta/(loglog Delta)^(1/3).
For all t in this interval, exp(-t)=X^-o(1) exceeds X^-tau, and X^-epsilon is negligible. The exp(O(log X/loglog X)) overhead in (A) is exp(o(t)), so the bound becomes <=exp(-t/3) after increasing the threshold. This matches the actual source cut bound, including finite families of cuts and bounded dominated starting laws. No one-copy root argument is applied to r51's two-copy problem, and no class-selective estimate is inferred for C145.

The full internal conditioning/product/activity/entropy proof chains have NOT all been semantically reread; their published lower operations are stipulated, and only the recorded interfaces/assembly and selected operative passages were read. That limitation remains part of the non-nomination.

## Research decision
The exact unfinished assertion in this packet is (B), which is a sufficient route to the all-order weighted thin-slice estimate (C), followed by a fully checked reuse of the source dynamical endpoint. It is not just the old unspecified global-pair gap: exact same-packet unfolding, local disintegration, phase-free inversion, inverse supports, profile cutoff and a workable exponent budget are now written down. But these advances are classical/source-compatible operations. No identifiable nonroutine operation beyond the strongest composition has been established. Completing this parked quantifier or writing a long dimension-six version would not by itself provide substantial-contribution evidence. Thus no full result is frozen or nominated. There is no assertion that (B) is impossible, currently open worldwide, beyond all classical methods, or necessarily nonroutine; the calculations favor compatibility rather than an obstruction.

Old scopes and dispositions, including r84, C145/I148, r51, SHGH/W136 and all specified protected full targets, remain unchanged. No bounded-conductor, fixed-field, Gorenstein, split-prime or other restricted substitute is offered.
