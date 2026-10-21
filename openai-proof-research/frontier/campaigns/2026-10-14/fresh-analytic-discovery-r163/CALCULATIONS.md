# Prefreeze Vlasov–Maxwell calculations

Authorized Codex / GPT-6 Astra / high / default service tier. Campaign 19/20, latest R041 is supplied context. Parent alone adopts grades and counts. This is a working notebook, not a frozen statement.

## Direction selected after operative reading

The completed original density-weighting supplement mapped in private/COMPARISON.md already considers full Schwartz momentum tails, uniform displacement, and polynomial label growth. Its coupled all-receiver-scale bootstrap is not reopened. The present direction keeps compact initial momentum support and examines low regularity of the initial fields and particle density.

The source's retarded data term uses a uniform pointwise bound on homogeneous waves, obtained from bounded initial field derivatives. The remaining cone-energy, density, occupation and direct estimates read so far depend on initial particle mass/energy, density supremum, and support, not derivatives of f. Primary R's published Section 4.2.2 already estimates the homogeneous electric wave along timelike characteristics through the expanding-sphere Jacobian. Its published rough-solution construction is in Section 4 before subsection 4.1. These are actual body reads, not inferences from the abstract.

## A sharper local-in-time form of the primary radiation operation

Let X be C1, |X'|<1, X(0)=x0. For smooth F0,G0 define

 W(t,x)=M_t F0(x)+t M_t(n dot grad F0)(x)+t M_t curl G0(x).

For a measurable time set A in an interval of length I, suppose (1-|X'(t)|^2)^(-1/2)<=8w on A. The map (t,n) -> y=X(t)+tn is injective for t>0 and has Jacobian J=t^2(1+n dot X'(t)). Indeed the balls B(X(t),t) are strictly nested; each fixed y meets at most one boundary. For any t>0, |y-x0|<=2t.

The derivative terms are bounded by Cauchy–Schwarz using J:

 integral_A integral_S2 t |grad F0(y)| dn dt
 <= ||grad F0||2 [integral_A integral_S2 (1+n dot X')^(-1) dn dt]^(1/2).

The same holds for curl G0. For the zeroth-order term insert t and 1/t. The first squared factor becomes integral_image |F0(y)|^2/t(y)^2 dy, which is at most 4 integral |F0(y)|^2/|y-x0|^2 dy <=16||grad F0||2^2 by the translated three-dimensional Hardy inequality. Thus it has the same bound. The angular integral is exactly (2pi/b) log((1+b)/(1-b)), b=|X'|, with its continuous value 4pi at b=0; it is <=C log(2+w). Consequently

 integral_A |W(t,X(t))|dt <= C sqrt(I log(2+w)) (||grad F0||2+||grad G0||2).       (R)

This bounds absolute radiation, hence both its signed vector impulse and every transverse projection. It uses no acceleration of X, no field sup norm, and no derivative of f0. It applies to any measurable A, even when the receiver leaves its w-band at other times. Initial-time Hardy control is centered at X(0), not at the beginning of A, so it also applies to intervals away from zero without restarting the coupled solution.

For source P>=1024 times the current support and I<=(w/P)^2, sqrt(log(2+w))<=C P; thus (R) costs at most C P sqrt(I). The initial particle boundary term remains <=C(T,P_initial,||f0||infinity) I. This fits the precise source direct-estimate format. It is not yet a completed theorem: all downstream uses of pointwise data bounds, direction counting, signed selection and bootstrap initialization must be checked.

This operation is a refinement of the actual primary expanding-sphere/Holder argument plus Hardy, rather than a presently demonstrated substantial new mechanism. The comparison must retain the primary operation even if the displayed published coarse exponent is weaker.

## Downstream compatibility now checked in the complete source

All ten operative source sections have now been read in full. There is no additional proof companion cited as a premise of the signed construction. The figure includes are diagrams only and were authenticated/read separately. The initial-cone boundary in the signed formula is bounded using only initial momentum radius, f0 supremum and horizon. The direction proof uses the baseline data term only through the integral of the full force over the union of its disjoint intervals, plus the bounded projection. Thus (R) is used ONCE on this union, with length at most I; there is no sum of square roots of individual interval lengths. The final selected receiver coefficient is C/sqrt(w), and the absolute-force loss is sqrt(w), exactly as in the source. No angular exponent or selection inequality changes.

Bootstrap initialization uses the smooth approximation's finite compact-slab force bound solely for openness. That bound may diverge as the approximation parameter goes to zero. It does not enter M, A or the lower threshold P0. The constants in the strict improvement may instead be chosen from T, initial mass/energy, initial momentum radius, ||f0||infinity and ||F0||H1. This is the uniformity needed for an actual approximation, rather than just individual global existence for every cutoff.

A later primary read of primary L Proposition 5.2 and its proof supplies the same logarithmic expanding-sphere estimate. This further reduces the additional content of (R): the derivative term is literally that classical L2 change-of-variables calculation; the zeroth-order term is paid by translated Hardy. No claim of a new substantial trace theorem is justified by the improved-looking displayed exponent.

## Uniform finite-horizon cap: the harmonic sum can be made uniform

For a family of smooth admissible data with common bounds just listed, let n0 exceed both the common initial dyadic momentum and the uniform threshold P0. On a first crossing from 2^(n-1) to 2^n, use P=1024*2^n and w=2^n. Long intervals are already covered by the trivial band bound |Delta V|<=16w after M>=16; the strict improvement covers short intervals. The full signed inequality therefore implies

  1/2 <= 1024 M sqrt(Delta_n) + 1024^2 A Delta_n log(2+1024*2^n).

Therefore Delta_n >= min((4096M)^(-2), [4*1024^2*A*log(2+1024*2^n)]^(-1)) >= c/(n+c0),

with common c>0 and c0. Successive first-crossing intervals are disjoint in increasing order. If level 2^N is reached by T, then

  T >= c sum_(n=n0+1)^N 1/(n+c0)
    >= c log((N+c0+1)/(n0+c0+1)).

Consequently N <= (n0+c0+1) exp(T/c), and a common finite cap Q_T follows. Here c and n0 may depend on the fixed horizon T through the source constants; this is NOT a uniform-in-time double-exponential theorem. The estimate is uniform in approximation index and in initial spatial cutoff radius.

## Proposed approximation and its Gauss correction

For 0<=f0 in L1 intersection Linfinity, supported in |v|<=R0, and F0=(E0,B0) in H1 satisfying the two Gauss constraints, spatial cutoff must change E0. Let f0,R=chi_R(x)f0 with 0<=chi_R<=1, and sigma_R=rho0-rho0,R. Then sigma_R ->0 in L1 and L2: rho0 is bounded by C R0^3 ||f0||infinity and belongs to L1. Hence sigma_R ->0 in L^(6/5). Define C[sigma]=-grad(-Delta)^(-1)sigma, so div C[sigma]=sigma. Sobolev duality gives ||C[sigma]||2<=C||sigma||_(6/5), and the Fourier multiplier gives ||grad C[sigma]||2<=C||sigma||2. Set E0,R=E0-C[sigma_R], B0,R=B0. These obey the truncated density constraint and converge in H1.

Now convolve f0,R in x and v with nonnegative compactly supported unit-mass kernels, and convolve E0,R,B0,R with the SAME x kernel. Velocity convolution preserves the density integral, so Gauss remains exact. Every approximate datum is smooth admissible; the particle support is compact, initial velocity radii are <=R0+1, and initial mass, phase-space density supremum, energy and field H1 are uniformly bounded. Thus the preceding Q_T applies to the actual coupled approximate solutions. This does not split the total Maxwell field among particle shells and has no cross-work defect.

This construction concerns compact initial momentum with possibly noncompact spatial support. It does not prove the old full Schwartz-momentum target.

## Subsequent completion and limits

REDUCTIONS.md §§6–9 completes the compatible nonresonant field compactness, coupled limit, renormalized initial traces, exact energy balance and comparison against a smooth source solution. These were developed after the feasibility notes above; the earlier words “proposed” and “not yet” record that chronology, not the final extent. No theorem was frozen because no additional closed nonroutine operation was identified after the primary reductions. The rough-rough and unrestricted finite-energy comparison obligations remain unproved.
