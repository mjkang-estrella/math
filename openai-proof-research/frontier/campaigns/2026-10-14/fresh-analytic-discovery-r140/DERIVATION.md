# PREFREEZE working derivation: endpoint evolution under potentials

Codex / GPT-6 Astra / high / default service tier. No nominee or contribution verdict. The initial family budget is Source080 endpoint Schrödinger convergence, plus Source079 local smoothing at navigation level only. Pin and operative proofs stipulated true.

## 1. Source interface and an initially tempting false gap

Let n>=2 and s=n/[2(n+1)]. Both pinned Source080 companions give the translated-unit-ball bound

    integral_B sup_{0<=t<1} |exp(it Delta)f| <= C_n ||f||_{H^s}.

The planar 09-endpoint proof (dual localization, heavy-child summation, linearization, approximation) and higher-dimensional endpoint proof explicitly give one common time graph and the Sobolev square norm. Their final representative argument has one exceptional set for all times. We do not reprove the source or infer a potential theorem from its catalogue.

Consider H=-Delta+V with real V in L∞. Direct Duhamel plus this maximal bound would ask for integral ||V u(t)||_{H^s}dt, which boundedness of V alone does not give. This is a failed route, not a missing operation: time-independent V commutes with temporal fractional differentiation, and the full equation supplies one modulation derivative.

## 2. Compatible modulation transfer closes bounded potentials

Set u(t)=exp(-itH)f, z(t)=eta(t)u(t), with eta smooth supported in (-2,2), equal to one on [0,1]. For 0<=s<1 choose 1/2<b<=1-s/2. Use the free Bourgain norm

    ||z||_{X^{s,b}}² = integral <xi>^{2s}<tau+|xi|²>^{2b}|zhat(xi,tau)|² dxi dtau.

The scalar inequality <xi>² <= C <tau><tau+|xi|²> gives

    <xi>^s <tau+|xi|²>^b
       <= C <tau>^{s/2}<tau+|xi|²>^(b+s/2)
       <= C <tau>^{s/2}<tau+|xi|²>.

Hence Plancherel gives

    ||z||_{X^{s,b}} <= C (||z||_{H_t^{s/2}L_x²}
                          + ||(i partial_t+Delta)z||_{H_t^{s/2}L_x²}).

The forcing is eta V u+i eta' u. Since V is bounded on L² and independent of time, this is controlled by the temporal Sobolev norms of cutoffs of u. The spectral theorem gives, for a fixed smooth compact cutoff chi and alpha=s/2,

    ||chi(t) exp(-itH) f||_{H_t^alpha L_x²}
        <= C_chi,alpha ||(1+|H|)^alpha f||_2.

Indeed integrate |chihat(tau+lambda)|²<tau>^{2alpha} first in tau against the spectral measure; <tau>^alpha <= C<lambda>^alpha<tau+lambda>^alpha. Fubini applies to nonnegative integrands. Bounded selfadjoint perturbation makes D(H)=H² with equivalent graph norms; complex interpolation between L² and these domains yields D((1+|H|)^{s/2})=H^s, equivalently using a positive shift H+c>=1. No H^s multiplier property of V is asserted.

Consequently ||eta u||_{X^{s,b}} <= C(n,s,b,||V||∞)||f||_{H^s}. This is not a frequency-by-frequency triangle estimate.

The standard transfer principle now applies to the source L¹_x L∞_t estimate: write z(t)=integral exp(it lambda) exp(it Delta)g_lambda d lambda with ghat_lambda(xi)=zhat(xi,lambda-|xi|²), ignoring the fixed Fourier normalization. Minkowski, then Cauchy--Schwarz in lambda, give

    ||sup_[0,1] |z(t)||_{L¹(B)}
       <= C integral ||g_lambda||_{H^s} d lambda
       <= C_b ||z||_{X^{s,b}},

because integral <lambda>^{-2b}<infinity. This composes at the EXACT s=n/[2(n+1)]<1. There is no endpoint epsilon or regularity debt for bounded time-independent potentials. The high spatial frequencies created by rough V are paid by modulation, not spatial derivatives of V.

This establishes feasibility of the full bounded-potential extension, but the whole operation is standard spectral calculus, the equation identity, and modulation transfer. It is not frozen or offered as a substantial theorem. Primary/history comparison is still in progress; no new-to-literature claim.

## 3. Actual stronger issue to test

At unbounded scale-critical V in L^{n/2}, n>=3, multiplication is bounded H¹ -> H^{-1}, rather than L² -> L². The preceding estimate cannot be reused with that domain silently. A source-critical maximal bound for the perturbed evolution would need an additional compatible spatial/temporal estimate. This is exploratory; no full scope has yet been frozen and no assertion is made that every classical construction fails.

## 4. Representative and comparison details for the paid bounded case

The modulation superposition is initially justified for smooth compact frequency/modulation data. The free maximal estimate makes it a bounded map X^{s,b} -> L¹(B; C([0,1])) (use a cutoff equal to one on a slightly larger closed interval). Approximation in X^{s,b}, summable differences, and a countable covering by balls give a representative continuous on every time line outside one spatial null set. The usual X^{s,b} -> C_t H^s_x embedding, proved by the same Cauchy--Schwarz modulation integral, identifies its L² class at each fixed time, including zero. This avoids any uncountable intersection of fixed-time exceptional sets.

Spatial Gaussian smoothing of the resulting L² evolution also converges uniformly in time outside one null set. Apply the actual source Gaussian-envelope proof to smooth spacetime approximations of z in X^{s,b}. The local L¹ norm of each supremum error envelope is uniformly bounded over ball centers. The source Gaussian approximate-identity lemma applies to the countably many envelopes. For each smooth spacetime approximation its spatial Fourier transform is integrable uniformly in time; its Gaussian error tends to zero uniformly. First send Gaussian scale to zero and then approximation index to infinity. Spatial smoothing is applied AFTER the perturbed evolution; exp(a Delta) does not commute with exp(-itH), and no commutation is used.

The hypothesis V independent of time is essential to this particular calculation. A merely bounded time-dependent V need not preserve H_t^{s/2}; replacing it by that larger class is not an established result here. This is not a frozen secondary target.

Choi 1907.11966v3 is an actual antecedent: Sections 3-4 use Bourgain-space potential estimates and the Duhamel smoothing route in one dimension, with an L² or W^{1,infinity} intersect L^rho potential hypothesis. Lemma l:43 differentiates the interaction representation and estimates the potential product in spatial H^s. Our bounded-potential calculation moves the fractional factor to temporal frequency and spends unused modulation regularity; it does not claim that Choi's printed theorem already states the all-dimensional arbitrary-L∞ conclusion. The finite displayed weight inequality, spectral theorem, and usual transfer supply the entire additional reduction. No substantial-contribution claim follows simply from removing a derivative assumption in that comparison.

## 5. Wave-operator structure gives another compatible classical reduction

In R³ write the corrected Beceanu--Schlag representation as

    W h(x)=h(x)+integral g(x,dy,omega) h(S_omega x-y) d omega,
    G=integral ||g(.,dy,omega)||_{M_y L∞_x} d omega < infinity.

The strong mixed measure norm means a total-variation majorant independent of x, with finite integrated mass. Taking the supremum in time INSIDE each transformed field, then Tonelli and invariance of balls under reflections/translations, gives

    sup_z integral_{B(z,1)} sup_t |W v(t)(x)| dx
      <= (1+G) sup_z integral_{B(z,1)} sup_t |v(t)(x)| dx.

This uses actual structure, not an invalid inference from scalar L¹ boundedness of an arbitrary nonpositive operator. With the intertwining identity

    exp(-itH) P_ac f = W exp(it Delta) W* f,

the source estimate applies once W* is bounded on H^s. For the corrected B^{1+} class (1612.07304v3, thm:struct), V lies in L^{3/2}: on each exterior shell Hölder gives ||V||_{3/2,shell} <= C 2^{j/2}||V||_{2,shell}, and the interior ball has finite volume. Splitting an L^{3/2} potential into a small L^{3/2} part and a bounded part gives infinitesimal form boundedness, hence the shifted form norm is equivalent to H¹. Interpolation gives the fractional form scale H^s for 0<=s<=1. The L² wave isometry and spectral intertwining give

    ||W* f||_{H^s} <= C_V ||f||_{H^s}, 0<=s<=1.

The source exponent in R³ is 3/8, safely inside this range. A finite pure-point spectral part, when present, is handled directly by its finite eigenfunction expansion; locally L¹ follows from L² of each eigenfunction. No differentiability of the structure coefficient g is required for the OUTPUT maximal norm. Thus this existing structure formula and the form scale pay the continuous-spectrum maximal extension at their true hypotheses. The explicit representation preserves continuity in time by integrable domination of the free maximal envelope.

The corrected large-potential theorem requires B^{1+} and a zero-energy condition; the old 1101.0502 critical-class claim cannot silently replace it. The companion 1701.03015v1 provides a small scaling-invariant class, but its norm is ||V||_B + ||V||_{dot B^{1/2}}, with the plane-slice norm B defined in def:trip. It is not plain L^{3/2}. Its proof explicitly pays iteration using the plane-slice estimate (eq:key), Banach algebra, and geometric Born series. The source endpoint adds no new iteration operation within those classes.

The exploratory pure L^{3/2} class contains epsilon |x|^{-a}1_{|x|<1}, 3/2<=a<2, with arbitrarily small L^{3/2} norm. Such a potential is not locally L², so is outside the corrected inhomogeneous B^{1+} assumption. This observation only separates that assumption; it does NOT prove failure of a structure formula for the potential, nor nonmembership in every alternative scattering class.

## 6. A concentrated-potential test for a tempting critical Bourgain contraction

A natural stronger route would prove

    ||V z||_{X^{s,b-1}} <= C ||V||_{L^{n/2}} ||z||_{X^{s,b}}     (C)

uniformly over real potentials, with b>1/2 so the source transfer applies. The following integrated scaling calculation rules out (C) for every fixed b>1/2, even for nonnegative smooth compactly supported potentials, and every fixed s>=0. It does not rule out the desired evolution estimate, other function spaces, or constants depending on more than the critical norm.

Take n>=3, a nonnegative nonzero smooth chi supported in (-1,1), and

    fhat_N(xi)=c_N chi(|xi|²-N²),   ||f_N||_2=1.

Polar coordinates give c_N comparable with N^{-(n-2)/2}. On bounded y sets,

    N^{-(n-2)/2} f_N(y/N) -> Phi(y)

in every fixed C^k norm. Indeed put q=|xi|²-N² in the radial integral, so r^{n-1}dr=(1/2)(N²+q)^{(n-2)/2}dq, and use compact q support and dominated differentiation. Phi is a nonzero constant multiple of integral_{S^{n-1}} exp(i y dot omega) d omega. In particular Phi(0)>0.

Choose a real nonnegative v in C_c^infinity in a small ball where Phi is nonzero. Put V_N(x)=epsilon N² v(Nx); then ||V_N||_{n/2}=epsilon||v||_{n/2}, independent of N. Choose a nonzero Schwartz eta with Fourier support in [-1,1], and set

    z_N(t,x)=eta(t) exp(-itN²) f_N(x).

Both input modulations satisfy |tau+N²|<=1 and ||xi|²-N²|<=1. Thus

    ||z_N||_{X^{s,b}} comparable with N^s.

Write F_N(y)=v(y)N^{-(n-2)/2}f_N(y/N). Then F_N -> v Phi smoothly with common compact support, and

    Fourier_x[V_N f_N](N zeta)
       =epsilon N^{(2-n)/2} Fhat_N(zeta).

Because v Phi is nonzero and compactly supported, its Fourier transform cannot vanish on the whole open annulus A={2<|zeta|<3}. Thus ||Fhat_N||_{L²(A)}>=c>0 for large N. Restrict the output norm to xi/N in A and |tau+N²|<=1. Here <xi>^s comparable with N^s and <tau+|xi|²>^{b-1} comparable with N^{2b-2}. Consequently

    ||V_N z_N||_{X^{s,b-1}} >= c epsilon N^{s+2b-1},
    ratio to ||V_N||_{n/2}||z_N||_{X^{s,b}} >= c' N^{2b-1} -> infinity.

For b=1/2 this test gives no divergence, but the ordinary modulation L¹ transfer has integral <lambda>^{-1}=infinity. Endpoint Besov modulation or atomic U² methods are compatible alternatives that this calculation does not dispose of. The test functions z_N are NOT claimed to solve the perturbed equation. In particular, failure of (C) is not a counterexample to a solution-specific estimate.

## 7. The critical form and endpoint Strichartz operations do compose, but have different output

For n>=3 and ||V||_{n/2} sufficiently small relative to the Sobolev constant, the real quadratic form

    q_V(h)=||grad h||²_2 + integral V|h|²

is closed on H¹, and its homogeneous part is comparable with ||grad h||²_2. After adding ||h||²_2, interpolate the square-root domain with L². This gives the full H^s form scale for 0<=s<=1 and uniform H^s persistence of the unitary evolution. Thus lack of a selfadjoint realization or H^s persistence is NOT the residual.

Let r=2n/(n-2), r'=2n/(n+2). Keel--Tao's actual retarded endpoint estimate, Theorem 1.2(7) with sigma=n/2 and both pairs (2,r), yields

    ||integral_0^t exp(i(t-a)Delta) F(a) da||_{L²_t L^r_x}
        <= C_n ||F||_{L²_t L^{r'}_x}.

Together with its energy-output version and Hölder,

    ||V u||_{L²_t L^{r'}_x} <= ||V||_{n/2} ||u||_{L²_t L^r_x},

this closes the small-potential L² Strichartz contraction (on a fixed finite interval, or globally), retaining the compatible form evolution by approximation/uniqueness. It is legitimate to use the retarded estimate with both endpoint pairs; this is not the invalid endpoint application of a generic time-truncation lemma.

However L²_t L^r_x output cannot simply be interchanged with L¹_x L∞_t output. Likewise the source free maximal estimate applied to Duhamel would require additional control of its forcing in a norm compatible with H^s. The preceding test disposes of one uniform Bourgain contraction, while the available Strichartz absorption remains fully credited. The derivation does not supply the needed retarded graph estimate for F=V exp(-itH)f. There may be a compatible atomic, resolvent, or graph-specific construction; no exclusion of those methods is claimed.

## 8. Exact stopping point

No full-scope result with an identified additional nonroutine operation has closed. The paid bounded-V modulation extension and paid structured-wave-operator extension are supporting calculations, not nominees or replacements for a stronger target. The unresolved operation is control of the perturbed common-time-graph maximal functional at source-critical regularity for a general small real L^{n/2} potential, beyond classes for which the cited structure theorem already applies. In R³ its concrete functional is

    integral_{B(z,1)} sup_{0<=t<=1} |exp(-it(-Delta+V))f(x)| dx

for f in H^{3/8}, with the canonical form evolution and a common time-continuous representative. A uniform bound in terms of a prescribed small ||V||_{3/2}, or even a sufficiently controlled V-dependent estimate permitting approximation, has NOT been established in this round. This is a precise research obligation, not a frozen conjecture or finding. No worldwide-open or priority claim follows from the bounded primary search.

## 9. Late relevant history read

After Sections 1-8 were developed, r45/weighted-tree.md was read in full. Its actual weighted descendant argument already yields local L^r maximal output for 2<r<min(p,2(n+1)/n), with the source's unspecified p>2. Both modulation transfer and the positive structure majorant above work with this stronger local output too. Thus the compatible known composition is stronger than merely the L¹ versions displayed here. This late read does not remove the critical-potential forcing obligation: it changes the output norm of the free transfer, while the missing potential control remains at the input/modulation interface. No L^r variant is nominated, and r45's unresolved finite-Schatten target and I66's singular-measure target retain all their old quantifiers.

Technical conventions: the closed time interval [0,1] is covered by two translated source intervals of length1, so no endpoint-time assertion is added without that covering. Section5 directly proves the continuous-spectrum transfer; a full pure-point addition requires its stated finiteness condition. A usual CLR justification for B^{1+} potentials was not separately read as a primary proof here and is not needed for the no-nominee conclusion.
