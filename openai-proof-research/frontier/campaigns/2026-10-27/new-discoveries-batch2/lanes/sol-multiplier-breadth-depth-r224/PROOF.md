# Ordinary proof candidate: the square-root factorial multiplier

Research date 2026-10-30 UTC. No independent review, acceptance, Lean or manuscript. Only the multiplier question is proved here; CZDS is not asserted.

## Literal endpoint and primary dependencies

For every real polynomial p(x)=sum p_k x^k having only real zeros, sum (sqrt(k)/k!)p_k x^k has only real zeros (with the usual convention allowing the zero polynomial).

Csordas–Forgács, https://arxiv.org/pdf/1505.00355v2, 26 August 2015: Definitions 2–7 and Theorem 6 on PDF pp1–2; Section3.1 pp9–11; Problem39(a),(b) p16. Theorem6 identifies the desired endpoint with F(x)=sum_{k>=1} sqrt(k)x^k/(k!)² belonging to LP+. Lemma21 proves only Hurwitz stability, not the desired real-zero conclusion.

A second primary body used here is Cho–Park, https://arxiv.org/pdf/2110.01885v1, 5 October 2021, Theorem2.1 pp4–6 and equation(3.4), PDFp8. We use its exact Fourier partial-fraction identity, and give the needed no-nonreal-zero argument below. Its introduction's positive-real-zero distribution alone would not suffice. Both PDF and extracted text are frozen in this lane; retrieval receipts give hashes.

## 1. Integral representation with the exact coefficients

Write H(z)=F(-z²/4)/(-z²/4), with its removable value H(0)=1. Since

 sqrt(n+1)/((n+1)!)² = 1/((n!)²(n+1)^(3/2))

and Gamma(3/2)=sqrt(pi)/2, termwise integration gives

 H(z) = (2/sqrt(pi)) integral_0^1 sqrt(-log u) J0(z sqrt(u)) du.

Indeed integral_0^1 u^n sqrt(-log u)du=Gamma(3/2)/(n+1)^(3/2). On every compact complex z-set, the Bessel series converges absolutely and uniformly for 0<=u<=1, and sqrt(-log u) is integrable. Thus this identity and the changes of integration below hold as identities of entire functions, not just on the real axis.

Use the elementary arcsine integral

 J0(z sqrt(u))=(2/pi) integral_0^{sqrt(u)} cos(zt)/sqrt(u-t²) dt.

It follows by integrating the cosine series and the beta integral, so requires no zero-location assumption. Absolute integrability follows from boundedness of cos on compact z-sets and the nonnegative arcsine kernel. Define

 K(t)=integral_{t²}^1 sqrt(-log u)/sqrt(u-t²) du
     =2 integral_0^{sqrt(1-t²)} sqrt(-log(t²+v²)) dv,  0<t<1.

Then

 H(z)=4/(pi sqrt(pi)) integral_0^1 K(t)cos(zt)dt.                  (1)

The endpoints are K(1)=0 and K(0)=sqrt(2pi).

## 2. The decisive monotonicity lemma

Let h(t)=-K'(t). Differentiation gives

 h(t)=2t integral_0^{sqrt(1-t²)} dv/((t²+v²)sqrt(-log(t²+v²))).    (2)

This differentiation is valid locally for 0<t<1: the original integrand vanishes at the moving upper endpoint, and its differentiated integrand has an integrable inverse-square-root singularity there. One may truncate away from that endpoint and pass to the limit uniformly on compact subintervals of t in (0,1). At v=0 there is no singularity for such t.

Put a=-log t>0 and v=t tan(theta). Then put r=-log cos(theta). Equation(2) becomes

 h(e^-a)=sqrt(2) integral_0^a dr/(sqrt(a-r)sqrt(e^(2r)-1))
        =integral_0^1 g(au)/sqrt(u(1-u)) du,                    (3)

where g(r)=sqrt(2r/(e^(2r)-1)), with g(0)=1.

For r>0, g is strictly decreasing. For example, the numerator of the derivative of 2r/(e^(2r)-1) is 2[e^(2r)(1-2r)-1], strictly negative since the bracket has value0 at0 and derivative -4r e^(2r)<0. Also 0<g(r)<=1. Thus (3) implies h(e^-a) strictly decreases in a, equivalently h(t) strictly increases in t. Dominated convergence against [u(1-u)]^-1/2 gives

 h(0+)=0, h(1-)=pi, and 0<h(t)<pi for 0<t<1.

Consequently K is absolutely continuous on [0,1], with derivative -h. To justify the endpoint assertion without assuming it: apply the fundamental theorem on compact subintervals, use h bounded, then pass to the endpoint values of K. Integration by parts in (1) yields

 H(z)=4/(pi sqrt(pi) z) V(z),  V(z)=integral_0^1 h(t)sin(zt)dt.  (4)

The quotient at z=0 is removable. In particular F(-z²/4)=-z V(z)/(pi sqrt(pi)).

## 3. Why V has no nonreal zeros

For completeness, the needed classical sine-transform implication is derived explicitly. For every positive integer k,

 c_k=(-1)^k V(kpi)/(kpi)<0.

Indeed substitute t=1-s: V(kpi)=(-1)^(k+1) integral_0^1 h(1-s)sin(kpi s)ds. The latter integral is strictly positive for a strictly decreasing positive function. Pair consecutive sine half-waves; their contributions are positive differences, with a positive remaining half-wave when k is odd. This also follows from Cho–Park Theorem2.1. Strict increase ensures none of the values V(kpi) vanishes.

Cho–Park equation(3.4), valid for every integrable kernel, states

 V(z)/(z sin z)=V'(0)/z + sum_{k>=1} c_k[1/(z-kpi)+1/(z+kpi)].

After multiplication by z, with w=z², this is

 V(z)/sin z = V'(0)+sum_{k>=1} 2c_k w/(w-k²pi²).              (5)

The series converges locally uniformly away from its poles. In this instance h is bounded and monotone, so integration by parts in the Stieltjes sense gives V(kpi)=O(1/k), hence c_k=O(1/k²); local convergence and taking imaginary parts are therefore justified directly.

If Im(w) !=0, the imaginary part of the kth term on the right of(5) is

 -2 c_k k²pi² Im(w)/|w-k²pi²|²,

which has the strict sign of Im(w). The real constant V'(0) contributes nothing. Thus (5) cannot vanish when w is nonreal. If z is nonreal but w is real, z must be purely imaginary: for z=iy with real y!=0,

 V(iy)/sin(iy)=integral_0^1 h(t)sinh(yt)dt/sinh y>0.

These exhaust the nonreal possibilities. At the real poles kpi the original V is nonzero. At0 it has a simple zero since V'(0)=integral_0^1 t h(t)dt>0. Hence every zero of V is real.

## 4. Entire LP+ endpoint, not merely a finite test

Equation(4) shows that every nonzero zero x of F must be negative real: choose a complex square root z of -4x; then V(z)=0, so z is real and x=-z²/4<0. Also F has a simple zero at0.

The coefficients a_k=sqrt(k)/(k!)² give order exactly1/2 by the coefficient formula rho=limsup k log k/log(1/|a_k|) and Stirling's formula. Hadamard factorization at order<1 therefore gives a genus-zero product

 F(x)=c x product_j(1+x/r_j), r_j>0, sum_j 1/r_j<infinity.

There is no nonconstant exponential factor at order<1. Since F'(0)=1, c=1. Finite products with the same form have only nonpositive zeros and converge locally uniformly to F; all coefficients of F are nonnegative. Thus F belongs to LP+. Pólya–Schur, in the literal Theorem6 of the question source, proves that {sqrt(k)/k!}_{k>=0} is a classical multiplier sequence. This completes the stated ordinary theorem.

## Scope, strongest adaptation objection and novelty limits

The proof uses a classical Pólya Fourier-transform mechanism. The potentially substantive bridge is the exact kernel formula(3), including its exponent3/2 and monotonicity. Applying sqrt(k) to a multiplier sequence without this bridge is invalid; integer-power closure supplies no substitute. A reviewer should check every constant, moving-endpoint differentiation, partial-fraction multiplication and order argument. The independent exact finite checks are supportive only, not used in the universal argument.

This may be a short classical corollary once the kernel is recognized; root must adjudicate substantive credit. We do not assert worldwide novelty or acceptance. Bounded 14,268-body campaign alias screening found the r223 nomination and unrelated Csordas citations, not a previous proof of this literal object. Current arXiv searches and actual later multiplier-body inspection do not clear all citing papers or contemporary proof registries. The old inaccessible registry intervals remain parked. Problem39(b), the CZDS assertion for arbitrary numbers of nonreal zeros, remains unproved and is not implied by this argument.

**Critical historical qualification found after drafting:** Baricz–Singh https://arxiv.org/pdf/1702.00626v1, Theorem6 (PDFp6), explicitly asserted the stronger statement eta_s=F_s in LP+ for every s>0. Its proof (PDFp10) treats z^s/Gamma(z+1) as entire and in LP, which is false for nonintegral s; the all-s assertion also conflicts with the question source's Example20. The CURRENT arXiv API identifies v2, updated16August2017; the frozen https://arxiv.org/pdf/1702.00626v2 omits Theorem6 and that proof entirely (five numbered main theorems remain). Thus this is a historical public assertion with a visible proof defect and later omission, not verified valid prior resolution. Do not suppress it, claim the target was never publicly asserted solved, or use it as a sound supplier. Root must evaluate the journal body and possible subsequent corrections before any novelty gate. OpenAlex lists the journal DOI https://doi.org/10.1090/proc/13927; that final journal body has not been checked here. The 2018 Al-Hamdani–Leon actual paper proves product-generated multiplier identities (Theorems3.5/3.8), not this radical endpoint.
