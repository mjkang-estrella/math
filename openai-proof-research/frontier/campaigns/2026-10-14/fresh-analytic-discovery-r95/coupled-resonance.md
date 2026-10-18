# Coupled resonance: exact ideal calculation and iteration boundary

Live author derivation, incorporating the parent's coupled-scale proposal. This is not a full-flow claim.

## Exact ideal shear

Let H_N be a smooth circle lift of integer degree, H_N'=N V, and let k be a positive integer. On a new orbit parameterized by w, put q=b+kw (mod 1), theta=w+H_N(q) (mod 1). For a physical clock Fourier mode chi(q) exp(2 pi i l theta), the orbit average is

 I_l(b)= integral_0^1 chi(b+kw) exp(2 pi i l[w+H_N(b+kw)]) dw.

Splitting the q interval into k unit intervals gives zero unless k divides l. This uses both the periodicity of chi and the INTEGER degree of H_N. If l=kr, the exact formula is

 I_(kr)(b)=exp(-2 pi i r b) integral_0^1 chi(q) exp(2 pi i[kr H_N(q)+r q])dq.

Changing the starting q interval does not change the integral because the displayed integrand is periodic. Thus many physical critical points can cancel exactly, but the resonant modes survive.

Suppose chi isolates a simple zero of V. For fixed nonzero r, the critical point solves V(q)=-1/(kN), not V(q)=0. Parameter-uniform stationary phase gives size (|r| k N)^(-1/2), with leading phase evaluated at that actual critical point and remainder O((|r|kN)^(-3/2)). Fourier compensation as in stationary-clock.md therefore realizes any fixed smooth mean-zero target J(b), at size 1/(kN), using physical clock modes l=kr and amplitude (kN)^(-1/2). The sign in the target Fourier index is reversed by exp(-2 pi i r b), and must be included when choosing the coefficients.

For every fixed derivative order d, the physical clock has bound C_(d,J) k^d/(kN)^(1/2). Taking k=floor(log N), with k>=1, makes this tend to zero for every fixed d. Positivity follows for large N. The mean-zero theta clock permits the same exact volume normalization as the one-pass construction. Thus the fixed-old-chart, next-parameter-to-infinity obstruction DOES NOT exclude this coupled ideal family.

The resonant output is a period perturbation. Its conversion to frequency spacing additionally uses the actual next orbit period kN; the relative period size 1/(kN) gives spacing-size relative jitter for angular indices of order kN. It does not itself prove that the required packets have that angular scale or that their spectral matrices approximate the previous ones.

## What changes after the previous clock

The actual first straightening is Q=(q+B_N(q,w))/P_N(w), where B_N is the incomplete clock integral and P_N=1+A_N. The next shear satisfies K'=M/[N P_N(w)] plus its degree correction, and Q=b+K(w). Consequently the physical q coordinate solves

 q+B_N(q,w)=P_N(w)[b+K(w)].

This equation is to be used on consistent local lifts; neither Q nor q may be treated as a globally bounded real coordinate while w traverses a degree-k orbit. Resetting the lifts introduces the corresponding integer q changes, which leave physical phases invariant but must be retained in derivative estimates.

In particular replacing this equation by q=b+kw inside H_N is NOT justified by a C0-small error alone: H_N has derivatives of order N and the resonant theta frequency is k. Uniform incomplete stationary phase suggests B_N=O(1/N) (for a fixed target clock), whereas the elementary supremum estimate gives only O(N^(-1/2)). Even the stronger bound is not a uniform estimate for all q,w derivatives: B_q is the clock itself, of size N^(-1/2), and higher q derivatives contain the rapidly varying phase. These derivatives enter both critical-point locations and the stationary amplitudes of the next orbit integral.

The exact ideal lemma therefore leaves three obligations:

1. Prove a summed stationary-phase expansion for the actual degree-k orbit, with all critical points, their relative phases, and uniform errors small compared with (kN)^(-1/2).
2. Prove that the next packet approximation and spectral root-sum cancellation permit k to grow slowly relative to N, rather than requiring k above a pre-existing power of N.
3. Maintain an appropriate physical phase description through arbitrarily many passages, including the strong matrix-density and color-prediction requirements. A two-step local clock does not supply this induction.

No completion or contribution verdict is attached to these supporting calculations.

## Actual two-step estimate on a second, untouched critical arc

There is a useful way to avoid differentiating the incomplete first clock. Assume V has a second simple zero and choose the NEXT clock cutoff chi_2 in a small arc around that zero, disjoint from the first clock support. On this arc B_N(q,w)=D_N(w), where D_N is either zero or the complete first-clock integral A_N (after choosing a consistent q origin). Thus every fixed w derivative of D_N and A_N is O(1/N). The physical first clock vanishes identically on this arc.

Set d_N=integral_0^1 P_N(w)^(-1)dw and choose the next continuous passage parameter M=kN/d_N. There is no integrality requirement on this continuous time parameter. Define K'=k/(d_N P_N), K(0)=0. Then K(w+1)=K(w)+k exactly and K(w)=kw+O_C^s(k/N) on [0,1], for each fixed s. The next periodic orbit is Q=b+K(w), with its invariant parameter b taken modulo 1.

On the selected physical q arc the j-th crossing solves

 b+K(w_j)=(q+D_N(w_j))/P_N(w_j)+j,

where j is the integer Q lift. The right derivative correction in w is O(1/N), because q is now restricted to a fixed bounded lift of the physical arc. Uniformly over all crossings, implicit inversion gives

 w_j=(q+j-b)/k+O(1/N),
 dw_j/dq=k^(-1)[1+O(1/N)].

The same estimates hold after each fixed number of b derivatives with constants depending on the fixed earlier jitter, not on k,N. Individual sheet endpoints at w=0 are dealt with by periodic relabeling; the physical integrand and K have their exact integer degrees. There are k crossings of every q in the arc.

For a fixed resonant mode l=kr, sum the q integrals over those k sheets. Comparing each phase kr w_j with r(q+j-b) costs O_r(k/N); comparing the summed Jacobian with 1 costs O(1/N). Since exp(2 pi i r j)=1, the resulting actual orbit average satisfies

 I_(kr)^actual(b)=e^(-2 pi i r b) integral chi_2(q) exp(2 pi i[kr H_N(q)+r q])dq + O_r(k/N).

For any fixed number of b derivatives the same conclusion holds, with constants polynomial in |r| of an order depending on the derivative count; the smooth target Fourier coefficients absorb these factors. This is a direct absolute-integral comparison, not a stationary-phase assertion for the perturbed phase. It avoids large derivatives of that phase.

Consequently k^3/N -> 0 makes the error o((kN)^(-1/2)), the principal stationary size. After the compensating physical clock amplitude (kN)^(-1/2), the error is o(1/(kN)), exactly the required period-jitter scale. Taking k=floor(log N) meets both this requirement and all fixed physical derivative bounds. The clock's theta mean remains zero, so its own volume normalization is exact.

Limits: this estimate evaluates the period of a clock on the specified actual second orbit. It is not a proof that the second shear itself is physically close in every required derivative after all coordinate normalizations, nor that its packet spectral densities have the required approximation. It also does not produce a second unused physical critical arc at every subsequent stage. The two original zeros suffice for this two-step calculation; reusing them indefinitely requires a new accumulated-coordinate analysis.
