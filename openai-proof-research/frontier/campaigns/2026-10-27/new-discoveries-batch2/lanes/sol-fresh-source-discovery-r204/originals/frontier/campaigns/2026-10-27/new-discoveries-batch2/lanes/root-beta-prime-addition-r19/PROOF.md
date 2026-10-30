# Candidate proof of Ferreira–Simon Conjecture 1

Date: 28 October 2026. **Ordinary proof candidate only; credit 0.** No full
Lean certificate, independent review, manuscript or acceptance is claimed.
A concrete classical product-formula bridge was subsequently found; see
CLASSICAL-REDUCTION.md. Root recommends routine-corollary EXCLUSION (credit 0),
pending independent adjudication of the exact Durand display and hypotheses.

The primary statement is Conjecture 1 of Ferreira–Simon,
arXiv:2108.09244v2, §4 (printed pp.20–21). For all a>0 and 0<b<1/2,

    Bprime(a,b) + Bprime(a,b)
      =d Bprime(2a,b) (1 + sqrt(Beta(a,1/2)/Beta(b,1/2-b))).       (1)

Variables on a side are independent. The source's Theorem B already proves
a=1/2 and a=1-b, and Theorem A proves the b=1/2 limit. Those cases and all
classical beta–gamma algebra are uncredited. The first campaign's Mills-ratio
refutation is a different conjecture in this paper and is not counted again.

## 1. A conditional inverse-Gamma identity

Write G_p for a rate-one Gamma variable of shape p. We prove, for 0<u<1,
0<b<1/2, and independent variables on either side,

    u/G_b + (1-u)/G_b
      =d (1 + 2 sqrt(u(1-u))/sqrt(W))/G_b,
    W ~ Beta(b,1/2-b).                                         (2)

Set c=2sqrt(u(1-u)) in (0,1]. Take reciprocals. By beta–gamma algebra, the
left reciprocal has the law

    Q = G_(2b) V(1-V)/(u+(1-2u)V),   V~Beta(b,b).

The right reciprocal is

    R = G_b sqrt(W)/(sqrt(W)+c).

For every integer m>=1 we will show E Q^m = E R^m. Both variables have a
moment generating function in a neighborhood of zero: Q<=G_(2b)/(1+c)
(minimize u/t+(1-u)/(1-t)), and R<=G_b/(1+c). Equality of all moments then
implies equality in law by uniqueness of a local moment generating function.

## 2. The left reciprocal moments

Put d=1-2u, so d^2=1-c^2. With r=2V-1, the beta density is proportional to
(1-r^2)^(b-1) on (-1,1), and

    V(1-V)/(u+(1-2u)V) = (1-r^2)/(2(1+d r)).

Expand (1+d r)^(-m) for |d|<1. Absolute uniform convergence justifies
termwise integration; odd terms vanish. The even beta moments give

    E Q^m = A_m sum_(k>=0)
        (m/2)_k ((m+1)/2)_k / ((b+m+1/2)_k k!) (1-c^2)^k,       (3)

where

    A_m = (2b)_m (b)_m / (2^m (b+1/2)_m).

Indeed the k-th even integral divided by the k=0 integral is
(1/2)_k/(b+m+1/2)_k; use (m)_(2k)=4^k(m/2)_k((m+1)/2)_k and
(2k)!=4^k k!(1/2)_k. This also handles d=0 directly.

## 3. The right reciprocal moments: an exact integration-by-parts equation

For real c>0 define

    I_m(c) = integral_0^1
       t^(2b+m-1) (1-t^2)^(-b-1/2) (t+c)^(-m) dt.

Then E R^m = 2(b)_m I_m(c)/B(b,1/2-b). The integral is finite and real
analytic on c>0. More explicitly it is holomorphic for Re c>0, using the
principal power of t+c and locally uniform integrable bounds at t=0,1.
Differentiation under the integral is justified by the same bounds.

Set g(t,c) equal to the integrand above and

    H(t,c)=t^(2b+m)(1-t^2)^(1/2-b)(t+c)^(-m-1).

Both endpoint values of H are zero because 2b+m>0 and 1/2-b>0. Direct
differentiation gives the pointwise identity

    c(1-c^2) g_cc + [1-2b-2(m+1)c^2] g_c - m(m+1)c g
        = m H_t.                                              (4)

All terms are integrable; integrate first on [epsilon,1-epsilon] and pass
to the endpoints. Consequently

    c(1-c^2) I_m'' + [1-2b-2(m+1)c^2] I_m' - m(m+1)c I_m = 0.   (5)

At c=1, substitute r=(1-t)/(1+t). Every (1+r) power cancels, yielding

    I_m(1)=2^(-2b-m) B(1/2-b,2b+m).                            (6)

The Gamma duplication identity therefore gives

    2(b)_m I_m(1)/B(b,1/2-b)=A_m.                              (7)

Put z=1-c^2. Equation (5) becomes the Gauss equation

    z(1-z) Y'' + [C-(m+3/2)z]Y' - m(m+1)Y/4 = 0,
    C=b+m+1/2>0.                                              (8)

The analytic solution at z=0 is uniquely determined by its value there:
substitution of a Taylor series gives

    y_(k+1) = (k+m/2)(k+(m+1)/2) y_k / ((k+1)(k+C)).            (9)

Thus (7)–(9) reproduce exactly (3), first near c=1. Both sides are real
analytic for 0<c<1 (the series in (3) converges for |1-c^2|<1), so the
identity theorem extends equality throughout 0<c<=1. There is no appeal to
a nonanalytic uniqueness assertion at a singular endpoint. The zeroth
moments are 1. This proves (2).

## 4. The literal beta-prime identity

Let A1,A2~Gamma(a), H1,H2~Gamma(b) be independent. Put
G=A1+A2 and U=A1/G. Then G~Gamma(2a), U~Beta(a,a), independent, and

    A1/H1+A2/H2=G [U/H1+(1-U)/H2].

Apply (2) conditionally on U. Its right-hand representation can use fresh
G_b,W independent of U and G. Finally 4U(1-U)~Beta(a,1/2), as follows by
the two-branch change of variables from the symmetric Beta(a,a) density.
Hence the last display has the law

    (G/G_b) [1+sqrt(Beta(a,1/2)/W)],

with the ratio G/G_b independent of the two beta variables. This is (1)
for every a>0 and 0<b<1/2, with the source's independence convention.

## Status, strongest objections and falsifiers

The proof uses standard beta–gamma algebra, binomial series, one exact
integration-by-parts differential equation, analytic uniqueness and moment
determinacy. None is a new general tool. It may be a reformulation of a
classical same-order Macdonald/Bessel product formula, which would create a
routine-corollary exclusion. Searches have not yet settled that point; absence
of a search hit is not novelty evidence. The local ODE identity (4), the
normalization (6), the independence in §4 and a published same-object product
formula are the highest-value adversarial checks.

No full Lean endpoint exists. Numerics validate transcriptions only and are
not used as proof. No worldwide priority, optimality, new machinery, acceptance
or separate credit for the conditional identity is asserted. The conditional
identity and the full source result would be ONE family if it survives gates.
