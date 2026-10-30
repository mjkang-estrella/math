# Zhou coefficient cancellation: proof and decisive subsumption

**Disposition: uncredited. This is a routine corollary of a theorem already
present in Xu–Zhao (January 2024), not a candidate for one of the thirty new
outcomes.** The independent ODE proof below does not change that disposition.

## 1. Exact target and source range

Primary target: Jianing Zhou, *Mixed Berndt-Type Integrals and Generalized Barnes
Multiple Zeta Functions*, arXiv:2502.15173v4 (3 February 2026), Conjecture 5.8.
The live abstract identifies this as the latest revision and gives the published
reference *Advances in Applied Mathematics* 174 (2026), 103027.

Theorems 5.1 and 5.4, equations (5.61), (5.62), (5.88), (5.89), define rational
coefficients through four integrals. Put G=Gamma(1/4), D(x)=sinh²x+sin²x, and

* C_m = integral x^(4m)(sinh x−sin x)/(D(x)(cosh x+cos x)) dx;
* E_m = integral x^(4m)(sinh x+sin x)/(D(x)(cosh x−cos x)) dx;
* D_m = integral x^(4m−2)(sinh x+sin x)/(D(x)(cosh x+cos x)) dx;
* F_m = integral x^(4m−2)(sinh x−sin x)/(D(x)(cosh x−cos x)) dx.

All integrals run over (0,infinity). The source states

    C_m = c1,m G^(8m)/pi^(2m) + c2,m G^(8m+4)/pi^(2m+2),
    E_m = e1,m G^(8m)/pi^(2m) + e2,m G^(8m+4)/pi^(2m+2),
    D_m = d1,m G^(8m−4)/pi^(2m−1) + d2,m G^(8m)/pi^(2m+1),
    F_m = f1,m G^(8m−4)/pi^(2m−1) + f2,m G^(8m)/pi^(2m+1).

The first three formulas have m>=1; **the fourth has m>=2**. Conjecture 5.8
asks c2,m+e2,m=0 and d1,m+f1,m=0, printed with m>=1. Its substantive common
range is the first identity for m>=1 and the second for m>=2.

At m=1, source Remark 5.5 gives F_1=G^4/(64pi)−pi/8 instead of the fourth
two-monomial formula. D_1=G^8/(512pi³)−G^4/(64pi), so the G^4 coefficients
still cancel if that separately supplied representation is used. This endpoint
observation is neither a counterexample nor a discovery.

## 2. The already published structural theorem

Closest source actually read in full at the relevant theorem and proof:
Ce Xu and Jianqiang Zhao, *General Berndt-Type Integrals and Series Associated
with Jacobi Elliptic Functions*, arXiv:2401.01385v2 (18 January 2024),
**Lemma 4.4**, including its proof via equation (4.17) and Lemma 4.3.

Use the source convention

    t=k² in (0,1), y=pi K(1−t)/K(t), z=2K(t)/pi,
    sigma=t(1−t), sigma'=1−2t,
    A_j(y)=sum_(n>=1) (−1)^(n−1) n^j/sinh(ny).

Lemma 4.4 states, for every integer s>=1, that there are rational polynomials
P_s and Q_s such that

    A_(4s−1)(y(t)) = z(t)^(4s) P_s(sigma),                 (1)
    A_(4s+1)(y(t)) = z(t)^(4s+2) Q_s(sigma) sigma'.        (2)

These are identities on the whole interval, not merely special-value statements.
The proof explicitly establishes symmetry/antisymmetry of the coefficient
polynomial. Thus it supplies precisely the parity feature rediscovered by the
ODE argument in section 5 below.

The standard identities used by both sources are

    dt/dy = −t(1−t) z²,
    y(1/2)=pi,
    z(1/2)=G²/(2pi^(3/2)),
    z'(1/2)=4sqrt(pi)/G².                                 (3)

These also appear explicitly in Zhou's equations preceding (5.82). No OpenAI
upstream theorem is needed by this reduction.

## 3. Elementary bridge and proof of both cancellations

Let

    T_j = Cbar_(j,2)(pi/2)+Sbar_(j,2)(pi/2),

using Zhou's Definition 2.1: both sums have the factor (−1)^(n−1); the
denominators are respectively cosh²(ny) and sinh²(ny).

For u>0 the elementary identity

    1/sinh²u + 1/cosh²u = 4 cosh(2u)/sinh²(2u)            (4)

gives

    T_j = −4 A_(j−1)'(pi).                               (5)

Termwise differentiation is justified uniformly on every compact subinterval
of y>0: the summands and their derivatives are bounded by a constant times
n^(j+1) exp(−epsilon n). This is an ordinary absolutely convergent series, with
no regularization or limiting interchange at y=0.

For j=4m, use (1) with s=m. Equations (3) and (5), and sigma'(1/2)=0, imply

    T_(4m) = 4m z(1/2)^(4m+1) z'(1/2) P_m(1/4)
           in Q G^(8m)/pi^(6m+1).                        (6)

For j=4m−2 and m>=2, use (2) with s=m−1. Differentiating with respect to t
at t=1/2 kills the terms containing sigma', while (sigma')'=−2. Hence

    T_(4m−2) = −2 z(1/2)^(4m) Q_(m−1)(1/4)
             in Q G^(8m)/pi^(6m).                        (7)

Zhou's exact source conversions (5.83), (5.84), (5.108), (5.109) are

    C_m+E_m = (−1)^(m−1) pi^(4m+1)/(2*4^m) T_(4m),     (8)
    D_m+F_m = (−1)^(m−1) pi^(4m−1)/4^m T_(4m−2).       (9)

Thus

    C_m+E_m in Q G^(8m)/pi^(2m),
    D_m+F_m in Q G^(8m)/pi^(2m+1).                        (10)

Comparing the source's rational coefficient expressions proves the asserted
cancellations. To interpret the coefficients as *any* rational representation,
rather than the canonical coefficient formulas in the source proofs, use the
classical algebraic independence of pi and Gamma(1/4): in particular
G^4/pi² is irrational. A retrieved author-hosted account is Michel Waldschmidt,
*Transcendence of periods: the state of the art*, Corollary 33, printed page 19
(sources/waldschmidt2005.pdf); its preceding Theorem 29 credits Chudnovsky.
The actual Corollary 33 statement was read, rather than inferred from a search
snippet. Therefore the two monomials in each source expression
are linearly independent over Q. The canonical formulas can instead be compared
formally, as in section 5, without this transcendence theorem.

This is a two-step specialization of Lemma 4.4: apply (4), then differentiate
once at the symmetric modulus. Under the campaign's explicit ban on immediate
or routine corollaries, it cannot receive discovery credit even if no previous
author explicitly wrote the final equations c2,m+e2,m=0 and d1,m+f1,m=0.

## 4. Still shorter argument for the first identity

Algebra directly gives

    (sinh x−sin x)/(D(x)(cosh x+cos x))
    +(sinh x+sin x)/(D(x)(cosh x−cos x)) = −(1/D(x))'.

Consequently integration by parts and D(x)=(cosh(2x)−cos(2x))/2 give

    C_m+E_m = 4m integral x^(4m−1)/D(x) dx
            = (8m/2^(4m)) I_−(4m,1).

The boundary terms vanish for m>=1, since D(x)~2x² at zero and grows
exponentially at infinity. Zhou's own introduction (1.5), credited to older
Berndt/Xu–Zhao results, already places I_−(4m,1) in Q G^(8m)/pi^(2m).
This alone rules out separate credit for the c/e half.

## 5. Independent all-order ODE derivation, preserved uncredited

This calculation was made before the exact Lemma 4.4 subsumption was found.
It confirms the source correspondence and does not assert novelty.

Let q_(2p−1)(a) be the source sn polynomial, so

    sn(v,a)=sum_(n>=0) (−1)^n q_(2n+1)(a) v^(2n+1)/(2n+1)!.

Let Q_(2p−2)(a) be the source sn² polynomial, with coefficient
(−1)^(p−2) Q_(2p−2)(a)/(2p−2)!. For 0<t<1 set r=sqrt(t), a=(1+r),
b=(1−r), h=(b/a)², and

    H_p(t)=a^(2p)[sqrt(h) q_(2p−1)(h)−h Q_(2p−2)(h)].    (11)

For p>=2 define w(v)=b sn(av,h) and U(v)=w'(v)+w(v)². Its coefficient of
v^(2p−2)/(2p−2)! is (−1)^(p−1) H_p(t), directly by the two source Taylor
definitions. The Jacobi differential identities give

    (w')²=(1−t)²−2(1+t)w²+w⁴,
    w''=−2(1+t)w+2w³,
    U''=3U²−2(1+t)U−(1−t)²,
    U(0)=1−t, U'(0)=0.                                  (12)

Each identity follows by expansion; the checker verifies the elimination of
(w')² exactly. Writing V=U−(1+t)/3 gives

    V''=3V²−(4/3)(1−t+t²),
    V(0)=(2−4t)/3, V'(0)=0.                              (13)

All Taylor coefficients are rational polynomials in t, inductively from (13).
The function −V(iv,t) solves (13) with parameter 1−t and the same initial
conditions. Uniqueness of the formal power-series solution (or analytic ODE
uniqueness) therefore gives V(v,1−t)=−V(iv,t). Comparing degree 2p−2 yields

    H_p(1−t)=(−1)^p H_p(t), p>=2.                        (14)

In particular H_p(1/2)=0 for odd p, and H_p'(1/2)=0 for even p.

Here is the exact source bridge, including its constants. Combine Zhou
Theorems 4.1 and 4.3, then apply his substitution (5.60)

    x=4sqrt(t)/(1+sqrt(t))², z(x)=(1+sqrt(t)) Z(t).

The combined source polynomial before substitution is

    sqrt(1−x) q_(2p−1)(1−x)−(1−x)Q_(2p−2)(1−x).

Since x(1−x)z(x)²/(dx/dt)=2t(1−t)Z(t)², the combined series equals

    (−1)^p * [2t(1−t)Z²/2^(2p)] * d/dt [Z^(2p) H_p(t)].

At t=1/2 this is

    T_(2p) = (−1)^p [
       p*2^(1−4p) H_p(1/2) G^(4p)/pi^(3p+1)
       +2^(−4p−3) H_p'(1/2) G^(4p+4)/pi^(3p+3) ].       (15)

For p=2m and p=2m−1 respectively, (14) kills exactly the monomial required in
(8) and (9). Equation (15) compares *canonical* coefficients directly, so this
version of the proof does not use algebraic independence of special values.

The exact checker constructs q and Q from the cubic Jacobi ODE independently
of the quadratic U ODE. It verifies (11), (14), the midpoint cancellations,
and the lowest source examples for p=2,...,12. This is verification of the
algebra and indexing, not a substitute for the uniform argument (12)–(14).

## 6. Formal and novelty limits

No complete literal-source Lean certificate is claimed. The saved Lean module
only checks elementary identities supporting the exclusion, and is explicitly
an uncredited helper. There is no reason to invest in formalizing (12)–(15) for
discovery acceptance once the prior-theorem subsumption is established.

No proof of worldwide first priority is attempted. The exact source theorem
already suffices to reject this candidate under the stated counting standard.
See discovery/review.md and provenance.json for actual searches and failures.
