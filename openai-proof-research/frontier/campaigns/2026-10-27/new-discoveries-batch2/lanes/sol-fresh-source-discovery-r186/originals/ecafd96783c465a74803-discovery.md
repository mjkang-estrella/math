# Unresolved: shifted Jacobi denominator law

Research performed 2026-10-28, solo, with no children. Discovery credit: **0**.
There is no complete proof of Remark 3.8 and no `PROOF.md` or Lean certificate.
This report gives a new attempted route and its exact unresolved obligation.
The ordinary argument below proves the source's computational top-coefficient
formula for the literal formal object; that partial result is not submitted as
a separate discovery or as a resolution of the denominator question.

## Scope and live sources

The primary is Iván Area, [arXiv:2608.23006v2](https://arxiv.org/html/2608.23006v2),
Definition 2.1, equations (6)–(7), Computational observation 3.1, Theorem 1.4,
Corollary 3.7, Remark 3.8. The live abstract page identifies v2 as 2026-10-05.
The target is the denominator of the polynomial in
`u = alpha^2 - 1/4`, `v = beta^2 - 1/4`, for every integer `r >= 1`.
The conjectured answer is

    delta_r = 2r + v2((r-1)!).

The companion [arXiv:2609.29531v2](https://arxiv.org/html/2609.29531v2)
is current v2, 2026-10-14. Its actual Theorems 1.5 and 7.36 give the exact
valuation of `[A^1 B^0] kappa_r` in ORIGINAL variables, with exponent
`3r-1+v2((r-1)!)`. Its Section 11 retains the larger shifted upper bound.
That original-variable result is already public and is excluded from novelty.
Primary Introduction (a), companion introduction and Proposition 7.37 make the
analytic phase identification beyond the checked range conditional. None is
assumed here: everything below starts with literal equation (6).

Actual downloaded source bodies and hashes are in `source/` and `provenance.json`.
The root adoption correction and its actual `check.py`/`checks.json` were read.
The earlier even-reality argument, false equivalence, unproved degree claims,
and broken decomposition routine are not adopted.

## Re-derivation of the integer starting algebra

Put `P_l(w)=prod_{0<=j<l}(w-j(j+1))`, `p=1+i`, `q=1-i`.
The source's Hankel coefficient is exactly `P_l(u)/(2^l l!)`; consequently
its inverse-factorial coefficient is

    C_s(x,y) = sum_{l=0}^s P_l(u) P_(s-l)(v) x^l y^(s-l)/(l!(s-l)!).

At the midpoint `x=p/2`, `y=q/2`, this is `Ctilde_s/(2^s s!)`, with

    Ctilde_s = sum_l binom(s,l) P_l(u) P_(s-l)(v) p^l q^(s-l).

Expanding `e_s(Z)=prod_{j=1}^s(Z-j)^(-1)` uses
`[Z^(-n)]e_s=S2(n,s)` for `n>=s`. The identity follows, for example,
by the common generating function `prod_{j=1}^s(1-j z)^(-1)` for the
complete homogeneous functions and the second-kind Stirling numbers.
Thus `A_n=2^n n![Z^(-n)]F` and `B_n=2^n n![Z^(-n)]log F` satisfy exactly

    A_n = sum_{s<=n} S2(n,s) 2^(n-s) (n!/s!) Ctilde_s,
    B_n = A_n - sum_{j=1}^{n-1} binom(n-1,j-1) B_j A_(n-j),
    kappa_r = Im B_(2r-1)/(2^(4r-2) (2r-1)!).

The cumulant identity follows by differentiating the exponential generating
series with coefficients `A_n`; it is not a numerical identification.
Legendre's factorial formula reduces the target to content
`min v2(coeff Im B_(2m+1))=3m`.

## A formal differential equation directly from Definition 2.1

Use an indeterminate `t`, not an analytic angle, and set

    x=(1+i t)/2, y=(1-i/t)/2,
    D=-(1+t^2) d/dt,
    V=u(1+t^2)+v(1+t^(-2)).

Then `2xy=x+y` and, on every polynomial in `x,y`, `D=2i delta`, where

    delta=x(x-1) partial_x + y(y-1) partial_y,
    Q=x^2 partial_x + y^2 partial_y,
    Theta_x=x partial_x, Theta_y=y partial_y.

Here are explicit all-order algebraic details, so that the crucial bridge
does not rest on phase identification or finite evidence.

The product defining `P_l` gives, coefficient by coefficient,

    partial_x C_(s+1) = (u-Theta_x(Theta_x+1)) C_s,
    partial_y C_(s+1) = (v-Theta_y(Theta_y+1)) C_s.

A direct operator calculation gives

    delta Q = x(x-1)Theta_x(Theta_x+1)
            + y(y-1)Theta_y(Theta_y+1)
            + xy(2xy-x-y) partial_x partial_y.

The last term vanishes on our curve. Combining these identities yields

    delta(C_(s+1)+Q C_s) = [u x(x-1)+v y(y-1)] C_s = -V C_s/4.

Since `C_s` is homogeneous of degree `s` in `x,y`, and `Q=delta+Theta_x+Theta_y`,
we have `D^2 C_s+2i s D C_s=-4 delta Q C_s`. Therefore, for every `s>=0`,

    D^2 C_s + 2i s D C_s + 2i D C_(s+1) - V C_s = 0.       (R1)

Finally `Z e_s=e_(s-1)+s e_s` for `s>=1`. Summing (R1), coefficientwise in
`Z^(-1)`, proves the exact formal equation

    D^2 F + 2i Z D F - V F = 0.                             (R2)

All sums are legitimate: each coefficient of `Z^(-1)` uses finitely many `s`.
No analytic solution, convergence, boundary selection, or phase expansion is used.

## Riccati recurrence, degree, and the top coefficient

Define integral Laurent polynomials by

    s_1=V,
    s_(n+1)=-D s_n - sum_{a+b=n, a,b>=1} s_a s_b.           (R3)

Dividing (R2) by `F` proves

    D log F = sum_{n>=1} s_n/(2iZ)^n.                      (R4)

This solution is unique by coefficient recursion. Induction in (R3) proves:

* `s_n` has integer coefficients, is divisible by `1+t^2` in the Laurent ring,
  and has parameter degree at most `ceil(n/2)`.
* `s_n(-t)=(-1)^(n+1)s_n(t)`.

For the divisibility assertion, `D((1+t^2)h)` is again divisible by `1+t^2`,
and products preserve it. Degree follows by checking the derivative and product
terms separately, including the odd/even index cases.

Each `L_n` from the source is a Laurent polynomial after the substitution for
`x,y`. Its imaginary part is odd under `t -> -t`, since that substitution
conjugates `x,y` and the coefficients before substitution are rational.
For even `n`, (R4) has real right side, so `D Im L_n=0`.
The kernel of `D` on Laurent polynomials in characteristic zero consists of
constants. An odd constant is zero. Thus **even-index imaginary parts vanish
for this actual series**, by (R2), not by swap symmetry.

For odd `n=2r-1`, let `J_t(s_n)` be the unique odd Laurent polynomial with
`D J_t(s_n)=s_n`. It exists because `s_n/(1+t^2)` is an even integral Laurent
polynomial; its monomials integrate with nonzero odd denominators. Write
`J(s_n)=J_t(s_n)|_(t=1)`. Equation (R4) and oddness give

    Im L_(2r-1)(t) = (-1)^r J_t(s_(2r-1))/2^(2r-1),
    kappa_r = (-1)^r J(s_(2r-1))/2^(4r-2).                 (R5)

This removes the possible imaginary integration constant rigorously. Also,
`x(i)=y(i)=0`, so `L_n(i)=0`. Any parameter coefficient of `L_n` beyond degree
`ceil(n/2)` has derivative zero by (R4), hence is constant in `t` and vanishes
at `i`. This proves that same degree bound for `L_n` itself.

Let `c_k=binom(2k,k)/(k+1)` be the Catalan numbers. The homogeneous parameter
degree `r` part of `s_(2r-1)` is

    (-1)^(r-1) c_(r-1) V^r.                               (R6)

Indeed the derivative in (R3) cannot contribute to that degree, nor can an
even/even product. The odd/odd products give precisely the Catalan recursion,
starting with `s_1=V`. This is a proof for all `r`.

The `u^r` coefficient in `V^r` is `(1+t^2)^r`. Its `D`-primitive is

    -sum_{j=0}^{r-1} binom(r-1,j) t^(2j+1)/(2j+1).

Combining (R5) and (R6) therefore proves, unconditionally for the formal definition,

    [u^r]kappa_r = c_(r-1) I_r/2^(4r-2)
                = 2 binom(2r,r) I_r / ((2r-1)16^r),
    I_r=sum_{j=0}^{r-1} binom(r-1,j)/(2j+1).               (R7)

This is exactly the primary source's equation (14), now derived at all orders.
The coefficient of `v^r` is its negative by the valid source antisymmetry.
In particular the degree of `kappa_r` is exactly `r` (the displayed rational
coefficient is positive and nonzero). Using the source's proved Theorem 1.4,
the valuation of (R7) is `-2r-v2((r-1)!)`. Thus the proposed denominator exponent
is attained by the pure top coefficient at every order. This proves the lower
bound, not the missing upper bound for all coefficients.

## The unresolved obligation: no full result

Let `Z_(2)` denote rational numbers with odd denominator. In the new notation the
remaining assertion is precisely

    for every r>=1,
    (r-1)! J(s_(2r-1)) belongs to 2^(2r-2) Z_(2)[u,v].     (GAP)

Equation (R5) shows that (GAP), together with (R7), would prove the full law.
It is NOT proved here. In terms of valuations it is
`min v2(coeff J(s_(2r-1))) >= r-1+s2(r-1)`.

A stronger degree-specific version surviving the bounded checks is

    (d-1)! [homogeneous degree d] J(s_(2r-1))
       belongs to 2^(2r-2) Z_(2)[u,v]   (1<=d<=r).         (GUESS)

This is a conjectural research lead only. No all-order induction for it was
obtained; the factorials and the midpoint cancellations are essential, not
provided by the recurrence's integrality or symmetry.

**Strongest objection:** (R2)–(R7) close auxiliary gaps but do not control the
2-adic size of the lower homogeneous pieces. Replacing a cumulant by a Riccati
recurrence alone merely relocates the principal cancellation. Claiming a full
solution from this report would be false. No finite checks, top attainment,
degree bound, or parity statement supplies (GAP).

## Exact falsifiers and bounded checks

`python3 check.py` runs an independent sparse integer Laurent recurrence and an
independent SymPy source/cumulant pipeline. It checks the source-vs-Riccati
identity through `n=9`, the inverse-factorial ODE through `s=4`, the generic
operator identity symbolically in its exponents, and the new recurrence/top
formula plus (GUESS) through `r=8`. These ranges test the new bridges; they are
not an extension of earlier large content sweeps and are not all-order evidence.

Two explicit falsifiers block simple attempted proofs of (GAP):

1. `s_3=D^2 V - V^2`. The pure `u^2` coefficient of its odd primitive is
   `t+t^3/3`. Neither Laurent coefficient is divisible by 4 in `Z_(2)`;
   their midpoint sum is `4/3`. Thus coefficientwise divisibility before
   midpoint evaluation, or a termwise midpoint valuation argument, fails
   already at `r=2`.
2. Extending the primary binomial-sum valuation to arbitrary odd denominator
   shifts is false. For example
   `sum_{j=0}^3 binom(3,j)/(2j+3)=464/315` has valuation 4,
   smaller than `3+v2(4)=5`. Consequently an indiscriminate shifted-moment
   generalization cannot handle all derivative terms.

`checks.json` is the actual successful output of this exact program, not a
handwritten all-true summary. A 500 MiB address-space limit is set before the
experiment. The reported high-water RSS is below 512 MiB. No large symbolic
sweep, Lean build, or helper formalization was undertaken.

## Bounded novelty and chronology

The live screen is detailed in `source/registry-screen.md`. It includes current
GitHub heads, immutable untruncated relevant subtrees, current catalogue bodies,
the actual primary/companion bodies, MathDB's actual rendered statement, and web
queries. No matching public shifted-law proof was located in that bounded scope.
This is not a global novelty certificate or a completed acceptance gate.

MathDB 391922 concerns the ORIGINAL-variable law already proved in the companion;
its empty solution list and stale open/progress prose do not imply novelty.
The source/companion publications predate this 2026-10-28 work. There is no claim
that the Riccati machinery, its classical WKB interpretation, or this partial
top-coefficient deduction deserves separate discovery credit or worldwide priority.

No source bytes, registries, shared ledgers, counts, other lanes, accounts, browser
tabs, external messages, or public posts were mutated. No GLM Karp/BBK lane files
were inspected. All writes are in this assigned lane.
