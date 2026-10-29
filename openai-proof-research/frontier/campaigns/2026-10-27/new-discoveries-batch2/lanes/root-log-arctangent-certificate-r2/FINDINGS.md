# A finite derivative certificate for the logarithm–arctangent candidate

Status: complete ordinary replacement for the candidate's coefficient/tail lemma,
not an independent final review, Lean certificate, source clearance or credit.
The candidate frozen at `88eb1b426c` is unchanged. Counts remain 3/30 additional,
33/60 total. Classical Abel summation and derivative monotonicity are uncredited.

## Definitions and the exact finite certificate

Put d = sqrt(17), and use the actual candidate's functions

    A(t) = (cosh(4t) - cosh(t)cosh(dt) + (5/d)sinh(t)sinh(dt))/2,
    B(t) = sinh(t)(cosh(5t)-cosh(dt))/2,
    U = B'A - BA' - A²,   V = -4BA,
    E(t) = (1+2t²)U(t)+tV(t).

Write U = sum u_lambda exp(lambda t), V = sum v_lambda exp(lambda t).
The coefficients and frequencies are exact elements of Q(d). In decreasing order,
the twelve positive frequencies are

    7+d, 2+2d, 10, 5+d, 2d, 8, 3+d, -2+2d,
    7-d, 2, -3+d, 5-d.

They are strictly positive and decreasing; squaring positive rationals verifies
4 < d < 21/5. The coefficients satisfy u_{-lambda}=u_lambda and
v_{-lambda}=-v_lambda. There can also be a constant in U; its contribution to E
has degree two and disappears after 24 derivatives.

For these twelve frequencies define the three ordered arrays

    c_i0 = lambda_i^22 (u_i lambda_i² + 24 v_i lambda_i + 1104 u_i),
    c_i1 = lambda_i^22 (v_i lambda_i + 94 u_i),
    c_i2 = 2 lambda_i^22 u_i.

**Finite certificate:** every one of the 36 prefix sums

    S_kj = sum_{i=1}^k c_ij  (1 <= k <= 12, 0 <= j <= 2)

is strictly positive. `checks.json` stores all 36 exact pairs (a,b), meaning
a+b*d. `verification.json` supplies an elementary rational proof of every sign:
41/10 < d < 21/5, and each expression is bounded below by
a+(41/10)b when b>=0, or by a+(21/5)b when b<0; every resulting rational is
strictly positive. There is no floating-point sign decision.

`verify.py` independently constructs A,B,U,V as Laurent polynomials in
X=exp(t), Y=exp(dt), with coefficients in Q(d). Derivation acts on X^i Y^j
by multiplication by i+jd. It checks that the resulting U,V equal the frozen
exponential table exactly. Thus the prefix certificate is attached to the
actual functions, not to an unrelated coefficient list.

## Finite Abel lemma

If c_1,...,c_m have positive prefix sums S_k and
w_1 >= ... >= w_m > 0, then

    sum c_i w_i = S_m w_m + sum_{k=1}^{m-1} S_k(w_k-w_{k+1}) > 0.

If the weights are only nonnegative, the same identity gives nonnegativity.
This is a finite algebraic identity; it imposes no sign on individual c_i.

## Positivity of the 24th derivative, with no infinite series

Direct differentiation gives

    E^(24)(t)/2 = sum_i [
        c_i0 cosh(lambda_i t)
      + t (c_i1+c_i2) lambda_i sinh(lambda_i t)
      + t² c_i2 lambda_i² cosh(lambda_i t) ].

`verify.py` also checks this identity by differentiating the complete
polynomial-exponential expression 24 times, comparing all coefficients exactly.
In particular the linear-in-t factor has 96u_i, not 94u_i; the extra c_i2
accounts for this difference.

For t>=0, each of the three weight functions of lambda>0,

    cosh(lambda t), lambda sinh(lambda t), lambda² cosh(lambda t),

is nonnegative and increasing in lambda. The first is strictly positive.
The prefix sums of c_i0, c_i1+c_i2, and c_i2 are strictly positive by the
certificate. Applying the finite Abel lemma to each sum proves

    E^(24)(t) > 0  for every t>=0.

The exact derivatives of E at zero through order 23 are zero except

| n | E^(n)(0) |
|---|---:|
| 10 | 37847040 |
| 12 | 19891322880 |
| 14 | 5550283554816 |
| 16 | 1162696473968640 |
| 18 | 206947471161556992 |
| 20 | 33226670114812723200 |
| 22 | 4978839848478924865536 |

These are recomputed from the independently generated exponential polynomial.
All initial derivatives are nonnegative. Repeatedly applying the fundamental
theorem of calculus, starting with the positive 24th derivative, gives
E^(j)(t)>0 for t>0 and j=23,22,...,0. In particular **E(t)>0 for all t>0**.

This replaces both the original 145 positive coefficient checks and its
large-order tail estimate. It needs no power-series convergence theorem.

## Alternative all-order coefficient deduction

For even n=24+h (h>=0), the exact exponential formula gives

    E^(n)(0)/2 = sum_i lambda_i^h (c_i0+h*c_i1+h²*c_i2).

Every prefix sum of the parenthesized array is positive. Abel summation with
weights lambda_i^h therefore proves all these derivatives strictly positive.
This independently verifies the same all-order coefficient conclusion. Odd
derivatives vanish by parity. This alternative is unnecessary for the shorter
derivative-ladder proof above.

## Relation to the source and review boundary

The frozen candidate proves that E>0 implies a strictly increasing centered
logarithmic gap between the Stolarsky mean and M. Its exact stabilization and
strict monotonicity argument then prove both displayed branches of Conjecture
4.7. This note replaces only its E-positivity step. It does not adjudicate the
published-body HOLD, concrete classical subsumption, or the use of the stronger
term 'super-stabilizable'. The original source and original candidate remain
the subject of the running independent reviews.

## Reproduction and unsuccessful shortcuts

Run `python3 check.py`, then `python3 verify.py` in this directory. Both enforce
512 MiB address-space and 35-second CPU ceilings, use only the standard library,
and use exact fractions. `check.py` records failed coefficientwise prefix tests
at N=10,12,...,22; N=24 is the first successful even N in that search. These
failures do not disprove the candidate. No resource failures occurred here.

Remaining work: independent review of this replacement if adopted, literal
Lean implementation, and all campaign source/novelty/manuscript/packet gates.
