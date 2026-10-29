# Exact reductions and a failed local shortcut

These are research reductions, not a resolution or credit-bearing result.

## A common power reduces the full question to min(s_k)=1

Let f=prod(z-a_k)^(s_k), s_k rational >=1, |a_k|>=1, and lambda=min s_k.
Choose g=prod(z-a_k)^(s_k/lambda); all its exponents are >=1, at least one
is 1, and f is a constant-unit branch multiple of g^lambda. Moduli and
derivative moduli are branch-independent. If the desired inequality is known
for g, then

    ||f'|| = lambda || |g|^(lambda-1) |g'| ||
           <= lambda ||g||^(lambda-1) ||g'||
           <= (sum s_k)/2 ||g||^lambda = (sum s_k)/2 ||f||.

The factor exponent is nonnegative, including lambda=1. Boundary zeros are
handled by continuity since exponents are >=1. If g's inequality is strict
when any root is exterior, f's is strict too. The all-unimodular equality case
is already the source's Theorem 4. Thus the normalized-minimum case suffices
for the full nondegenerate claim. The reverse implication is just restriction.
In particular f=Q^lambda, lambda>=1, for an ordinary zero-free polynomial Q
is a routine classical corollary, and must not be nominated separately.

## Why controlling f'/f at a derivative maximizer is false

Take a=1+i/10, b=-3-i/10 and f(z)=(z-a)(z-b). Both roots are strictly outside
the unit circle: squared moduli 101/100 and 901/100. Since a+b=-2,
f'(z)=2z+2, with unique global boundary maximum 4 at z=1.
But f(1)=1/100-2i/5, and

    |f'(1)/f(1)|^2 = 160000/1601 > 1 = ((s_1+s_2)/2)^2.

Consequently, the source's boundary-root strategy of proving
|f'(z0)/f(z0)| <= (sum s)/2 at a maximizing z0 cannot be extended as stated
to exterior roots. This does NOT contradict the conjecture:
|f(-1)|^2=160801/10000>16=||f'||^2, so the actual norm inequality is strict.
All arithmetic is independently executable in checks/route_obstructions.py.
The first 300 random probes missed this local obstruction; those negative
numerical results never established the stronger claim.

## Algebraic derivative reduction, still no norm proof

For rational s_k>=1 choose m so m s_k are positive integers. The derivative
formula f'=f sum s_k/(z-a_k) implies (f')^m is an ordinary polynomial: each
root has remaining multiplicity m(s_k-1)>=0 after extracting the common
denominator, and the numerator is the mth power of a polynomial. If S=sum s,
its degree is m(S-1). Thus ordinary Bernstein supplies
|z f''/f'|<=S-1 at a point of maximal derivative modulus. This does not by
itself bound |f'/f|; the explicit quadratic above satisfies the Bernstein
condition while violating the proposed local conclusion. A global comparison
of ||f'|| and ||f|| remains missing.

## Classical source comparison (bounded)

Read Erdelyi's 1993 JCAM survey, Sections 9--11, from the author's public PDF.
Theorem 9.1 gives an unspecified absolute constant times degree for derivatives
of generalized nonnegative trigonometric polynomials. Theorem 11.4 concerns
the real interval with an absolute constant and restricted zero count. Neither
statement gives the exact complex-derivative circle bound S/2. This is a
scope/constant comparison, not an assertion that the entire generalized-
polynomial literature cannot subsume the conjecture.

The actual 2026 Bergman thesis introductory Theorem 8 (printed p12, PDF p24)
was visually read. It explicitly requires all a_k on the unit circle. The
download contains 34 introductory pages, not the appended journal article;
it does not close the published-body requirement. Both public Rubin thesis
files likewise contain only introductory portions (100/102 PDF pages).
