# Ordinary proof candidate: the full pendulum time-map conjecture

UTC 2026-10-30; local date 2026-10-29. Eligibility and literature priority are not certified.

Source: da Costa, Grinfeld, Pinto and Xayxanadasy, arXiv:1907.13009v1,
equation (14), section 4.4 Conjecture 1. For every fixed
0<phi<pi/2, the function z -> T_B(z,phi) is convex on (0,2).
The argument below proves strict convexity throughout this exact rectangle.
No restriction relative to the homoclinic parameter is imposed.

Put a=1-cos(2phi), so 0<a<2, and b(z)=acos(1-z)/2.
The source's actual function is

    T_B(z,phi) = integral_0^phi (z+a-1+cos(2x))^(-1/2) dx
              + integral_0^b(z) (z+a-1+cos(2x))^(-1/2) dx.

All integrands are real and positive: their denominator squared is at least
z in the first integral and at least a in the second. With t=1-cos(2x),
dx=dt/(2 sqrt(t(2-t))), this becomes

    T_B = (1/2)(integral_0^a + integral_0^z)
                 dt / sqrt(t(2-t)(a+z-t)).                    (1)

For n>=0 define finite positive moments

    M_n(a,z) = (integral_0^a + integral_0^z)
                      t^(n-1/2) (a+z-t)^(-1/2) dt.

The binomial series, with positive coefficients, gives the exact expansion

    T_B = 1/(2 sqrt(2)) sum_(n>=0) binom(2n,n)/8^n M_n(a,z). (2)

Indeed (2-t)^(-1/2)=2^(-1/2) sum binom(2n,n)t^n/8^n
for 0<=t<2. Both integration intervals in (1) have endpoints less than 2.
Monotone convergence justifies (2); finiteness also follows directly from
(1). No derivatives of the infinite series are needed.

We prove that each z -> M_n(a,z) is convex, keeping a>0 fixed.
For n=0 and n=1, the substitution t=(a+z)sin^2(theta), together
with arcsin sqrt(a/(a+z))+arcsin sqrt(z/(a+z))=pi/2, yields

    M_0(a,z)=pi,
    M_1(a,z)=pi(a+z)/2 - 2 sqrt(az).                         (3)

The first is constant. The second has second derivative
sqrt(a)/(2 z^(3/2))>0.

Now n>=2, and put p=n-1/2>1. The first summand

    A_n(z)=integral_0^a t^p(a+z-t)^(-1/2) dt

is convex in z>0, because for each t in [0,a] its integrand is a
nonnegative multiple of a convex function of z. Its integral is finite.
For the other summand set y=z-t to obtain

    B_n(z)=integral_0^infinity (z-y)_+^p (a+y)^(-1/2) dy.     (4)

Here u_+=max(u,0). Since p>=1, u -> u_+^p is convex; hence each
integrand in (4) is convex in z. Integrating its convexity inequality
proves convexity of B_n. The integrals have compact support in y for
each z, so there is no integrability qualification missing. Thus M_n=A_n+B_n
is convex for every n>=2.

Every partial sum in (2) is convex, and passing to the finite pointwise
limit in the convexity inequality proves convexity of T_B on (0,2).
The coefficient of M_1 is 1/(8 sqrt(2))>0, and the remainder is convex
by the same argument. Consequently T_B is strictly convex. This proves
the literal source Conjecture 1 for all its parameters.

For a checkable strengthening, T_B is C^2 in z locally inside (0,2),
by differentiation of the original fixed-interval integral and the smooth
moving-endpoint integral (their denominators stay positive locally).
Subtracting the M_1 term leaves a convex C^2 function, so

    d^2 T_B / dz^2 >= sqrt(a)/(16 sqrt(2) z^(3/2)) > 0.

The strengthened bound is ancillary and receives no separate credit.

The only general tools used are the binomial series, monotone convergence,
and preservation of convexity by positive sums, integrals and finite
pointwise limits. The source itself contains the original integral and
local curvature tests, but not this expansion/convex-moment argument.
Whether this is an eligible substantive advance or a routine classical
adaptation requires independent adjudication; no such clearance is assumed.
