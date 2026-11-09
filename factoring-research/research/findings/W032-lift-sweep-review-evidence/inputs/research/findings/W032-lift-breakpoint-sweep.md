# W032: sweep an entire N-lift family through quadratic-many breakpoints

Parent constructive derivation, 2026-10-08. **Unreviewed; no experiment.**
Verified complete factoring improvement: **NONE**. This is a concrete
consumer for the new exact carry quotient, not the earlier individual-digit
uniform-sampling claim and not an assumed fast generator.

## Acquire one base stencil

Let R>=2, M=N^(2R), L=2R-2, m=2R+1. Retain the checked denominator
branch leastprime(N)>2R+1. Choose positive consecutive base points

    a_i=a0+i,  0<=i<=m,   a0+m<N,

all units modulo N. Taking a0=1 makes a_i=O(R); a nonunit initial point
is a paid ordinary factor exit, never silently removed. Acquire the lower
remainders r_i=[V_R(a_i)]_M through the exact polynomial recurrence in
W032-exact-carry-quotient.md. Since r_i=1 modulo N^2, write exactly

    r_i=1+N^2*u_i,    0<=u_i<N^L,
    u_i=v_i+N^(L-1)*b_i,
    0<=v_i<N^(L-1),   0<=b_i<N.

The base carry quotient is the integer

    c0=Delta^m u_i/N^L=Delta^m r_i/M,    |c0|<4^R.

The sign convention is that of the signed binomial weights
w_i=(-1)^(m-i)binom(m,i). Retain these O(R)-bit integers.

## One shared lift parameter and its exact law

For each integer w in [0,N), lift EVERY base point by the same amount

    a_i(w)=a_i+12*N^(L-1)*w.                           (1)

These are unwrapped integers, not canonical representatives modulo N.
They remain units and consecutive; their O(R logN)-bit input widths are
paid. The accepted scalar polynomial extends to these integer inputs.
The polynomial for U=(V_R-1)/N^2 modulo N^L has derivative a/12 modulo N:
its leading low-precision term is a^2/24 and all other terms are
multiples of N^2. Taylor expansion of (1), with L>=2, therefore gives

    U(a_i(w))=u_i+N^(L-1)*a_i*w mod N^L,
    u_i(w)=v_i+N^(L-1)*[b_i+a_i*w]_N.                 (2)

All terms quadratic in the shift have valuation at least 2L-2>=L.
Here 12 is a unit since R>=2 and the least-prime guard excludes 2 and 3.
There is no hidden prime or period used to choose the lifts.

The exact carry quotient of the lifted stencil is consequently

    c(w)=c0-sum_(i=0..m) w_i*floor((b_i+a_i*w)/N).     (3)

Indeed the change in Delta^m u divided by N^L is
Delta^m(a_i*w)/N - Delta^m floor((b_i+a_i*w)/N), and the first term
vanishes exactly because a_i is affine in i and m>=2. Thus no fractional
term is discarded. Every c(w) is an integer, |c(w)|<4^R by the general
carry-quotient bound, and its gcd with N equals the original filtered gcd.

This is not a claim that c(w) or its gcd is uniform. The full-lift
individual-digit law supplies no independent law for this shared parameter
or this divided finite-difference consumer.

## Enumerate every attained value without enumerating w

For positive a_i and b_i in [0,N), the ith floor starts at zero and
changes by one at integer thresholds

    w_(i,k)=ceil((k*N-b_i)/a_i),
    1<=k<=a_i,   1<=w_(i,k)<=N-1.                   (4)

Because a_i<N, a single floor cannot jump by two at one integer w.
There are at most sum_i a_i thresholds. They may coincide across i;
such ties MUST be processed together before testing the new c value.
Testing intermediate tie updates would create values never attained by
any actual lift, and would not validate this consumer's stated family.

Start with c=c0 at w=0. Sort all retained threshold records (w,i,k).
At each distinct threshold w*, subtract sum w_i over the records at w*
and test gcd(c,N). The function is constant between adjacent thresholds,
so this procedure tests every attained c(w), including the final interval.
If an interval has length one, its value is still represented. If there
are no thresholds, only c0 is tested. Zero and full gcds are failures.
Repeated c values may be retained or deduplicated with paid bookkeeping.

For a0=1,

    sum_i a_i=(m+1)(m+2)/2=O(R^2).

Thus at most 1+O(R^2) distinct interval values are tested even though
the family has N parameter values. Generating thresholds, sorting them,
and processing ties is a specified algorithm; no root-finding or ordering
oracle is assumed. General a0 incurs O(R*a0+R^2) records, so a huge base
start cannot be treated as having the same cost.

## Complete primitive cost and the unresolved yield

Base acquisition has the proposed shared-polynomial bound soft O(R^2 logN),
pending its own audit. Event numerators kN-b_i have O(logN+logR) bits;
their positive integer ceiling divisions use known a_i. With a0=1,
there are O(R^2) records and comparisons of O(logN+logR) bits. Weights
and c have O(R) bits. The O(R^2) gcds use actual operand widths and
proper-factor validation. A conservative total primitive envelope is
soft O(R^2*(logN+R)), including the base polynomial work, random-free
events, sorting, ties, and gcds. Space for the explicit event list is
O(R^2*(logN+logR)) bits plus base polynomial arithmetic workspace.
This is not an implemented fast-arithmetic benchmark.

For R=Theta(logN) the full-family sweep is polynomial in input length.
Its output count is also only polynomial. There is NO theorem that one
of those values has a proper gcd. This can compress an unproductive family
just as effectively as a productive one. A failure exhausts this exact
family at the supplied R,a0; it is not a primality certificate or a lower
bound against different depths or base points. All depth choices and
restarts must be charged in any eventual factoring algorithm.

The decisive next steps are an independent derivation/complexity audit
and a single preregistered bounded screen that records ALL intervals,
ties, zero/full/proper outcomes, and failed charts. Compare (3) at frozen
control w values with direct polynomial re-evaluation at the actual lifted
inputs. Such a test can falsify bookkeeping or obvious degeneration,
but cannot establish an asymptotic factor-supply theorem. None is run here.
