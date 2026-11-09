# W005 — construct the second field around an exact square

Date: 2026-10-08. **PROVISIONAL parent derivation for independent review.**
Verified new complete factoring improvement: NONE. Symbolic work only.

## Computation being changed

The accepted W004 construction fixes both fields, then searches for a packet
which is twisted-square in the first and ordinary-square in the second.
Here construct the second trace from a rational square certificate. This
eliminates that second-field square test/search algebraically. The remaining
modular constraint is explicit below, and appears to retain the hard root
choice rather than solving it. This is a concrete generator, not a point oracle.

Take integers u,v,t with s=u^2+v^2, t=2R, s congruent to 5R modulo odd N,
and gcd(N,30R)=1. The first field is the accepted irreducible
f_1(T)=T^2-sT+t^2. Its packet is

    Q(T)=(t^2-u^2*T)*(v^2-T),
    Q(alpha_1)=alpha_1*(v^2-alpha_1)^2.

The blinded norm sampler now supplies the residue pair cheaply under its
strict interface; the first lifted u,v can be obtained by the accepted selector.
The formulas here also work for any such fixed first anchor.

Write d=v^2-u^2. Choose a nonzero rational parameter tau and put

    H=(tau+d/tau)/2,       k=(tau-d/tau)/2,
    h=t*H,                D=k^2-u^2,
    s_2=-(u^2*v^2+t^2+2*t*H*k)/D.                         (1)

Skip D=0. Since H^2-k^2=d, coefficient comparison modulo
f_2(T)=T^2-s_2*T+t^2 gives the exact identity

    Q(alpha_2)=(h+k*alpha_2)^2.                            (2)

Indeed the constant coefficients are t^2*(v^2-u^2), and the alpha_2
coefficients agree by the definition of s_2. This constructs an ordinary
square, with its root, in a field chosen afterward. Testing irreducibility of
f_2 and distinctness from the first quadratic field is still charged, and
failed choices remain failures. No positive supply is asserted for those tests.

s_2 is rational here. This deliberately changes W004's integral-trace selector.
Before modular use require tau and D to be units in Z_(N), so h,k,s_2 lie
in Z_(N). Every rational denominator is cleared and checked. One may work
with the rational quadratic algebra and the explicit root h+k*alpha_2;
there is no appeal to the old integral-root trace formula in this step.
Positivity s_2>2t is not claimed or needed by identities (1)-(2).
If some downstream construction requires it, that is a separate filter.

## The actual modular equation

Require s_2 congruent to s modulo N, ensuring f_2(R)=0.
Set g=v^2-R. For unit tau,D the trace condition is equivalent to

    (tau^2-R)*(9R*tau^2-d^2)=0 mod N.                     (3)

Exact derivation before reduction: writing F=-(u^2*v^2+t^2+2tHk),
one has
4*tau^2*(F-sD)=
 -(2t+s)*tau^4 +(2s^2-4u^2v^2-4t^2)*tau^2 +(2t-s)*d^2.
Using t=2R and s=5R modulo N factors this as the negative of (3).
No factorization of N is used in the identity.

When g is a unit, reduction of the explicit ordinary square root produces

    y=(h+kR)/g = R*(3tau^2+d)/(2*tau*g),    y^2=R mod N.  (4)

Thus a valid tau is already a root-producing certificate, and can be verified
in polynomial time. This alone is not an efficient method to find tau.

For a clean separated-branch analysis additionally require d, g, and
v^2-4R to be units. A proper gcd in those checks returns a factor; a full
gcd may be skipped. Their product restrictions are not granted positive mass.
Modulo each p^e dividing N the two factors of (3) cannot both be divisible by p,
because d^2-9R^2=4*(v^2-R)*(v^2-4R). Hence each local branch satisfies exactly

    tau^2=R,       giving y=tau,
    or 9R*tau^2=d^2, giving y=d/(3tau).                    (5)

If both types occur at different prime powers, gcd(tau^2-R,N) immediately
splits N. If the type is uniform globally, (5) still gives a root of R.
The four local parameter roots correspond to two choices of root sign and
two branch types. Repeated primes need the unit separation just stated.

## Why the easy construction from the outer x is not a speedup

Knowing x with x^2=R makes two global branches cheap:

    tau = x mod N,        or tau = d/(3x) mod N.

One may use any rational/integer lift having these residues and charged
height. Both choices give y=x in (4). Negating either gives y=-x.
Thus generating the compatible field from either globally chosen branch,
and recovering its displayed ordinary square, yields a trivial outer gcd.
Random integer lifts, choosing between these two branches, or negating them
does not change this conclusion. In an irreducible quadratic field the only
two roots of the nonzero Q(alpha_2) are +/- the displayed one, so another
exact square-root algorithm cannot repair this correlation.

This closes only those explicit constructions. It does not prove that all
possible field distributions, all mixtures, or other packets are useless.
It also illustrates why root-choice independence of the ORIGINAL norm
certificate does not license later use of x in the field selector: the
new trace is outside the accepted inner interface if constructed this way.

The independent-root or mixed-local-sign problem is therefore still present
in a concrete low-degree congruence. To improve it, one would need a different
computation that finds useful tau without tying all local signs to x, with
paid probability and work; simply renaming (3) an easy quartic is not one.

## Cost, falsifier, and constructive response

For inputs and tau of b bits, (1)-(4), denominator checks and quadratic
irreducibility/distinctness tests have polynomial bit cost. Searching tau,
unbounded lift heights, rejection and branch distribution are not included
for free. A scan is a real algorithm but has no improved coverage bound.

The cheapest decisive test is symbolic: expand (1)-(2), factor the trace
residual, verify (4)-(5), and inspect the strict root-choice dependence.
No numerical run is proposed until an actual new tau-generation mechanism
survives that gate.

The failed assumption is that constructing an ordinary square before choosing
the field automatically removes the modular-root constraint. It instead moves
that constraint to (3). A materially different next computation would keep
the field selector entirely inside the blinded-certificate interface and use
its uniform residue distribution for a priced sieve or a coupled computation
over many parameter values. Such a computation must specify its actual
products/updates and success law; none is granted by this note.
