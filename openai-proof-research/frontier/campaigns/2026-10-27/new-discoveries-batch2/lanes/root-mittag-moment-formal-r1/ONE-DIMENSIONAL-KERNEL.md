# Alternative positive-kernel route using only one-dimensional integrals

2026-10-28. Ordinary derivation, not yet a Lean certificate. This is a route for
one missing bridge of the same candidate, not a separate discovery. The frozen
ordinary proof and its independent preliminary review remain unchanged.

For v,w>0, write S=v+w and I(x)=integral_0^1 exp(x u²) du. The actual half-order
series gives E_(1/2)(i sqrt(vt))=exp(-vt)[1+(2i sqrt(vt)/sqrt(pi))I(vt)] for t>=0.
Thus its real cross product is

 K(t)=exp(-St)[1+(4t sqrt(vw)/pi)I(vt)I(wt)].

Define the positive Laplace mixture

 J(t)=(2sqrt(vw)/pi) * [
   integral_0^1 exp(-tw(1-u²))/(v+w u²) du
   + integral_0^1 exp(-tv(1-u²))/(w+v u²) du].

Every rate is nonnegative on u in [0,1], and every denominator is strictly
positive. Mixed lower differences of J are nonnegative by the already proved
interval-integral preservation lemma.

Here is an elementary proof that K=J. Differentiating u exp(xu²) and integrating
gives I(x)+2x I'(x)=exp(x). Hence

 K'(t)+S K(t)=(2sqrt(vw)/pi)[exp(-wt)I(wt)+exp(-vt)I(vt)].

Differentiating J under its compact-interval integrals gives exactly the same
right side: S-w(1-u²)=v+w u² in the first term, and the symmetric identity
in the second. The initial value is

 J(0)=(2/pi)[atan(sqrt(w/v))+atan(sqrt(v/w))]=1=K(0).

Consequently exp(St)(K-J) has zero derivative and zero initial value. This proves
the identity, without a polar-coordinate theorem or a moving angular cutoff.
At v=0 or w=0, the literal kernel equals exp(-(v+w)t), which is handled separately.
No zero-scale endpoint is silently removed.

The needed half-order formula can itself be obtained directly from the literal
series already defined in Lean. Put B_n=integral_0^1(1-u²)^n du. Integration by
parts of u(1-u²)^(n+1) yields

 B_0=1, B_(n+1)=2(n+1)/(2n+3) B_n,
 B_n=sqrt(pi)n!/[2Gamma(n+3/2)].

Uniformly integrate the exponential series on [0,1], with majorant exp(|x|):

 integral_0^1 exp(-x(1-u²))du = (sqrt(pi)/2) E_(1,3/2)(-x).

Use E_(1,1)(-x)=exp(-x) and the already proved genuine even/odd decomposition.
This specifies all links to the actual Mittag-Leffler objects; neither the
half-order formula nor the equality K=J is assumed in the current Lean component.

The analytic differentiations above are justified on every bounded t-interval
by continuous integrands and uniformly bounded derivatives (v,w fixed positive).
The resulting first-order identity extends through t=0 by the same compact bounds.
No asymptotic, stable-law existence, numerical inference, or new tool claim is used.
