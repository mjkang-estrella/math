# Proposed classical-root route for the clamped tail (not fully formalized)

This is an alternative to the Cramer--Indritz ingredient of the original
PROOF.md. It is NOT covered by the original19-file preliminary review freeze.
It needs a new final mathematical/formal review if integrated. No new discovery
credit is claimed for any classical root, Cauchy, peak-location or scalar lemma.
The full original mathematical proof remains unchanged and can be reviewed on
its own merits. The source conjecture and its all-degree scope are unchanged.

## Peak inequality

Let p=H_n be the physical Hermite polynomial, E=2n+1, and
y=p exp(-x^2/2). All roots r_i of p are real, with multiplicities. At a real x
where p(x)!=0 and y'(x)=0, set t=p'/p and q=E-x^2. Then t(x)=x.
The Hermite equation yields the Riccati identity

    t'=2xt-2n-t^2.

Differentiate twice more and substitute t(x)=x:

    t'(x)=1-q,   t''(x)=2x,   t'''(x)=2-2q^2.

The logarithmic derivative of the actual real-root factorization gives, writing
a_i=1/(x-r_i),

    sum a_i^2=q-1,   sum a_i^3=x,   sum a_i^4=(q^2-1)/3.

Cauchy--Schwarz applies to the real vectors(a_i),(a_i^2) even when some a_i
are negative. Thus x^2 <= (q-1)(q^2-1)/3. Since x^2=E-q,

    3E <= F(q),   F(q)=q^3-q^2+2q+1.                     (1)

No assumption that x exceeds all roots is needed. No zero-count or simple-root
hypothesis is needed: the full root multiset is used.

## Excluding peaks after the literal cutoff

F is increasing on the whole real line, since its derivative is
3(q-1/3)^2+5/3>0. Let b=22/7 and R(E)=b-b^2/(4E). For E>=7,

    pi-pi^2/(4E) <= R(E),

by factoring the difference as(b-pi)(4E-b-pi)/(4E)>=0. Exact rational algebra:

 (3E-F(R(E)))*117649E^3
   =352947(E-7)^4+6535179(E-7)^3+40836159(E-7)^2
       +89231464(E-7)+19560668 >0.                       (2)

For the source a=sqrt(E)(1-pi/(2E)), a^2=E-pi+pi^2/(4E).
If x>=a then q=E-x^2<=pi-pi^2/(4E)<=R(E), so (2) contradicts (1).
Consequently, for every n>=3 there is no nonzero weighted-Hermite stationary
value at or after the literal source cutoff.

Since y^2 tends to zero at infinity, a compact-maximum/Fermat argument implies
y(x)^2<=y(a)^2 for every x>=a: otherwise take a compact interval from a to a
large point where the value is smaller; its positive interior maximum would be
a forbidden stationary value. The bulk inequality at a therefore supplies
the entire clamped tail for n>=3 without a global Cramer inequality. Degrees1
and2 use the explicit elementary global bounds already justified in PROOF.md.

## Real-rootedness proof being formalized

For complex z put v_k=H_k(z) and B_k=Im(v_(k+1) conj(v_k)). The physical
three-term recurrence gives

    B_0=2 Im z,
    B_(k+1)=2 Im z |v_(k+1)|^2+2(k+1) B_k.

If Im z!=0 then (Im z)B_k>0 by induction, so v_(k+1) cannot vanish. This proves
all complex roots real. Formal RealRoots.lean proves this directly and then
the real polynomial splitting, without assuming an abstract Hermite surrogate.
The earlier real-rootedness proof read in the public trureturing clone at
f8ffe9ed02e01601ed0b43a400ebc1c09cdc6ada used a different division/imaginary-ratio
induction; it was a useful classical reference. No code was copied into this
cross-product proof and no prior Hermite real-rootedness is claimed as new.

## Formal checkpoint now complete for the tail

The parent has compiled RootMoments.lean: the actual Hermite polynomial splits,
its roots are indexed by positions in the roots.toList (retaining multiplicities),
and the polynomial splitting log-derivative identity is differentiated locally
only where the polynomial is nonzero. All three root-moment identities above
are instantiated; no moment hypotheses remain in stationary_peak_inequality.
TailMaximum.lean proves polynomial-Gaussian decay, the compact-maximum/Fermat
transfer and source_tail_abs for every n>=3 at the literal sourceCutoff.

LowTail.lean supplies direct global square bounds3/2 for degree1 and25/4 for
degree2 and proves these fit the exact clamped source Gamma coefficients.
The degree2 bound uses the exponential Taylor lower sum throughdegree5 and
an exact positive polynomial certificate: on[0,2] its Bernstein coefficients
are positive, and on[2,infinity) its shifted quadratic remainder is positive.
The source cutoff is positive and lies strictly inside the turning point.
SourceAssembly.lean transfers ANY proved bulk bound to the literal source
statement and closes the even-degree and degree1 all-x cases. These subcases,
classical roots, Taylor and Cauchy helpers are UNCOUNTED.

Checkpoint:111 declarations across11 modules, all actual types/axiom reports
read; only propext,Classical.choice,Quot.sound. This is a local supporting
compilation checkpoint, NOT an independent final strict candidate replay.
The generic odd comparison/strict loss and pre-x0 bulk estimate remain before
source full assembly. The new tail route is not covered by the original
preliminary freeze and must receive a new final mathematical/formal review.
No complete source-conjecture proof, manuscript, packet or credit is claimed.
