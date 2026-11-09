# Two routes through the interpolation question

Status: complete proposed refutation of the literal source Conjecture 6.1; HOLD for independent source/prior/substantive review. Counts remain9 additional/39 total/next40. No formal certificate or manuscript.

## Route A: differentiate the exact divided-difference remainder

For real a,b with b>0 and a²+b²<1, put w=a+ib, v=a-ib. The second divided difference of z³ at w,v,z is w+v+z=z+2a. Thus for g(z)=z³/6 the interpolation remainder is

    R(z) = ((z-a)²+b²)(z+2a)/6.

This identity can also be obtained by polynomial division. Its derivative is

    R'(x)=(3x²-3a²+b²)/6.

The proposed comparison is |R'(x)|<=|x-a|. At x=1 and 0<a<1, R'(1)>0, and its excess over the claimed bound is EXACTLY

    [b²-3(1-a)²]/6.

Thus every pair with 1/2<a<1 and 3(1-a)²<b²<1-a² violates the conjecture at1. This is a nonempty open region, since 3(1-a)²<1-a² iff (2a-1)(a-1)<0 in the relevant interval. The rational choice a=3/4,b=1/2 lies strictly in it and gives gap1/96.

At x=0, the error is |b²-3a²|/6. In particular the z=0 clause fails when a>0 and b²>6a+3a², provided a²+b²<1. Choosing a=1/100,b=1/2 meets these strict inequalities and gives gap1897/60000. These calculations establish every hypothesis of both witnesses; numerical optimization played no role.

Mechanism: the imaginary separation contributes +b² to the derivative of the cubic remainder. The quadratic extremal candidate has derivative magnitude 2|x-a|, which contains no b² term. The real-node theorem cannot control this contribution by continuity in a when a approaches the evaluation point.

## Route B: an independent power-recurrence/operator route

Start from the interpolation operator itself, rather than a proposed remainder formula. For any m>=0 define

    U_m=(w^m-v^m)/(w-v).

Multiplying w,v by their quadratic equation yields U_0=0, U_1=1 and, for every m>=2,

    U_m=2a U_{m-1}-(a²+b²)U_{m-2}.

This is an exact all-order statement by induction. The slope of the interpolant to z^m is U_m. For m>=2, the normalized monomial g_m=z^m/[m(m-1)] has ||g_m''||_D=1. Its derivative residual at a real x is therefore

    x^(m-1)/(m-1) - U_m/[m(m-1)].

For m=2, U_2=2a and the residual equals x-a, precisely the conjectured quadratic baseline. For m=3, U_3=3a²-b². The inequality at1 reduces to b²<=3(1-a)², exactly the region found by the divided-difference route. The recurrence also gives U_4=4a³-4ab². This route explains why conjugacy does not eliminate imaginary dependence: it eliminates odd powers of b but leaves the even term -b² in U_3. The all-order recurrence, the normalized operator formula, and the exact failure region are substantive analytic work beyond an isolated failed shortcut or a finite sweep. The two routes converge on the same family; no extra credit is assigned to them.

## Strongest classical/subsumption objection

The witness is very short: interpolation of a cubic at two points is elementary. A reviewer can reasonably judge its discovery value modest. That judgment is separate from a complete classical bridge. The literal source devotes Section6 to proposing these complex-grid extensions; its own Proposition6.1/Corollary6.1 give formulas, not the desired estimates. They actually accommodate the displayed witness.

The nearest cited real-node result is Shadrin, *Error bounds for Lagrange interpolation*, JAT80(1995)25–49. Its journal body lies on an excluded publisher route and was not fetched or retried; only the source's actual pp14–15 account was read. Thus a full audit of the Shadrin proof and its citing literature is a remaining prior-art gate. The claimed real-node uniform theorem does not logically imply a pointwise complex-node inequality. For the real-node two-point cubic geometry b=0, our first-clause obstruction disappears.

Actual closest available primary bodies: Ellard–Šmigoc1604.05148v1, Theorem1.4, Example2.1, Lemma2.2 and Theorem2.3 proof (pp3–4) use even/odd elementary symmetric functions and real interlacing to obtain parity-separated Newton-type inequalities. Example2.1 explicitly has vanishing odd elementary functions for imaginary pairs. It neither states the interpolation conjecture nor its refutation; it explains why transferring unrestricted real-variable inequalities is dangerous. Khare–Tao1708.05197v6 Proposition1.13 (pp10–11) is stated on positive REAL coordinate tuples. Its proof apparatus in §8 is not a theorem on conjugate complex grids. The source itself cites this restriction on p15. No inference of a complex-domain bridge from a real-positive Schur quotient is legitimate.

A possible strong objection is that these known formulas and imaginary-pair examples make the counterexample routine. We have not identified a published same-object refutation or a predecessor theorem explicitly supplying it. Root must adjudicate both the elementary-shortness objection and the incomplete prior-art gate. No new-to-literature assertion is made.

## Limits and next step

The version-specific universal negation is complete; no mathematical gap in that endpoint is claimed. Unresolved: independent verification, broader citing/journal body search and current public-registry clearance under inherited denials, and substantive qualification. Do not invest in optimal constants or Conjecture6.3 merely to pad this result. The decisive next action is independent source/subsumption review of PROOF.md and frozen pp14–16. No child or review was started by this lane.
