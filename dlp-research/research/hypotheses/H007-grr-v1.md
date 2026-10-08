# H007 GRR-v1: corrected five-point relation system

Independent Claude Opus proposal, native Astra /root/encoding_review mathematics.
Cost/prior-art review COMPLETED under ecdloop-h007-algebra-cost-priorart-astra-20261008-r1; see findings/H007-algebra-cost-review.md.
No experiment or Lean claim. Main improvement NONE.

Freeze p>3, E:y²=C(x)=x³+ax+b, full odd prime order q, finite target R=(r,s).
B=2^k divides p-1, k>=1. Coordinate candidate set V=u+mu_B. This restricts
the prime family; the auxiliary-isogeny extension in the raw report is NOT supplied.
All solver outputs must be Fp-rational coefficient tuples.

Four unknowns c2,c1,d1,d0:
D(x)=d1*x+d0;
A(x)=x³+c2*x²+c1*x+c0;
c0=s*(d1*r+d0)-r³-c2*r²-c1*r.
Then f=A+yD vanishes at -R. Its norm A²-C*D² is divisible by x-r.
h=(A²-C*D²)/(x-r) is monic quintic, coefficients degree<=2 in four unknowns.
The normalization covers every five-finite-point decomposition, with repetitions:
the required divisor has pole order exactly6, with unique leading basis termx³.
O targets and decompositions containingO are outside this frozen relation finder.

Let g0(X)=h(X+u)=X^5+z4 X^4+z3 X³+z2 X²+z1 X+z0.
Its monic root-squaring Graeffe map is:

    G(g)=X^5+(2z3-z4²)X^4+(z3²+2z1-2z4*z2)X³
           +(2z3*z1-z2²-2z4*z0)X²+(z1²-2z2*z0)X-z0².

Introduce five coefficients for eachg0,...,g_(k-1); linkg0 to the norm/shift,
successive maps, and finalmap to(X-1)^5. Exactly4+5k unknowns,5(k+1) quadratic
equations. Substituting initial quadratic coefficients into firstmap instead
would create quartics: retain the stated auxiliary coefficients.

Terminal condition means everyroot ofg0, WITHmultiplicity, lies inmu_B.
It does NOT mean g0 dividesX^B-1. Example(X-1)^5 passes but cannot divide a
squarefreeX^B-1. Repeated roots may be valid repeatedpoint relations.

## Paid extraction and exceptions

Splitg0 withmultiplicities using a supplied primitiveB-throot and recursive
gcd splits over two-power subgroup cosets. Root-of-unity construction, modular
powering, gcds, extraction and storage are charged; no free scan ofB candidates.
Translate roots byu. Reject this solution ifgcd(h,D)!=1. Otherwise
y=-A(x)/D(x) is rational, satisfies thecurveequation, and retains multiplicities.
Verify the five-point sum equalsR. Ifx=r occurs andD(r)!=0, that branch is-R;
normdivision removed exactlyone occurrence. The orientation is not arbitrary.

Rejecting commonfactors is an explicit restriction: some valid oppositepoint
pairs and invalid nonrational pairs are both excluded. The raw assertion of
automatic validity for every rationalx is false. A conditional symbolic example:
D=0,A=(x-r)(x-c)²,h=(x-r)(x-c)^4, withr,c inV andC(c) nonsquare, passes
membership but includes nonrational points. No such numerical fixture was run.
Full branch completeness would need separate divisor factorization, rationality,
multiplicity and square-root work. Full odd group order excludes rationaly0
points; an odd subgroup alone would not suffice.

## Hypothesis, cost gate, prior art

Low equation degree and permutation symmetry do not imply cheap solving.
An actual solver must price Fp-rational root filtering, empty systems, discarded
exceptional solutions and extraction. A Groebner computation overFp can return
algebraic-closure solutions; coefficient-field arithmetic alone is not filtering.
The raw m! success/failure rate and solutioncount reduction are unproved.
B counts candidatex values; signed factor-base pointcount is different.

For general attempt costT and useful yield sigma, aboutB/sigma attempts plus
dependency solving is a conditional ledger, not an established expectedcost.
AtB=q^(1/5), beating sqrt requires(B/sigma)*T+setup+linearalgebra below sqrt.
No sparse-linear-algebra complexity may be assumed from sparse rows alone.
The known direct-Q label-independence recovery can avoid a full-rank requirement,
but does not supply useful yield or fast dependencies.

Primary PKM sections3.3-3.4 inspected by reviewer:
https://www.iacr.org/archive/pkc2016/96140156/96140156.pdf
P-224 has a large two-power factor inp-1; this does not establish an infinite
simultaneously suitable prime-order family or a secp256k1 algorithm.
An auxiliary-curve rational-isogeny factorbase does not automatically yield the
same divisor-level Graeffe chain. Poles/denominators/pushforward need construction.

Disposition: surviving, narrowly specified solving-complexity hypothesis.
Independent prior-art/fullcost review completed; an actual justified solver still precedes selection of a finite test.
The proposer's multi-parameter F4 sweep is NOT authorized; no proof it fits
60seconds/1M instrumented events, and finite slopes do not prove asymptotics.
