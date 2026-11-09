# W003 parent norm gate — coordinator disposition

2026-10-08. **Accepted at the scopes below, with a correction to the
one-field limitation.** Verified new complete classical factoring complexity
improvement: **NONE**. The research objective remains active.

The coordinator consumed all 322 lines of the
[independent review](W003-normgate-review.md) and checked its new identities
against the 190-line [assessed note](W003-normgate.md). All 18 frozen review
inputs, 30 review delivery entries and 16 original delivery entries verify.
Only the mutable STATE original differs from its frozen review input; all
other originals match. The review SHA-256 is
`6418998b6e1e3f5e3708011ca7e8c4261f66b98be6aee1b57558f815fe521269`.
The assessed note remains unchanged, SHA-256
`dae0f013bac05b31ce3b3f6373fcd8e2a2d0e3b0ff35086574a27cea6f26af5f`.
This disposition governs their historical provisional labels and preserves
the original source, access and delivery records.

## Construction and paid reference accepted

For odd N>1 with gcd(N,15)=1 and a unit 1<=R<N, the modular equation
u_0^2+v_0^2=5R has a solution. The local square-set intersection, lifting
through a nonzero coordinate and CRT prove this for arbitrary prime-power
multiplicities. The proof uses the factors only for existence. R need not
be a square for this subproblem.

The two sorted N-record lists with witnesses and a fixed tie rule give a
deterministic reference without a factor oracle. Retain the review's fixed
multitape, schoolbook-arithmetic realization: **O(N n^2) time and O(N n)
working bits**, n=bit_length(N), including list construction, sorting,
sequential access and verification. This is exponential in n. A faster
replacement must supply its own input domain, cost, randomness and failure
contract. The later polynomial overhead does not erase the Norm2 cost.

Given a verified reduced pair, set u=u_0+4N, v=v_0, s=u^2+v^2, t=2R and
f(T)=T^2-sT+t^2. Accept the height bounds, discriminant between consecutive
squares, irreducibility and positive conjugates. Modulo N,

    f(T)=(T-R)(T-4R),    f'(R)=-3R,    s=5R.

The derivative and s are units. The direct trace identity
(2alpha-s)w=Tr(alpha*w)-s*Tr(w)+Tr(w)*alpha clears an integral w into
Z[alpha]; it does not allow arbitrary denominators or a map from the whole
field to Z/NZ. Accept the exact criterion that alpha is a square in K iff
s+2t or s-2t is an integer square. These events give verified roots k/3 or
k of R respectively. Their frequency is not established.

The identities A^2+B^2=alpha and Norm((A+beta)/B)=-1 are retained, with
A=(u*alpha+v*t)/s, B=(v*alpha-u*t)/s and beta^2=alpha. B is nonzero in K,
but division after reduction requires its image to be a unit. A proper gcd
is a factor; a zero image gives the separate verified root Abar. Extending
the reduction to beta would require a root of R that is not supplied by
the norm certificate.

## One-field completion and precise remaining target

Replace the assessed note's denial of an allowed rational-row product by
the following explicit completion from review section 6:

    t^2-u^2*alpha = alpha*(v^2-alpha),
    Q(T)=(t^2-u^2*T)*(v^2-T),
    Q(alpha)=alpha*z^2,    z=v^2-alpha.

The two allowed pairs are (t,u) and (v,1). Irreducibility makes z and both
rows nonzero, including when v=0. This is an exact one-field twisted target
with polynomial construction and verification overhead after Norm2. It
does not make alpha a square on the continuing branch.

For g=v^2-R modulo N, the row images are R*g and g, giving Q(R)=R*g^2.
A proper gcd(g,N) yields a factor. If g=0 modulo N, v is already a root
of R. If g is a unit, the identity by itself provides no root of R. There
is no proved frequency of either earlier success. Norm(z)=t^2-u^2*v^2
and Norm(t^2-u^2*alpha)=t^2*Norm(z), with magnitude bounds O(N^4) and
O(N^6); these bounds supply no smoothness or relation-yield theorem.

Accept the conjugate-reuse obstruction. Any rational polynomial Q satisfying
Q(alpha)=alpha*z^2 satisfies Q(alpha')=alpha'*tau(z)^2 under conjugation.
If that second value were a nonzero square, alpha' and therefore alpha
would be squares, contrary to the continuing branch. The reverse orientation
has the same obstruction. This excludes reusing conjugates of this law;
it does not exclude independently chosen fields.

Also retain [alpha]=[s+2t]=[s-2t] in K^*/K^{*2}, since
(alpha±t)^2=(s±2t)*alpha and s>2t. In particular the explicit two-row
witness rules out a character separating [alpha] from the subgroup of all
rational-pair rows in this one field. The remaining question is constructive:
can the same rational-row product be an ordinary square in an independently
selected second field, with recoverable unit images and a paid useful
success law? One-field attainment is no longer the missing step.

## Source and probability boundaries retained

Accept the source qualifications at the inspected primary passages only.
Shallit's D=-1 specialization reaches the sum-of-two-squares base case;
the separate referenced fast method was not obtained. BGH section 5 can be
matched using c=(5R)^(-1) and coefficients c,4c, which are distinct units,
then (u_0,v_0)=(X,2Y). Suitable prime production, the integer-conic inputs
and unit denominators remain charged. Neither inspected passage verifies
the complete unconditional fast Norm2 contract used here. This is a source
limitation, not evidence that a faster solver does not exist.

The review's six focused searches did not obtain AEM's full primary theorem
or proof. Preserve that limitation and its search ledger. Abstracts and
metadata do not settle the exact domain, success probability or expected
cost. No additional retrieval loop is selected by this disposition.

For an outer uniform unit square R modulo odd N with r distinct prime
divisors, an actual inner root independent of the hidden x conditional on R
gives a proper gcd with probability 1-2/2^r. Unequal prime-power exponents
are allowed. Raw-word rejections, nonunits and elementary preprocessing
remain separate charged branches. This conditional law supplies no lower
bound on the event that the inner construction returns a root. Norm2
success is not factoring success, and no complete restart bound follows.

## Next action

The parent norm gate is complete as a reviewed construction and correction.
The existing [W004 constructive task](../tasks-W004.json) should consume this
accepted two-row witness and the completed Lens B disposition while retaining
its [frozen brief](../hypotheses/W004.md). Pass the result as an in-flight
research update, not a new review round or a change to frozen inputs.
Its independent-field selector and proposed mixed-target construction still
require their own proof, cost, success accounting and separate review.
No experiment, implementation, Lean change or new speedup is selected here.
