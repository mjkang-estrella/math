# H012: compressed relation-witness operations

Status: independent concrete-mechanism development, no accepted improvement.
This targets a live limitation of H010's negative result: an explicit canonical
coefficient layer is expensive, but that does not lower-bound every compressed
circuit or algorithm bypassing that layer. No engine, experiment or broad formal
infrastructure is authorized merely because this possibility remains open.

## What a candidate must supply

Specify an executable operation finding a usable relation witness across the
five domains, including actual coefficient/circuit construction, exact emptiness
semantics, repeated/invalid roots, rational-point/sign checks and root extraction.
A fast evaluation circuit alone is insufficient. For the existing five-domain
collector with B~q^(1/5), the complete query cost/yield needs K/sigma=o(B^(3/2))
with a fixed power margin for an exponent claim, in addition to paid public setup,
rank, relation processing, memory and verification. No root/factor/support oracle.
A changed collector or family requires its own explicit ledger.

Native Astra /root/h006_structured_relation_ideas is exploring genuinely distinct
compressed mechanisms, such as circuit norm evaluation, subset zero predicates
with witness descent, and exact sketches with paid recovery, only if concrete.
Literal sparse/dense layer transforms and H009 long division are already rejected
in their scopes; no need to reimplement them. New ideas need a source of gain,
prior-art distinction, unsupported assumption and cheapest decisive falsifier.

## Root's known one-slice reference (not an algorithmic gain)

Once the OTHER FOUR coordinates are fixed, f(X)=S6(u1+X,fixedothers,r) has degree
at most16. For nonconstant f of actual degree d with companion matrix C_f of the
monic normalization, the standard resultant identity gives

    product_(zeta in mu_B) f(zeta)
      = (-1)^(B*d) lc(f)^B det(C_f^B-I).

Thus a single-domain predicate can use fixed-size polynomial/matrix work and
O(log B) powering. Degree drops, zero or constant f, and all field operations
must be handled and charged. Alternatively reduce X^B-1 modulo f by powering,
compute the bounded-degree gcd, and recover its split roots with all randomized
failures paid. Rational-point/sign verification still applies. Root supplied
this reference to the proposer for independent scrutiny; no implementation ran.

This is established bounded-degree slice processing, comparable to ordinary
elliptic sign/sum completion after fixing the other points. Scanning the B^4
outer tuples still loses. A useful compressed candidate must name the additional
operation that avoids that outer search, including witness recovery. High degree
is not a runtime bound; low circuit size is not a root-search algorithm.

## Distinct live roles

- Native Astra: this H012 compressed-witness operation brief, read-only.
- Native Sol /root/h010_early_dependencies: adaptive-target/base replacement for
  Factory Fable's two missing-output rounds; separate lens, no duplicated work.
- T3 Grok H010 hybrid geometry r1 remains live under its retained task ID.
- Root integrates shared records/commits. No experiments, children or edits in
  the delegated briefs. Useful parallelism without padded duplicate ideas.

Best supported reference remains classical square-root work with paid resources
and known automorphism constants. Verified improvement NONE. Next decisive step:
a full operation card that can survive mathematical and complete-cost review.
