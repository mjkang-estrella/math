# Research deduction: the full shifted bound via a binary filtration

Dated 2026-10-28 UTC; credit 0 pending root gates. The complete ordinary argument
is PROOF.md. It proves the requested all-coefficient law, relying on the supplied
sound r3 literal-formal Riccati bridge and attainment. This is not a partial
range, top-coefficient-only, or helper submission. No analytic phase identification
is assumed, and the original-variable theorem in 2609.29531v2 is excluded.

The exact target is Iván Area, arXiv:2608.23006v2, Definition 2.1 (6)–(7),
Remark 3.8, u=alpha²-1/4,v=beta²-1/4, all integers r>=1. We prove

    (r-1)! J(s_(2r-1)) ∈ 2^(2r-2) Z_(2)[u,v],

indeed the stronger (d-1)! homogeneous-degree-d version for all 1<=d<=r.
The supplied pure-u coefficient then attains denominator exponent
2r+v2((r-1)!), resolving the entire literal shifted law as an ordinary theorem.

## Classical tools and supplied dependencies

The Riccati construction and its exact source bridge are adopted from
sol-jacobi-shifted-denominator-r3/discovery.md and the root r3 ADOPTION.md.
The root r2 ADOPTION.md was read and its false parity/equivalence/checker
inferences are not used. Binary-digit subadditivity, factorial Legendre formula,
odd-unit triangular inversion, and the primary's binomial valuation are classical
or published tools. No general WKB integrality claim is invoked. The already
proved attainment, parity and degree bounds do not receive separate credit here.

## All-order research mechanism

Use the integral normal-form algebra R=Z[x,w]/(w²-x²-1), with
partial x=-w², partial w=-wx. With a=u+v,b=u-v and P=aw²+bwx, one has V=2P
and D=2 partial. The degree-d part of the original s_n is
2^(n+1-d) times that of the integral Riccati sequence h_n with potential P.

For nonzero parameter bidegree (i,j), let q(i,j)=s2(i)+s2(j)-1.
The coefficientwise weighted class C is stable under the derivation, addition,
negation, doubled products and squares. The square proof pairs distinct parameter
monomials; equal monomials use q(2i,2j)=q(i,j). The Riccati convolution pairs
distinct spectral indices; a remaining diagonal term is a square. These two
pairings give h_n ∈ C for every n, rather than only in a checked range.

The w-parity of the coefficient at a^i b^j equals j modulo 2. For odd j,
q(i,j)=s2(i)+s2(j-1)>=s2(i+j-1). Thus the w-odd part of homogeneous degree d
has the factor 2^s2(d-1). For odd n the normal form is

    (1+x²)A(x²)+wx B(x²).

The first part has an odd polynomial partial-primitive vanishing at x=0.
The second has primitive w f(x²), where

    f(X)+2(1+X)f'(X)=-B(X).

Its coefficient matrix is triangular with odd diagonal 2k+1, so f preserves
the entire factor 2^s2(d-1) over Z_(2). At t=1, x=0,w=1. The original
primitive's scaling is 2^(n-d), so its degree-d midpoint coefficient has
valuation at least n-d+s2(d-1). For n=2r-1 this is
2r-2-v2((d-1)!), exactly the stronger sufficient bound. Integral substitution
a=u+v,b=u-v transfers it to the requested variables without dividing by 2.

This explicitly controls the coordinate denominators, quotient reduction,
primitive denominators and factorials which the root lead left unresolved.

## Adversarial limitations and falsifiers

The strongest ordinary-proof attack is at the weighted quadratic closure or the
primitive normal form. PROOF.md supplies both in detail; no unresolved ordinary
all-coefficient lemma remains in that argument. The formal counterpart is still
incomplete, and no independent reviewer has assessed this new proof yet.

C is NOT a subring: a,b ∈ C but ab ∉ C, because q(1,1)=1. Forgetting the factor
2 in off-diagonal spectral products would therefore invalidate the proof.
Likewise one must pair unequal parameter monomials inside each square.

The mandatory r=2 t-primitive t+t³/3 still refutes coefficientwise pre-midpoint
divisibility in the t basis. The proof selects the w-odd component after an
integral recurrence in a different algebra; the odd-x primitive part vanishes at
the midpoint. For example the degree-two normalized h_3=-P² has primitive
midpoint 2ab/3; rescaling multiplies by 2, giving 4(u²-v²)/3, consistently with
the mandatory example. The false generic shifted moment 464/315 is not used.

## Exact validation and formal status

check.py constructs R as unique sparse normal forms with w exponent 0 or 1.
It checks the full bidegree filtration for n<=15, normal-form primitives r<=8,
and compares independent original t-Laurent and literal source cumulant
constructions through n=9. Finite ranges were selected to test normalization
and cancellation, not extended for their own sake. The final test run passes
and `/usr/bin/time` reports 55836 KiB RSS. A 480 MiB address-space limit is set
for the Python experiment. Checks are not the proof of the universal assertion.

formal/ArithmeticStart.lean is a deliberately small verified beginning: five
natural-number divisibility lemmas, actual #print axioms only propext. The final
pinned Lean run passes at 174220 KiB observed RSS. The complete literal endpoint
and all unimplemented source/filtration/primitive/attainment modules are spelled
out in LEAN-BRIDGE-PLAN.md. No completed Lean theorem or acceptance is claimed.
An initial failed broad import exceeded 512 MiB RSS; it is candidly retained,
not reclassified as bounded. Guarded later attempts stayed below the ceiling.

## Current sources, chronology and novelty limits

Read the full mandatory r3 source record and both root adoptions. Fresh public
primary and companion HTML hashes equal r3's cached raw HTML exactly. Current
versions remain v2 October5 and v2 October14. Full companion body read; its
original-variable theorem does not provide the shifted bound.

Fresh registry heads, untruncated subtrees, actual catalogue bodies and search
scope are in source/registry-screen.md and receipts. The newer trureturing
head e1b5b0c6ee6c878a2b9a1b2df49f59bac5d6ed37 has commit time
2026-10-28T23:34:01Z; proof written after retrieval starting23:37 UTC. No matching
counterpart located in that bounded screen; no worldwide-priority claim. The
full broad compositional-square denominator entry was read and is a different
specific functional equation, not a located subsumer of this Jacobi argument.

No ledger/count/shared-lane edits, git actions, child agents, worker polling,
browser tabs, access-control bypass, uploads, messages or account changes.
Root alone decides independent acceptance and discovery credit.
