# A certified four-variable floor-sum lower bound

Research manuscript and source certificate, 30 October 2026. Acceptance, credit,
publication and worldwide priority are not asserted.

## Abstract

We give a computational theorem certificate for the four-variable lower bound
posed separately in Section 4 of Thanatipanonda and Wong [1]. The theorem holds
for every positive integer modulus, all four indexed residues, and every prefix
shorter than a complete period. An elementary threshold-count identity reduces
the real floor sum to 64 integer clamps. Sorting the four labels gives a fixed
Presburger contradiction. Its complete generated proof is elaborated in Lean,
including all arithmetic implications, definitional extensions and discharged
hypotheses. The attached mathematical source is the certificate; the following
description does not replace its 12,459 reachable rule nodes with a short hand
proof. Neither solver discovery nor the classical reduction is claimed novel.

## 1. Literal theorem and source scope

For integers m>0, 0<=K<m, and an indexed tuple a=(a1,a2,a3,a4) with
0<=ai<m, write s(T)=sum(i in T) ai and define

    S_m(a,K) = sum(j=0..K) sum(T subset {1,2,3,4})
               (-1)^(4-|T|) floor((j+s(T))/m).

Here floor is the actual real floor, the outer interval includes both endpoints,
and subsets are subsets of the four indices. Repeated entries are allowed and
the empty subset occurs once, with coefficient +1.

**Theorem.** For all these parameters,

    S_m(a,K) >= -3 floor(m/3).                            (1)

The named kernel endpoint is
`Assembly.literal_endpoint : FloorSums.LiteralEndpoint`. The latter type
quantifies natural m,a,K with exactly the above inequalities. Nonnegative
integer parameters and natural parameters identify without restricting this
domain. `FloorSums.actual_source_sum` proves equality to the real-floor expression;
natural division is not an approximation to floor. The theorem includes m=1,
K=0, K=m-1, zero entries, ties, and both nonzero residue classes of m modulo 3.

In [1], Table 1 and the paragraph immediately before Theorem 15, printed p.15,
pose precisely (1). Theorem 15 proves the weaker lower bound
-2 floor(m/2)-floor(m/3), by combining signed two- and three-variable bounds.
The later Conjecture 17 contains other dimensions and assertions about extremal
configurations. This manuscript proves (1), not all of Conjecture 17 or an
extremizer classification. The published version of [1] is dated 23 February
2018; inherited primary-response evidence records arXiv v1 on 10 August 2017
and v2 on 14 February 2018. Those historical versions were not retrieved anew.

## 2. Elementary exact reduction

Put H=K+1, so 1<=H<=m, and C_H(u)=max(0,min(H,u)). For any subset sum s,
0<=s<=4(m-1). If 0<=j<H, then 0<=j+s<5m, and therefore

    floor((j+s)/m) = sum(l=1..4) 1_{lm<=j+s}.

For integers r,s, the number of j in {0,...,H-1} with r<=j+s is
C_H(s+H-r). To see this directly, it is H when r<=s, zero when r>=s+H,
and s+H-r between those two boundaries. Thus

    F(s):=sum(j=0..H-1) floor((j+s)/m)
         =sum(l=1..4) C_H(s+H-lm),                       (2)
    S_m(a,K)=sum(T) (-1)^(4-|T|) sum(l=1..4) C_H(s(T)+H-lm). (3)

These identities count threshold equalities with the correct weak inequality:
C_H(0)=0 and C_H(H)=H. They use all sixteen subsets. They also show that the
empty-subset contribution vanishes on this domain, without removing it from
the source definition or certificate. For comparison, s=qm+r, 0<=r<m, gives
F(s)=Hq+max(0,r+H-m). This one-subset formula is classical: see Proposition 2
of [1] and Theorem 3.1 with its proof in [2]. It is not independently credited
here. At H=m, F(s)=s and the signed fourth difference of this linear expression
is zero. At m=1 every parameter is zero. Neither boundary requires a separate
exception in the formal proof.

A permutation of the four indices bijects their subsets, preserves cardinality,
and preserves each corresponding subset sum. Hence (3) is unchanged by a
permutation, even when values coincide. We may sort to a<=b<=c<=d. This is the
only symmetry reduction used; strict ordering or a generic-position assumption
would lose permitted tuples. The declarations `FloorSums.literal_eq_clamped`,
`FloorSums.endpoint_of_sorted_clamped_bound` and the explicit sixteen-term
expansion in Expansion.lean implement these exact steps.

## 3. The precise integer contradiction

Let t=floor(m/3). Its integral characterization is 3t<=m<=3t+2. The query has
exactly seven integer variables m,H,t,a,b,c,d. It asserts m>=1, 1<=H<=m,
t>=0, the two remainder inequalities, 0<=a,b,c,d<m, a<=b<=c<=d, and the
strict negation of (1), with S replaced by the 64 clamps in (3). Equivalently,
the latter is S<=-3t-1. There are eighteen assertions. The proof uses seventeen:
the unused assertion is m>=3t. Removing it strengthens the contradiction
obligation, so it does not weaken the theorem.

Each clamp is exactly the integer conditional
`if u<0 then 0 else if u>H then H else u` (equivalent boundary choices give
the same value). The packet includes the actual SMT-LIB query, original
certificate, and shared DAG. Query SHA256 is
2864e469f3990f82b453b10649f93d9a177cafd2b9eb5869ae207ad5e3ebc704.
`ClipBridge` proves the actual 64 conditional identities. `SourceBridge`
proves their argument identities and the complete signed `sum_match` equality.
`Assembly.query_of_neg_bound` derives every used assertion from the literal
domain, sorting, and the negated bound, with `sourceEnv` assigning t=m/3.
These bridges are proved, not left as hypotheses to a checker theorem.

## 4. Certificate proof and hypothesis discharge

The original solver output is a 6,626,456-byte proof expression. It is evidence
from which the source certificate was generated, not a trusted oracle. Its
22,672 shared nodes contain 12,459 reachable rule applications. Simultaneous
lexical lets are interpreted in their outer environment, with their body in the
extended environment; this avoids sequential-let substitution or capture.
The reachable rule counts are: rewrite 1466; assertion 17; modus ponens 134;
hypothesis 227; congruence 1503; definition introduction 128; transitivity 955;
definition axiom 243; unit resolution 5540; arithmetic lemma 1329; hypothesis
discharge 644; definition application 128; not-or elimination 145.

The logical justification is induction through this acyclic dependency graph.
Each theorem expresses its conclusion under its explicit residual assumptions.
Assertions come only from the query. Equality transitivity and congruence use
their supplied equalities; propositional rules prove their precise clauses.
An introduced hypothesis remains a binder until a discharge rule proves the
conclusion using a classical contradiction under its negation. In particular,
deleting an assumption in a Python set is not a proof of its discharge: each
of the 644 generated Lean discharge steps supplies an actual proof term.

Arithmetic obligations are exact integral affine implications. Their inherited
generation checks can be understood as rows A*x+c>=0, clearing positive
denominators, integer gcd rounding, and positive linear combinations eliminating
variables until a negative constant row results. If all nonconstant
coefficients have positive gcd g, the integral condition g*B+c>=0 is equivalent
to B+floor(c/g)>=0; strict inequalities are shifted by one before normalization.
Positive combinations preserve truth. Omission of rows can only lose proving
power. Bounded search failure is not evidence of a contradiction. In the
delivered proof all 1,329 resulting arithmetic implications are themselves
Lean theorems; no Python arithmetic verdict is a kernel premise.

There are 128 fresh extension symbols. Each is replaced by an explicit acyclic
integer conditional definition. For example clauses not P or z=u and P or z=v
hold when z is defined as `if P then u else v`. This uniquely extends any
assignment to the seven original integers. `Assembly.Vars` has only the seven
original fields, not arbitrary additional extension values. The semantic
translation contains 10,188 explicitly typed integer/Prop definitions; its
576 integer conditionals include the 128 extension definitions. All mathematical
semantics and proof terms are supplied as source, including the 45 split actual
origins for the historical Dag168 block. Dag168 itself is an import wrapper.

The root theorem is `Assembly.n22671 (v : Vars) (q : Query v) : e7489 v`,
where e7489 is definitionally False. It has no residual hypothesis binder.
Consequently a counterexample to (1), after sorting and (2), supplies `q` and
contradicts this theorem. This proves `sorted_clamped_bound`; the permutation
and literal-floor identities then give the named endpoint. This is a universal
certificate proof, not a sweep of finitely many moduli. The extensive source
DAG is essential to this computational proof; no concise analytic replacement
for it is asserted.

## 5. Certification, reproducibility and trust

The independent r4 review reports a fresh strict serial replay: 437 mathematical
modules and 22 audit partitions, or 459 Lean invocations. It inventories 35,654
declarations in 436 actual mathematical origins, including private/generated
declarations and instances. The sole empty origin is Dag168. All declarations
are safe and nonpartial; the only transitive axioms are propext,
Classical.choice and Quot.sound. The name-set SHA256 is
7abfdce5f2b7e1d6ba7df2fc0de7ee9a96faa975f113e04b512bfd42008a668b.
This manuscript lane's separate replay receipt and verification report record
its own execution, rather than substituting the predecessor receipt for it.

The frozen input archive hash is
17ba800adb3154f5c3929ef076c47b9d1f0adaace1576793faa4154ff19be13f.
All mathematical source bytes are preserved. The accompanying deterministic
packet adds documentation, primary evidence, provenance bindings, replay and
full-audit tooling. It includes no owned compiled objects. A clean replay
requires the specified external Lean 4.34.1 executable (SHA256
e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550),
mathlib revision d13f23b723b8a846827a245b89c10fc7d3f11612, and the nine actual
package revisions in pins.json, with their already built external libraries.
It is a source distribution, not a bundled toolchain or a complete recursively
copied research history. Absolute external paths remain disclosed in README.
Kernel checking, the pinned library environment, source interpretation and the
host execution environment delimit the certification claim. SHA256 binds bytes;
it is not a mathematical proof or an independent priority determination.

## 6. Related work and bounded provenance

This lane inspected the frozen primary body of [1], introduction and Section 4
through Theorem 15 and the following conjectures, and the actual Theorem 3.1
formula and proof of [2]. Other body-read claims belong to the named inherited
reviews, not to an independent rereading here. The source/prior review read the
whole Theorem 9 proof of Onphaeng and Pongsriiam (2017), the three-page Tverberg
(2012) paper, [2], a 2021 univariate floor-sum paper, and specified portions of
the 2022 absolute-value inclusion-exclusion paper. Its exactcoverage.json gives
URLs, hashes, page limits and chronology. Older signed block bounds do not
reach (1); bounds for individual absolute-value differences do not by themselves
bound the required joint difference. No complete published subsumer was found
in those inspected bodies, which is a bounded observation rather than a proof
of absence. The classical short-proof/routine-corollary question remains for
root adjudication; certificate size and formalization do not establish novelty.

Current public-registry proof-body clearance remains unavailable. Carlitz 1959
and 1960, Jacobsthal 1957, Grimson 1974, and four metadata-only citing bodies
remain uncleared. Denied GitHub API/raw/codeload/diff/patch, ScienceDirect and
Google challenge routes were not retried; inaccessible historical intervals
remain parked. No network retrieval was performed in this lane. The packet
preserves predecessor failure reports, immutable reference bindings and the
local PDF-marker failure. Neither worldwide priority, campaign acceptance nor
publication follows from the present theorem certificate. Root's own replay,
prior adjudication, final review and acceptance remain pending.

## Bibliography (primary bodies inspected in this lane)

[1] T. Thanatipanonda and E. Wong, *Curious Bounds for Floor Function Sums*,
Journal of Integer Sequences 21 (2018), Article 18.1.8.
https://cs.uwaterloo.ca/journals/JIS/VOL21/Wong/wong7.pdf .
Frozen PDF SHA256: 345c2cf3893d3c2c0371e0b2053bf02c6f04469243f7c1ca33e1d0681fc15d7d.

[2] S. Aursukaree, T. Khemaratchatakumthorn and P. Pongsriiam,
*Generalizations of Hermite's Identity and Applications*, Fibonacci Quarterly
57(2) (May 2019), 126-133, Theorem 3.1 and proof, p.128.
https://www.fq.math.ca/Papers/57-2/pongsriiam02072019.pdf .
Frozen PDF SHA256: 29292c0a4c0fb29c80d855fe8ec48cb6db4cf4603c0e936cbfd608f1435c005a.

PDF status: NOTAUTHORED. QA_NOTPERFORMED. The mandatory unmodified marker could
not start under the unchanged helper memory cap, including a supported Node
configuration with smaller heaps and jitless execution. This source manuscript
is provided independently of a PDF; no PDF authoring or visual QA is claimed.
