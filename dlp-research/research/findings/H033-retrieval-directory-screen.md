# H033 stronger descriptor lookup comparator

Status: root proposal, independent native Astra mathematical review COMPLETED.
Candidate-specific paper comparator; no numerical run, implementation, Lean
claim or supported ECDLP improvement. Related findings: H032-retrieval-capacity-
falsifier.md and H032-memory-retrieval-cards.md. Remaining lookup-cost analysis
by Factory Fable is separately active and has not yet supplied its conclusion.

## Construction and exact search

Keep R1's sorted descriptor table E=w(3v+s+t) with unique signatures. Preserve
its actual ordered-triple or sorted-multiset convention. For first signature
component x in [0,m), define b(x)=floor(wx/m) in [0,w). Store w+1 boundaries:
D[j] is the first record with bucket at least j; D[w]=w. Since b is monotone,
one sorted pass fills the directory in O(w) bounded-integer operations/writes.
Multiplication/division and their operand/intermediate widths are paid, not
unit-cost consequences of the number of entries. Product wx needs up to u+v
bits with the previously defined u=ceil(log2(w+1)), v=ceil(log2(m+1)).

A query reads D[b(x)] and D[b(x)+1], then searches just that interval for its
exact FULL signature. Apply the same tag/range/replay/endpoint/scalar checks.
Empty buckets return no match. The directory costs (w+1)u bits. Successful
literal peeling has m>=w, hence v>=u and

    (w+1)u <= w(u+v) = P.

Thus the directory ARRAY fits inside the candidate's removed peel stack.
This is not a license to omit scratch: construction and query need index,
arithmetic, addressing and comparison storage. The remaining removed reservation
max(V+Q,m(s+t)) is available for it. A concrete register implementation must
show its peak fits before claiming full bit-level memory dominance. No complete
machine refinement is asserted here. Alternatively a paid bit-prefix partition
with B<=w buckets avoids division, at the cost of its own occupancy distribution.
Small w may simply use the already admitted direct/binary descriptor baseline.

## Lookup bound and counterexample to automatic balance

If bucket j has n_j entries, balanced three-way binary search requires at most
ceil(log2(n_j+1)) signature comparisons. An implementation using lower_bound
then equality may need one additional comparison. These are comparisons, not
field-operation or bit-cost totals. Over a declared query distribution p_j the
bound weights those bucket costs by p_j; no p_j is inferred from peeling.

Counterexample supplied by the independent reviewer, checked by root: choose
m=w+2 and sorted triples (0,i,i+1), i=1,...,w. These are distinct valid indices;
successively peel from the end of the path. Every first component is zero,
so all w records occupy one bucket. A successful peel therefore does not imply
balanced buckets or constant expected search. These are abstract signatures,
not a claim that a specific EC hash implementation produces that archive.

The directory changes only how exact search is performed. With the same archive,
chosen hash, signature convention and checks, the descriptor acceptance set and
its replay containment in retrieval are unchanged. Different rehash choices
retain all qualifications in H032. No elapsed-time stopping equivalence follows.

## Decision

Global log(w) comparisons are not a compulsory comparator charge: a paid
directory can reduce them when the ACTUAL occupancy/query distribution supports
it. Neither a uniform distribution nor a complete lookup-speed advantage for
either arm is established. R1 must compare against this and other competent
storage layouts, with construction/scratch/replay costs and solver-derived query
counts. This strengthens the paper falsifier; it does not supply a faster DLP
algorithm or justify a data-structure benchmark divorced from the solver.

Primary source re-read by root: Dietzfelbinger–Pagh, §§1.1–1.3,
https://www.rasmuspagh.net/papers/bloomier.pdf . Its retrieval model permits
arbitrary nonmember payloads and explicitly states word/RAM/hash assumptions;
those results do not establish an ECDLP full-work advantage. The directory
argument and counterexample above are direct elementary reasoning, not attributed
as new discoveries or as the paper's theorem. No hardware prices are assumed.

Review: native `/root/h007_additive_relations` checked the directory inequality,
search/replay invariants and counterexample. Root explicitly retains unresolved
concrete scratch accounting rather than claiming an implemented peak bound.
No edits/runs/imports/children by reviewer. Root alone integrates. No Lean
declaration changed; existing check suite remains the prior recorded validation.
