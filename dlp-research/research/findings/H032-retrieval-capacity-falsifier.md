# H032 R1: retain the construction descriptors

Status: root paper counter-comparison independently ACCEPTED by native Astra
`/root/h007_additive_relations`; native Sol proposer `/root/h010_early_dependencies`
agrees and withdraws the single-batch capacity rationale. No numerical experiment,
source implementation or Lean claim. Verified improvement NONE.

This addresses the exact SINGLE frozen batch and hard construction peak in
[H032-memory-retrieval-cards.md](H032-memory-retrieval-cards.md), not all static
retrieval structures. R1 already constructs a sorted descriptor table with w
entries: three hash-cell indices, a seed and a tag. Its size is

    E = w(3v+s+t),

with u=ceil(log2(w+1)), v=ceil(log2(m+1)). The admitted literal builder reserves
E+P+max(V+Q,m(s+t)), P=w(u+v), plus all other solver state.

## Descriptor baseline

Keep the existing sorted descriptor table instead of peeling it into a retrieval
map. On a query, compute the same signature and tag, binary-search the signature,
check the tag and seed range, then perform exactly the same bounded replay,
endpoint-equality check, scalar recovery and final verification. O is dispatched
as in the candidate. No stored full endpoint coordinates are required.

Use the SAME signature convention on both sides. For XOR retrieval, a sorted
multiset of its three cell indices preserves the XOR. Repeated indices must not
silently become a set; alternatively retain the ordered-triple convention used
by the builder. All candidate uniqueness/deduplication checks remain required.

For w≥2, iterative binary-search index scratch fits within the candidate's
P=w(u+v) peel-stack reservation: a successful peel has m≥w, hence v≥u. The
w=1 case is direct comparison. Query-coordinate, hash and replay buffers are
common and charged on both sides. Thus every endpoint batch this R1 builder can
construct under its hard peak can also be held by this descriptor baseline.
The candidate's smaller FINAL array does not produce extra endpoint capacity
under that peak constraint.

## Pointwise acceptance, not a random-hash argument

Condition on one fixed archive and one hash choice with a successfully correct
R1 retrieval map and unique signatures. For any fixed query, descriptor signature
and tag acceptance identifies a stored payload. Correct retrieval maps that same
signature to that exact seed/tag payload. Therefore descriptor acceptance implies
retrieval acceptance with the same seed and the same range checks. Both replay
and verify identically. All genuine archive members are recognized by both;
descriptor-triggered false replays form a subset of retrieval-triggered false
replays for these fixed queries. No independence or2^{-t} model is used here.

This is NOT a coupling across different construction hashes. A descriptor baseline
may stop at its first valid table while R1 continues peeling/rehashing. Their
true membership remains correct, but false-replay subset inclusion across the
different hashes is not asserted. A comparator that follows R1's entire hash-
selection procedure preserves the coupling and must pay that same procedure.
Avoid silently combining the cheaper first-hash construction with a later-hash
pointwise guarantee. Pure descriptor lookup needs no peel; its complete cost is
a separate comparison if it selects a different hash.

For a fixed logical query stream, both methods detect the first useful genuine
archive hit at the same query. Different processing times or a wall-clock cap can
change finite outcomes. Query generation must not silently depend on elapsed
time or lookup results beyond verified recovery. No universal runtime dominance
or stochastic stopping equivalence is inferred from the set-containment claim.

## Disposition and remaining possibility

The stated single-batch endpoint-capacity/DP-tail rationale is falsified against
this competent baseline. The original proposer explicitly accepts that result.
There is no reason to build a solver to test that rationale.

Retrieval can still trade cheaper lookup for peeling/build/replay overhead versus
binary-search comparisons. That is a new explicit LOOKUP-COST hypothesis, not
the original capacity gain. It would require a credible matched full-work premise
before any benchmark. No such premise is supplied here. Resident-memory-only
budgets, multiple resident archives, or reduced-scratch construction need separate
contracts; they are neither evaluated nor ruled out by this finding.

Review record: root proposed the descriptor comparator; Astra supplied the
multiset, failed-build coupling and logical-query-stream qualifications; Sol
withdrew the original capacity rationale. All roles read-only/no experiments,
imports, edits or children. Root alone integrates. Validation recorded in STATE.
