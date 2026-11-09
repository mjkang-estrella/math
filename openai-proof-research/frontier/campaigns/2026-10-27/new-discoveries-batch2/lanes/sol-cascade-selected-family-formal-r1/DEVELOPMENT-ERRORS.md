# Development errors and limits

Every development compile used the frozen runner serially, autoImplicit=false,
warningAsError=true, a180-second wall deadline and sampled RSS ceiling3GiB.
No timeout or RSS ceiling breach occurred in this lane; no limits were increased.
No unbounded proof-search tactic or heartbeat override was introduced.

The first SelectedFamily attempts failed on: simplification under List.ofFn
composition; fixed-chunk take equalities; a redundant tactic after simp; prefix
witness inference; use of the wrong direction of List.drop_append_of_le_length;
reversed drop_drop addition order; getElem proof transport while unfolding the
anchor; unnormalized append lengths; an implicit alternating-prefix length;
and an unused parameter warning. Corrected with explicit prefix/getElem lemmas,
length equalities, list induction, and explicit index arguments. The final family
compiled before integration.

SelectedCounting initially failed at the literal Eq.(5) length index: simplifier
rewrites inside List.ofFn inserted Fin.cast terms while retaining the original
finite sum index. Several direct simp-only variants failed. The proved general
sum_fin_cast lemma resolves the finite-function reindexing by equality elimination;
its first invocation left the equality proof implicit, then an explicit omega
proof closed that final goal. No source semantics or summation index was changed.

The first audit inventory regex missed six declarations with same-line simp
attributes. The final generator handles them and explicitly includes eight
structure field projections; all152 entries were replayed and inspected.

Early development verifier calls overwrote their logs and receipt.json; their
exact full stdout is retained only in the task conversation, not reconstructed
as a purported original file. From the later verifier revision, overwritten
module logs are copied to timestamped logs in verification/. Some failed full
outputs are thus available, and this document records the earlier failures
candidly. The final isolated replay is complete and has no failed module.
A preliminary successful replay with the smaller audit inventory was replaced
by the final fresh replay after correcting the inventory; proof source bytes did
not change between those replays.
