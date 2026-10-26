# Completed: twenty verified outcomes

The user-requested campaign is complete: **20/20 distinct MathDB source-question outcomes**.
Authoritative records: `ledger.json`, `README.md`, `collection-verification.json`, and
`delivery-verification.json`. The deliverable is
`openai-proof-research/output/release/twenty-proofs-v1.zip`.

Each outcome has a full Lean proof of the exact claimed outcome, a paper, source
provenance, independent review, visual PDF QA, and an extracted-source rebuild.
The collection includes known-result formalizations, counterexamples, and explicit
literal-source corrections. It is not a claim of twenty new discoveries.
The two arithmetic questions share a joint paper and module. Bernstein's related
monotonicity/minimum questions and the duplicate signed-set question add no counts.

All assigned T3 workers and reviewers completed. No active proof work remains.
The final collection contains twenty nested packages; all inner and outer manifests
and hashes passed independent readback. The collector now requires review/replay
acceptance and source/hash binding, including an explicit original-premagic adapter.
Nine malformed acceptance-record regressions were rejected.

Reproduction uses Lean4.34.1 and the exact mathlib/dependency pins in each package.
The standard packages include `verify_outcome.py`; premagic has its original
`formal/rebuild.py` and verification scripts. Source-body retrieval and precompiled
pinned dependencies are external requirements, transparently documented.

Only the campaign's own exact files and release artifacts were committed. Existing
unrelated repository work was preserved. No external posting, publication, push,
or message to another person was performed.
