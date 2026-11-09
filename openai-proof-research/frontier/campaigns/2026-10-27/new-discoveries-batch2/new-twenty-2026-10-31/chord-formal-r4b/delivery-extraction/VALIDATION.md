# Validation receipts

PARTIAL, NOT ACCEPTED. No original target Prop closed.

All 117 modules (110 inherited, 7 new including the audit) rebuilt from a fresh source-only extraction and passed leanchecker with explicit module arguments. All 110 inherited SHA-256 hashes are unchanged. The final import-closure audit inventories and audits exactly 225465 declarations, with both set inclusions checked in Lean. LOCAL metadata: {"declarations": 6585, "unsafe": 0, "partial": 0, "axiom": 0, "unsafe_rec": 0, "implemented_by": 0, "extern": 0, "unapproved_transitive_axioms": 0}. Upstream metadata: {"declarations": 218880, "unsafe": 633, "partial": 2636, "axiom": 15, "unsafe_rec": 2604, "implemented_by": 300, "extern": 761, "unapproved_transitive_axioms": 198}. Upstream runtime metadata is reported separately and is not attributed to LOCAL proofs. All LOCAL transitive axioms are in the three permitted names.

Peak sampled summed session RSS: 3014784 KiB. Strict serial calls use the required CPU, wall, affinity, RSS and allocator limits. Full uniquely named call logs are retained under logs/ and fresh-extraction/logs/. Fresh replay progress is in logs/fresh-replay.log. No background job remains after handback.

Independent representative-state regression checks every assignment at n=3 through 7 and every two-end extension at n=3 through 6: no violations. The inherited independent small-table regression checks all labelled matchings and side assignments through n=5 and reproduces range-{1,2} class counts 0,0,1,4,1. Negative controls reject the wrong Euler offset, omission of the empty circle, uniqueness at n=4 and the adjacent-pair representative. These computations do not discharge a general Prop.
