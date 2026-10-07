# W007: conventional BSGS modular recovery and executable baseline

Date: 2026-10-07. Status: modular arithmetic and executable generic solver
independently reviewed and accepted. No new speed claim.

Question: can the conventional baby/giant method be proved correct on every
scalar using only W005's concrete-refinable orbit arithmetic, including
composite/order-one groups and m>q duplicate baby entries? Falsifier: a matching
baby yields the wrong canonical scalar, quotient/remainder block witness falls
out of range, or the actual solver fails to find the witness.

Coordinator's `Research/BSGSArithmetic.lean` defines scalar negStride=(q-m%q)%q
and blockCount=(q-1)/m+1. Four generic theorems:

- `stride_cancels`: (m+negStride)%q=0 when q>0;
- `recover`: a residue match at giant i/baby j implies (i*m+j)%q=d for d<q;
- `quotient_in_range`: d/m<blockCount; this isolated lemma even allows m=0
  under Lean's natural division semantics, but algorithms require m>0;
- `complete_digits`: positive m gives the matching witness i=d/m,j=d%m.

These are integer statements, not an assumed oracle solver, EC result, lookup
implementation or cost bound. No primality or coprimality hypothesis is used.
`timeout 60 ./scripts/lake.sh env lean Research/BSGSArithmetic.lean` passed.
First attempt failed because rewriting modular addition left an inner modulus;
an explicit equality with the unmodded cancelling sum fixed the proof.
All four supporting theorems were added to Audit.lean; full `./scripts/check.sh`
passed97 audits/33 build jobs (15 screened files). Native Astra independently
passed the frozen arithmetic source: all four lemmas compiled, with no omitted
prime/gcd assumption; arbitrary matching baby indices and q=1 are covered.

Sol `/root/small_curve` owned only new `Research/BSGS.lean`: implement actual
baby construction, linear list lookup, giant updates and modular return from
an input point. Prove correctness for every `P.publicKey d`, every m>0, using
the reviewed OrbitArithmetic laws and these arithmetic lemmas. Decidable point
equality is explicit. Lookup must be implemented and proved, not assumed.
Boundary instances should include m=1,3,7,8 on SmallCurve and order one through
general results. No writes to shared definitions/audit/checkpoint by delegate.

This stage intentionally keeps linear lookup to isolate functional correctness.
W004's negative cost finding applies: it must not be advertised as total
square-root runtime. A sorted-table implementation with a lawful comparator,
explicit access/storage semantics and proved costs remains required for the
planned efficient reference baseline. If only wrapper counts are instrumented,
all W005 generator-setup exclusions must remain explicit. No Machine goal,
randomized semantics, hardware estimate or cryptographic family is changed.

## Implementation and independent verification

The frozen implementation contains actual recursive linear lookup with soundness
and completeness, baby membership, giant-update invariants and bounded search.
`solve` constructs the baby list afresh, negates its final mG, searches from the
target, and returns the matching index modulo q. It accepts no secret scalar
or inverse table. Generic `solve_correct` handles every positive m and every
orbit scalar. `order_one_correct` covers q=1. `smallCurve_edges` kernel-checks
all seven scalars at m=1,3,7,8; executable evaluation returned some 0 through
some 6 in each case. There are nine public supporting theorems, all audited.

Author command: `timeout 60 ./scripts/lake.sh env lean Research/BSGS.lean`.
Two initial attempts failed on let reduction and 0+fuel elaboration; corrected
before source freeze. The final compile and all nine author axiom checks passed.

Independent native Astra `/root/encoding_review` recompiled the frozen file,
then checked its source via Lean stdin with all nine axiom reports. PASS, no
blocking issue or hidden prerequisite. Dependencies were limited to propext,
Classical.choice and Quot.sound. The reviewer specifically checked that duplicate
babies may return any matching index and modular recovery still gives d; no
primality or coprimality hypothesis is needed. It confirmed actual coordinate
refinement, no secret input, orbit-only scope and unpriced generator evaluation.
The failure branch can compute an unused final giant; no total work theorem
is inferred from the source structure.

Coordinator imported the module and added all nine declarations to Audit.lean.
The integrated `./scripts/check.sh` result is recorded in research/STATE.md.
This is a correctness baseline; sorted lookup, complete cost accounting and
refinement to a frozen machine goal remain open.
