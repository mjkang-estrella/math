# W002 Lens B — Coordinator intake

2026-10-08. **SUBMISSION READ; new deductions UNACCEPTED pending review.**
Verified COMPLETE classical factoring complexity improvement: **NONE**.

The constructive task is completed with no pending runs. The coordinator read
all 495 report lines, the complete input inventory and retrieval records.
All 22 frozen inputs, 42 delivery entries and 10 primary-source records verify.
Current STATE and W001 synthesis differ from their saved snapshots; those
snapshots verify. The report is preserved unchanged as
W002-adaptive-submitted-draft.md. Both originals hash:
9d91b8b17dfeea5c36785a5c9a82512798b041fb230c67c8383c43b8bc588a80.

## Provisional reading

The generator is an explicitly capped multiplier-one continued-fraction
recurrence with modular numerators. It obtains a composite coprime base using
gcd and exact division, with a decreasing potential and a deliberately
conservative cubic cost. Removing square base columns while retaining their
roots is claimed to preserve exactly the signed integer-square kernel.
The extractor tests every kernel basis vector and uses a homomorphism into
square roots of one modulo global sign to certify finite-list failure.

The symbolic s^2+1 family has d_i=1 and X_i=s^(i+1) modulo N. Its arbitrarily
large square kernel maps only to global signs, so all extraction attempts fail.
The explicit s=50t+2 family survives the stated even/perfect-power checks,
and the CRT extension concerns only a fixed finite prime screen. The parent
traced the recurrence and signed-overlap identity without finding an immediate
contradiction. This is not acceptance or a completed independent audit.

The declared L_N[1/2,3] upper envelope is a finite-trial cost only. Repeating
the deterministic trial gives identical data. The generator and coprime
processing are known CFRAC and known refinement mechanisms; no improved
factoring bound is claimed.

## Questions requiring independent resolution

1. Validate exact divisions, complete-quotient invariants, modular numerator
   identities, O(n)-bit state, ordering, early gcds and all preprocessing
   branches. Check H's construction and the natural-log L-constant conversion.
2. Check gcd refinement with coincident/dividing bases, exponent updates,
   termination, pairwise coprimality, square/nonsquare columns, exact sign
   handling and full prime-square-kernel equivalence without a factoring oracle.
3. Prove the map into roots modulo global sign, basis sufficiency and the
   finite-list certificate for arbitrary odd continuing N, including repeated
   prime powers. Check whether an unquotiented character is ever implicitly
   assumed, and charge every root, modular power and gcd.
4. Validate the for-every-cap failure, the infinite non-perfect-power family,
   and the fixed-prime-screen CRT extension. Preserve the restriction: neither
   balanced semiprimes nor growing input-dependent cutoffs are covered.
5. Audit the sequential-tape cost and memory claims. Pair scans, decomposition
   merging, dense elimination/provenance, kernel storage and testing all basis
   vectors require explicit implementations at the stated envelope.
6. Check the H026 escape wording carefully. Input-dependent labels or varying
   integers alone do not prove noncontainment in a fixed universe. Determine
   exactly which H026 premise fails; supply a concrete arithmetic support
   argument if needed, or narrow the report's claim. Escaping that particular
   counting proof must not be confused with obtaining useful relations.
7. Verify the primary prior-art comparisons, including the independent-uniform
   square-subset surrogate versus the actual deterministic CFRAC stream.
   Keep blocked source access and uninspected proofs explicit. No numerical
   examples or heuristic substitutions should replace these checks.

There are no earlier review rounds or proposer responses. No report edits,
experiment, implementation or Lean work precede review. The ECM constructor
has also completed but its result is not a dependency of this review; do not
read sibling W002 drafts or duplicate their tasks.

[Submission](W002-adaptive-relation-universe.md),
[preserved original](W002-adaptive-submitted-draft.md),
[input inventory](W002-adaptive-inputs.json),
[retrieval record](W002-adaptive-retrieval.json).
