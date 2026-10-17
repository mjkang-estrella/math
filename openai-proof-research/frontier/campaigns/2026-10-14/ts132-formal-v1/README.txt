TS132 scoped Lean support — implementation, not independent formal review

Author: Myeongjin Kang. No affiliation.
Original prose CC BY4.0; original code MIT. Third-party inputs retain their rights.

The unchanged full target is the every-C transitive ordinary-sensitivity separation
and the fixed-alpha>2 sequence with diverging zero-input block sensitivity.
This package does NOT formalize that full theorem and does not change the count.
The implementer authored the contribution gate but did not author TS132.

What is compiled
----------------
22 supporting theorems, 6 definitions and 1 named instance (29 public declarations).
13 control theorems and 1 definition (14 public declarations).
All 43 exact types and transitive axiom reports are printed. The only allowed
axioms are propext, Classical.choice and Quot.sound. No new axiom, sorry, admit,
unsafe code or native_decide is used in the support or controls.

1. Actual recursive Word, first-difference edgeLabel, and HeadConstant definitions.
   Finite tournament indegree counting, fiber counting, fiber inheritance,
   quotient incoming-label uniqueness and induction prove card<=3^h. For h=4,
   card<82. The base relation on an additive group is assumed irreflexive and
   total on distinct elements; it is not identified with Paley squares in Lean.
2. Affine difference scaling and preservation of an explicitly specified first
   differing coordinate. Actual maps on (iota->K) x H for H a subgroup of K units
   have injectivity, transitivity, composition, identity and a left inverse.
   This function-vector model is separate from Word; their identification and
   actual Paley gate-label covariance remain in the human proof.
3. Finite-depth bounds for real sequences satisfying explicit coupled scalar
   recurrences, initial upper bounds and epsilon*3^(d+1)<=2. Side normalization
   lemmas assume the scalar inequalities. Strict seed support includes
   (44*M^21)^2 < M^2*k^20 from M>0 and 3*M^2<=2*k.

Not formalized
--------------
The Paley-square orientation and its number theory; the Word/vector model
identification; nested Boolean predicates, raw-bit automorphism group, actual
ordinary/joint sensitivity profiles and their recurrence derivation; prime
existence and integer rounding; zero-input blocks; OR balancing; Boolean
composition; the every-C asymptotic or logarithmic fixed-alpha conclusion.
See coverage.json for exact contracts and all theorem names. No scalar hypothesis
is presented as already discharged by the Lean Boolean construction.

Reproduction
------------
Pinned Lean 4.34.1 (commit5045d0056413266e57c625dcd7c365b10e377c52) and mathlib
d13f23b723b8a846827a245b89c10fc7d3f11612. The default tool/cache paths are in
rebuild.py. --lean and --cache accept an equivalent pinned installation.

  python3 -B rebuild.py --output .replays/independent-build
  python3 -B mutations.py --output .replays/independent-mutations
  python3 -B verify.py --anchor EXTERNALLY_SUPPLIED_OUTPUT_MANIFEST_SHA256

Each build copies current task sources into a fresh temporary directory inside
this package, compiles TSLocal and Controls, and then prints types and axioms.
No existing task .olean is used. Dependency objects are reused read-only from
the established cache. Compiler identity, dependency revisions, current-source
hashes and log hashes are recorded. The rebuild also requires tracked dependency
trees clean. These checks do not constitute a full independent rebuild/audit of
Lean, mathlib or every cached object; those remain explicit trust boundaries.

The read-only offline verifier checks the external output anchor, exact sealed
membership, copied inputs against three externally anchored manifests, source
Git blobs, declaration coverage, build/source/log identity, axiom reports,
six genuine proof-goal rejections and the actual zero-exit printed-failure
wrapper control. --check-inputs additionally compares the immutable originals
at their relative repository paths. This option is unnecessary for standalone
identity verification of the retained snapshots.

Only .replays/ is an expressly unsealed future replay area. It is excluded from
the sealed inventory; its contents supply no original verification evidence.
Symlinks are rejected everywhere. Other extra files and even empty directories
cause rejection. The verifier itself writes nothing and performs no network call.

Validation and provenance
-------------------------
logs/fresh-build records the clean current-source build. Concrete Lean controls
include the three-cycle and a three-element head-constant set, h=0, zero scalar
collapse, row-only label preservation, zero/positive epsilon, actual seed
parameters, and failure of the depth18 threshold. Six source mutants test a
false tournament bound2, zero-scalar equality preservation, a false strict81
bound, reversed affine differences, a too-small profile envelope and a depth18
strict seed. Each fails at a proof goal, not parsing/import resolution.

One initially proposed two-power mutation was discarded because its unchanged
proof terms produced type mismatches; it is not among the accepted six controls.
The source theorem contracts were not changed for that diagnostic correction.
checked_run.py rejects both nonzero exits and printed error/failure markers;
logs/runner-control demonstrates rejection when the child prints SOME FAIL yet
exits zero.

The source theorem truth is stipulated at the campaign pin. No upstream truth
audit, independent formal PASS, full-theorem claim, shared edit, git operation,
public upload or acceptance was performed. Helper ancestry and exact copied
hashes are in provenance.json. Primary reading and full-scope anchors are in
source-contracts.json and the retained review inputs.
