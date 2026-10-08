# W008: lawful coordinate keys and counted indexed lookup

Date: 2026-10-07. Status: design and coordinate-key implementation independently
accepted; indexed-search implementation in progress. Previous milestone `9667d72`.

## Purpose and falsifiers

W007 proves functional BSGS correctness but its linear lookup defeats a claim
of square-root total work. The next layer must search an actual indexed array,
prove correctness including absence/duplicates, and count executed comparisons.
It will not price preprocessing or establish total runtime by itself.
Falsifiers: a wrong/missed key, treating fuel exhaustion as absence, a hidden
linear traversal/copy during lookup, a count detached from executed tests, or
a key deriving from the secret rather than conventional coordinates.

## Sol proposal (read-only round)

Use a separate `PointKey P` with executable key : P.Point -> Nat and equality
reflection on orbit points. Nat's ordinary order supplies total comparison.
Concrete SmallCurve key is 0 at infinity, 1+5*x+y at affine coordinates. Prove
key<26 and injectivity directly; no scalar lookup. This is an internal key,
not a change to the frozen seven-bit public encoding. The abstract contract
alone cannot prohibit a secret-revealing key: concrete implementations still
require source review, as W002 demonstrates.

Entries cache key and forward baby index; duplicates are allowed and payload
indices do not break key ties. Implement half-open interval binary search over
Array Entry. At lo<hi, read entries[lo+(hi-lo)/2], test equality, and test strict
order only on failure. Recurse into [mid+1,hi) or [lo,mid). No runtime toList,
linked-list indexing, slicing or subarray copying. Proof-only list views are
allowed. Nat arithmetic and physical array access are not constant-time claims.

Required claims:

- Soundness: returned entry exists at an actual index with the target key.
- Completeness and absence on an indexed nondecreasing array.
- Any matching duplicate payload is acceptable.
- Equality calls = probes; ordering calls <= probes; success has one fewer
  ordering call than probes. Empty intervals execute zero of these calls.
- For length n>0, probes <= Nat.log2 n+1, via n<2^k implying probes<=k.
- If recursion uses fuel, prove the public wrapper cannot exhaust it;
  exhausted and absent must not be confused in the correctness argument.

These counters exclude key construction, baby generation, sorting, conversion,
allocation, copying, scalar arithmetic, comparator bit work, reference counting,
and physical access latency. Sorting and full primitive/storage accounting
remain required for any whole-solver cost theorem. No RAM model is adopted.

## Existing APIs inspected

Pinned Lean 4.34.1 sources: Init/Data/Array/BinSearch.lean implements inclusive
binary search with actual indexed reads and one/two strict-order tests. Sol
found no correctness/count theorem in inspected Init/Std sources; coordinator
read its implementation. We will not infer counts for our different equality-
then-order loop from that implementation. Init/Data/Array/Sort/Lemmas.lean
provides mergeSort permutation, membership, size and pairwise-sortedness proofs.
Nat.log2_lt supports the power-of-two bound; indexed sortedness can be related
to List.pairwise_iff_getElem and Array.getElem_toList in proofs.

A later correctness-only adapter can map generated babies to keys, convert to
Array and use mergeSort, preserving entries via permutation/membership proofs.
It cannot inherit a two-buffer space bound or free sorting. Full sorted-BSGS
integration is a subsequent stage, not established by a query theorem.

## Ownership and review

Proposer: native Sol `/root/small_curve`, no files changed or compile claims.
Independent reviewer: native Astra `/root/encoding_review`, read-only new round
with the original proposal and earlier W005 cost/key objections supplied.
Coordinator owns this record, checkpoint and eventual shared integration.

## Independent design decision

Native Astra approved the bounded stage, with explicit corrections:
maintain lo<=hi<=size; distinguish array location from scalar payload in soundness;
cache a midpoint entry once; completeness/absence need sortedness and adequate
fuel while wrapper non-exhaustion must hold independently of sortedness. Any
matching duplicate is valid. Sorting by key is a total preorder on entries,
not antisymmetric when payloads differ. An unsuccessful completed search should
have orderingCalls=probes; successful searches must have positive probes.
No total-cost model, free preprocessing or two-buffer memory claim was approved.

Coordinator assigned Sol ONLY Research/IndexedLookup.lean, independent of the
key module. Coordinator owns ONLY Research/PointKey.lean plus shared integration
and records. No delegate writes to audit/checkpoint/imports or commits.

## Coordinate-key implementation

Coordinator implemented PointKey contract and direct coordinate packing for all
RawPoint values (not merely the seven valid curve points). Arithmetic proofs
establish injectivity and key<26; subtype reflection and orbit residue equality
follow. A five-bit value bound is stated explicitly without a storage-layout,
serialization or bit-operation claim. The public tape encoding is unchanged.

Command: `timeout 60 ./scripts/lake.sh env lean Research/PointKey.lean`.
Initial attempt failed to close an impossible zero-equals-positive branch with
simp alone; adding omega fixed it. Unused implicit binder warnings were removed
by making the orbit arguments explicit. Final standalone compile passed cleanly.
All six public claims await independent implementation review by native Astra;
indexed search is still under implementation by Sol.

Independent PointKey implementation review: native Astra PASS, clean bounded
compile; all six axiom reports use only propext and Quot.sound. No secret access,
encoding change or cost overclaim found. Review did not inspect unstable lookup.

A separate whole-solver cost-design review was delegated to Factory Fable 5.1,
request `ecdloop-w4-cost-ledger-fable-20261007-r1`, task ID
`node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-w4-cost-ledger-fable-20261007-r1`.
Its brief includes previous W005 objections, current exclusions, explicit word
width/primitive/state/ownership/setup obligations and lower-bound limitations.
This is future design work, not permission to reinterpret existing counters.
Initial delegation was rejected because role was not a schema enum; retry with
role=design and the same stable request ID succeeded. No duplicate child started.

Coordinator integrated PointKey and all six public audits. Full command
`./scripts/check.sh > /tmp/ecdloop-w008-key-check.log` passed 112 audited
declarations and the executable smoke check. IndexedLookup is unimported and
uncommitted while its author finishes correctness/probe proofs; this validation
does not certify that unfinished module. The key-only checkpoint includes the
accepted design and retained live task IDs, not an efficient-solver claim.

## Frozen indexed-search implementation and review

Sol completed Research/IndexedLookup.lean, 31 public theorems. Actual midpoint
entries are cached and directly indexed; sortedness is a nondecreasing key
preorder. The public lookup wrapper uses zero fuel for empty arrays, otherwise
log2(size)+1. Generic proofs distinguish array location from payload, establish
soundness/completeness/absence, and prove non-exhaustion independently of
sortedness. Power-of-two probe bounds hold even for arbitrary supplied fuel.
Executed equality/order counters satisfy the specified relations; their sum
is at most twice the wrapper fuel. No whole-solver, allocation or latency bound.

Author bounded compile and all 31 axiom checks passed. Three earlier attempts
failed on parser/proof elaboration issues (including if-distribution and an
unavailable tactic); corrected before freeze, no timeout or counterexample.
Kernel boundary checks cover empty/unit, missing below/above/between, distinct
payloads sharing a key, all equal keys, sizes four/eight and explicit exhaustion.

Independent native Astra recompiled the frozen source and audited all 31
claims: PASS, standard permitted axioms only. No proof, access, counting or
scope blocker. It specifically confirmed absence/exhaustion separation and
that fuel adequacy requires no sortedness. The implementation is accepted
within its query-only scope. Integration into BSGS is recorded in W009.
