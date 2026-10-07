# W005: proposed conventional BSGS algebra and cost layer

Date: 2026-10-07. Status: algebra-first implementation independently reviewed
and accepted; abstract RAM ledger requires further specification.
No core definition changed. Preceding verified milestone: `05ed8be`.

Proposer: native Sol `/root/small_curve` (read-only task). Coordinator records
the proposal before implementation. This is a conventional baseline needed to
evaluate later improvements, not an improved ECDLP claim.

## Algebra proposal

For an existing `P : CyclicProblem`, let orbit n = iteratePoint P.next P.zero n.
A new separate `OrbitArithmetic P` would contain executable add and neg with:

```
add_orbit : forall a b, add (orbit a) (orbit b) = orbit (a+b)
neg_orbit : forall a, neg (orbit a) = orbit ((P.order-a%P.order)%P.order)
```

These are refinement obligations, not global assumed attack facts. The
SmallCurve instance must use its coordinate add/neg and prove both laws. For
addition, induction and the checked group laws suffice. For negation, use
finite cases plus orbit periodicity. No table-based inverse-log implementation.
The laws do not establish efficient execution; implementations require review.

## Executable baseline proposal

For q>0 and m>0, B=ceil(q/m). Build babies 0..m-1 forward, executing m additions
so the final point is mG; sort cached point keys; negate mG; query successive
giant points target-i*mG for i<B. Return (i*m+j)%q on a match. This modular
return handles m>q duplicate baby keys; W004 used m<=q with a canonical-range
guard, which must not be generalized silently. Zero and q=1 need explicit tests.

Correctness obligations: orbit n = orbit(n%q); orbit equality iff equality of
residues; baby construction invariant; giant invariant with scalar stride
s=(q-m%q)%q; cancellation (s+m)%q=0; sound match recovery; complete witness
i=d/m, j=d%m with i<B and j<m. No q-primality or gcd(m,q)=1 premise.

## Proposed ledger (separate from Machine)

Proposed name: `BSGSRAMLedger`. Counts must arise from explicit primitives or a
small state interpreter, not a postulated cost function assigned to answers.
Trace adds, negations, key construction, equality and order comparisons,
indexed table reads/writes, scalar arithmetic, allocation/release, and peak
live slots. Key comparisons and group calls may initially be abstract units,
with their internal bit/field work explicitly excluded. This is no tape or
hardware model and replaces none of `SolvesWithin` or existing goals.

Suggested implementation: two explicitly allocated arrays for merge sort,
charging copying and storage. A baby entry carries a fixed-width coordinate key
and an index wide enough for m (not just outputWidth if m>q). Cache keys. Binary
search needs charged indexed access, never hidden linear traversal of a Lean
list. Scalar/control costs need stated primitive granularity and register scope.

Suggested conservative targets, L=floor(log2(m))+1:

- additions <=m+B-1, one stride negation;
- binary-search visits <=B*L and equality/order tests <=2*B*L;
- sort comparisons <=2*m*L;
- sorting read/write bounds proportional to m*L, proved for actual chosen code;
- <=2*m live table entries plus explicitly bounded registers.

These are PROOF TARGETS, not proved claims. At m=ceil(sqrt(q)) the suggested
addition target is <=2*m-1, but deterministic sorting/lookup retains log factors.
Physical tape movement, comparator bit work, field arithmetic and hardware
calibration require separate refinements. A cost bound in this layer cannot be
substituted into the existing tape goals.

Build and sort anew for every target in the first baseline. A future amortized
theorem would charge construction + sum of queries, retained memory and table
validation/loading. Coordinates and public constants are fixed independently;
input parsing and target validation must be proved separately if initially
accepting a typed point directly. No secret labels or full inverse table inputs.

## Bounded implementation milestone after review

Implement the algebra refinement and costed baby table, then concrete sort,
binary search and giant loop, keeping separately reviewable stages. Check all
seven coordinate-curve scalars at m=3 and edge m=1, m=q, m>q. Prove general
algebra invariants and cost bounds, rather than treating seven-case checking as
generic BSGS correctness. Std-only kernel checks, each initially timeout60.

Falsifiers: unmatched law/refinement on the coordinate implementation; failing
scalar recovery, especially wrapped/duplicate cases; an uncharged operation
that the proposed ledger says is counted; mismatch between RAM access and
claimed tape costs; unchecked advice in coordinate keys or parameters.

## Sources and alternative hypothesis

[HAC §3.6.2, algorithm 3.56](https://cacr.uwaterloo.ca/hac/about/chap3.pdf)
explicitly distinguishes sorted-table comparisons and group operations. The
rest of this proposal is the proposer's design, not an assertion that HAC
supplies Lean proofs or a tape simulation.

Sol also suggested signed baby ranges with centers (m-1)+i*(2m-1), sign
recovery and charged offset/stride construction. Coordinator independently
proposed zero-centered ranges to Opus in a separate signed-BSGS review. These
are distinct boundary conventions requiring separate checks, not interchangeable
formulas. Any saving is a known constant-factor opportunity with added sign,
key and memory costs, never an exponent improvement. W006 will record tests.

## Independent review and decision

Native Astra `/root/encoding_review`: qualified pass for algebra-first stage.
It independently checked q>0,m>0 arithmetic including m>q: any matching duplicate
baby index works modulo q. Conditional laws suffice for on-orbit targets;
periodicity follows from wraps/iteration and residue equality from distinctness.

Required before later ledger adoption:

1. Explicit deterministic key construction and lawful total comparator, with
   key equality iff point equality on the orbit. Injective encodePoint alone
   does not establish an efficient comparator or coordinate implementation.
2. State correctness only for orbit targets. The Point type may include others;
   input validation and off-orbit rejection are not consequences of these laws.
3. Specify allocation initialization, copying, reads/writes, key creation,
   comparisons, loop tests, arithmetic (including division/modulo) and release.
   Abstract constant-unit Nat arithmetic is not bit complexity.
4. Fix table slot contents/ownership, register/stack scope, temporary copies and
   intermediate scalar widths. <=2m table slots is feasible for explicit
   bottom-up ping-pong merge with one baby buffer plus one m-slot scratch buffer;
   it is not proved for recursive slicing/concatenation or by Lean Array syntax.

Decision: implement only generic orbit lemmas, OrbitArithmetic with coordinate
refinement, and (if tractable) forward baby construction with exact instrumented
addition count and entry/final-point invariants. Sol `/root/small_curve` now owns
only new `Research/OrbitArithmetic.lean`. No shared edits, no global attack
assumptions, no sorted solver/RAM/tape cost claims. General correctness and
boundary instances must be checked independently before acceptance.

## Implementation progress and counting correction

Sol implemented generic iteration composition, orbit period/modulo/equality
lemmas, `OrbitArithmetic`, and the actual SmallCurve coordinate add/neg instance.
Forward baby construction includes general length, indexed-entry, final orbit m,
and instrumented wrapper-count invariants. Edge checks cover m=0..8 on the
order-seven curve, including m>q. `order_one_orbit` handles the generic q=1 case.
The completed independent code/proof review is recorded below.

Coordinator identified an extra cost obligation during source review: the
builder evaluates `orbit P 1` as generator input, which invokes P.next and may
perform coordinate addition outside the instrumented wrapper. The author
renamed the count to `countedAddCalls` and explicitly excludes this setup and
any internal operations. Thus the proved count m means EXACTLY m direct
`countedAdd` wrapper invocations, not total coordinate additions. This narrower
instrumentation is useful for the construction proof but does not satisfy the
planned complete BSGS ledger. A later costed implementation must receive a
validated public generator or charge its computation explicitly; it must not
silently reuse this count as complete addition work.


Final author validation: `timeout 60 ./scripts/lake.sh env lean
Research/OrbitArithmetic.lean` passed, with21 public theorem audits using only
allowed standard dependencies. Four earlier compile attempts failed on routine
elaboration/decidability, with no timeout or mathematical counterexample;
corrected before source freeze. Author's executable edge evaluation returned
(m,length,wrapperCalls,final)=(0,0,0,O),(1,1,1,G),(7,7,7,O),(8,8,8,G).

Coordinator integrated every public theorem into Audit.lean. Full
`./scripts/check.sh` passed93 named audits,14 screened files,31 build jobs and
smoke output. `git diff --check` passed. Independent Astra now reviews this
stable source and W006 separately from its earlier design review; no claim
of accepted RAM/tape/solver correctness is added by compilation.


Independent implementation review by native Astra `/root/encoding_review`:
PASS for algebra and wrapper-count milestone. Recompiled frozen source without
warnings, verified periodicity/residue laws, coordinate refinement, all-m entry/
final/length invariants and stated count exclusion. No code/proof blockers.
This review does not adopt the deferred RAM model or certify total additions.
