# H039 hybrid: matched-memory and arithmetic gate

2026-10-08. Native Sol `/root/h034_c4_implementation` read-only review;
root checked the algebra against H039-composition-disposition.md and the
accepted H019-xonly-baseline-screen.md. Paper analysis only. No experiment,
new Lean claim, hardware estimate or claimed discovery. Prior-art review is
separately pending under the task ID recorded in STATE.md.

## Full-memory arithmetic comparison

For a uniform full-range scalar, H019 interleaved negation BSGS has leading
survival max(1-z²/2,0) after z sqrt(q) emitted keys. This uses its contiguous
prefix coverage and enough memory for the entire schedule. Small finite seams,
batch overshoot, dispatch and setup remain as scoped in H019.

The fixed-table hybrid assumes survival exp(-u²-2 beta u) after beta sqrt(q)
babies and u sqrt(q) walk points. Use its assumed costs c_b per baby and
c_w+P per walk point; normalize a paid arithmetic budget by c_b sqrt(q).
Then the hybrid has z=beta+r u with r=(c_w+P)/c_b. For r>=3/2,

    z²/2 - (u²+2 beta u)
      = (beta+(r-2)u)²/2 + (2r-3)u² >= 0.

Since exp(-x)>=1-x for x>=0, the H019 survivor is no larger than the hybrid
survivor at every such budget. Before hybrid setup finishes (z<beta), its
survival is1 and H019's is at most1. After z>=sqrt(2), H019's leading survivor
is0. Thus the comparison includes both boundary regions. Integrating the
survival functions also compares expected paid arithmetic in these models.

With c_b=(2.5+s)M, c_w=(5+s)M, s=S/M in[0,1], and P>=0,
r>3/2. Therefore this particular hybrid's ideal field-arithmetic opening over
rho disappears against H019 WHEN H019's full table fits. This is not inferred
by subtracting upper bounds; it compares the stated leading survival models
under an explicit common arithmetic invoice. The hybrid law is assumed, not
proved for an executable walk. H019 table traffic, allocation, hashing and
labels are NOT priced by this arithmetic model, so this is not a complete-cost
or wall-clock dominance theorem. Additions are omitted by the existing field
ledger convention. Known extra automorphisms must be matched on both sides.

## Restricted memory is not automatically fatal

Realizing every self-collision by archiving all visited points requires their
records/labels or paid reconstruction. This is additional to beta sqrt(q)
babies, and the unbounded-horizon integral g(beta) cannot silently coexist
with a hard archive cap.

However, that objection does not rule out distinguished-point detection.
A conditional feasible scale illustrates why. Fixed beta>0 still means
Theta(sqrt(q)) baby records, not an asymptotically low-memory algorithm. Let n=ceil(log2 q), use n²
batched walkers and distinguished-point probability theta=n^-4. Assume a
competent coalescing walk with the required useful-collision behavior and
controlled cycles, starts, endpoint handling and recovery. In a field-operation
accounting where inversion costs O(n) multiplications and each restart costs
at most O(n²), the illustrative overhead orders are:

- Amortized inversions: O(sqrt(q)/n) field operations.
- Expected endpoint records: O(sqrt(q)/n^4), each still O(n) bits plus metadata.
- Restart work: O(sqrt(q)/n²) field operations under the stated restart bound.
- Aggregate reporting delay: O(n²/theta)=O(n^6) walk steps, conditional on
  expected coalesced-path delay O(1/theta).

The process needs a common deterministic quotient transition, suitably
distributed DP predicate, controlled DP-free/fruitless cycles and useful
nonzero coefficient relations. Null hits, scalar inversion and final
verification require paid policies; endpoint capacity/overflow and fallback
are not supplied by an expected-count bound.

These are lower order than sqrt(q); baby storage for fixed beta>0 remains
Theta(beta sqrt(q)) records, or Theta(beta n sqrt(q)) bits. They do not imply
that the actual chosen walk has the ideal law, that useful coefficients always
result, or that cycles are controlled. Field-operation estimates are not bit
complexity or measured time; conversions and table costs must be explicit.
The scale only defeats the unsupported claim that memory overhead MUST erase
the small-fixed-beta opening. It does not establish an improvement.

## Admission gate

The next useful evidence must specify a memory budget and record layout,
actual transition and cycle policy, collision-reporting/recovery contract,
useful coefficient handling, and paid lookup/setup/fallback costs. Compare
against rho with the SAME detection implementation and the best feasible
restricted-memory BSGS/interleaving/preprocessing alternatives. Fully charge
single-target preprocessing; a many-target online advantage is a different
claim. Primary prior-art review must establish whether the proposed blend is
already known before any novelty language or new experiment.

Verified complete-work improvement NONE. Best supported exponent1/2. The
remaining hypothesis is a conditional constant-factor, restricted-memory
opening, not an exponent improvement. No new numerical run is admitted.

Validation: ./scripts/check.sh > /tmp/ecdlp-h039-hybrid-memory-check.log 2>&1
exit0 (366 existing audits). No new Lean claims; this checks repository health,
not the paper model. Native Sol final review completed with the conditions
above; root independently checked the square completion and boundary cases.
