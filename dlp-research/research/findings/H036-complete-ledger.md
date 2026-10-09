# H036 strengthened comparator and conditional complete ledger

Status: reviewed paper accounting screen for explicitly enumerated layouts;
not a verified executable speedup, globally optimal backend or calibrated price
model. Native Sol supplied schedules and invoices. Root corrected two packet
errors and selected exclusive prefixes; native Astra independently checked
descriptor invariants and COMPLETED the abstract final gate audit. No code run.

## Descriptor-free chronological archives

The H034 archive inserts every unsuccessful chronological leaf query until its
first match. With one-based code c, descriptor=c-1, edge=(c-1)>>1, and sign is
(c-1)&1 (zero denotes plus). Decode only at recovery; that work is paid.
For nonzero Q, interleaved merged H019 skips baby0=O, then inserts giant0,
baby1, giant1,..., so role=c&1 and index=c>>1. Split-role codes similarly give
baby index=c, giant index=c-1. Nodes need only(key,next), not a descriptor field.

This requires per-index inspection, no future centers inserted early, EVERY
unsuccessful query inserted including same-role duplicates, and no deletion or
continued skipped match. Giant infinity and valid cross-role equality terminate.
H034 null recovery clears the archive and starts a freshly numbered fallback;
a zero shifted target returns before allocating it. Resource censorship is
terminal, not resumable state. These are literal-contract invariants, not
properties of all solvers or descriptions of the frozen Python source.

Role-first traversal uses the current node code, avoiding a stored tag read.
Masks/branches remain paid. Selective key access needs a supporting layout.
The prior matched-memory record/head ratio4 is superseded by3 for typed packed
payload (n-bit key, n/2+O(1)-bit pointer/head), or2 for uniform n-bit cells.

## Explicit regular schedules and corrected packets

Use canonical modular prices M,S,A, field reads/writes RF,WF, index/pointer
reads/writes RI,WI, integer increment/subtraction alpha, integer comparison with
branch epsilon, field equality with branch e, and mask/parity chi. Indexed
access includes address calculation; other index transformations are charged.
No physical bit-packing implementation is inferred from these declarations.

Both arms use H035 fused side keys with F=2.5M+S+3A per regular key. Batch
arithmetic is(5b-3)M+2bS+6bA+I. Store exclusive prefixes at their OWN index,
p_i=product_{j<i}d_j, so inverse traversal needs no i-1 subtraction. Endpoints
retain3b-3M prefix/inverse work. Full updates and center keys pay3r corrections.

Candidate: process a full thickened-graph line batch, gather point indices,
construct denominators/prefixes, invert backwards, then emit plus/minus keys
directly to the archive. Alternatively replay the deterministic graph iterator
instead of storing its indices; its reconstruction is charged.

Stronger H019: use ONE center per role and ellH=n² offsets per block, transposing
the old center/offset batching. Batch-invert all offset denominators. Process
offsets descending, inspect lower-side baby and giant keys immediately, retain
only upper-side keys, inspect centers, then upper sides in ascending order.
This preserves contiguous per-index inspection. Offsets uG and -uDG are
DIFFERENT coordinates; root rejected Sol's temporary cross-role reuse claim.
Only loop indices are shared. Setup, full advances, exception slow paths and
terminal workspace remain lower order with the same growth assumptions.

| Declared packet | Candidate2b keys | H0194b keys |
|---|---:|---:|
| Field reads including buffered inspection | 6b | 14b |
| Field writes | 3b | 8b |
| Gathered index reads/writes | b/b | 0/0 |
| Integer arithmetic | 5b | 4b |
| Integer loop comparisons | 5b | 4b |
| Denominator zero tests | b | 2b |

These are explicit paper implementation invoices, not a proved instruction
minimum. The withdrawn alternatives included a slower14b-transfer gather-copy
packet, full rather than half output buffering, erroneous shared role offsets,
and an unnecessary reverse predecessor subtraction. No measured rate relies on
them. Endpoints are O(1) per batch; further concrete code may change the invoice.

The resulting core differences are

    delta_gather = -(RF+WF)/2+(RI+WI)/2+3alpha/2+3epsilon/2,
    delta_replay = -(RF+WF)/2+5alpha/2+5epsilon/2.

With equal prices for all cell reads and writes, gather's traffic terms cancel;
its remaining positive integer cost is not a zero-cost indexing assumption.

## Table and lifecycle prices

For an unsuccessful insertion define

    tau=chi+RI+WF+2WI+alpha+2epsilon.
    vC=vSplit=epsilon+RF+e+RI,
    vMerged=2epsilon+chi+RI+(RF+e)/2.
    gC=F+3RF+3WF/2+(RI+WI)/2+5alpha/2+5epsilon/2+e/2+tau,
    gB=F+7RF/2+2WF+alpha+epsilon+e/2+tau.

Thus gC-gB=delta_gather. Split H019 uses gSplit=gB+RI for its separate insertion
head; merged uses gB. The averaged merged probe price uses the reviewed half
same-role visit count and selective key reads; the deterministic duplicate and
terminal corrections are O(1). It is not a physical cache statement.

Retain node reservation/release price rho and head reserve/zero/release price z.
One explicit per-cell lifecycle invoice is

    rho=aF+aI+dF+dI+2alpha+2epsilon,
    z=aI+WI+dI+2alpha+2epsilon.

Unused node payload is not initialized. The actual chosen allocator may realize
different costs; these loops are an explicit convention, not a universal
allocation lower bound. Candidate capacity is3sqrt(q), H019sqrt(2q), up to
lower-order terms. With Hc=h*sqrt(q),1<=h<2, spare heads satisfy

    (m-1)h <=3(3-sqrt(2))  [typed packed payload],
    (m-1)h <=2(3-sqrt(2))  [uniform n-bit cells].

Hence m=1,2 fit, and m=4 requires respectively h<3-sqrt(2) or
h<(2/3)(3-sqrt(2)). Equality boundaries need rounded finite admission; scratch,
null codes, headers and setup peaks cannot be ignored. This corrects the older
unconditional admission of4Hc based on unnecessary stored descriptors.

## Fixed fallback and complete symbolic gate

Fix candidate fallback in advance to fresh blinded MERGED H019 at m=1. Let
a=integral_0^3 exp(-x²)dx, f=exp(-9), b=2sqrt(2)/3. Against control lambda
(merged or split) with admitted head multiplier m, the ledger difference is

    D = a*gC+f*b*gB-b*gLambda
        +z*h*(1+f-m)+rho*[3-(1-f)*sqrt(2)]
        +[(1-f)*vC+f*vMerged-vLambda/m]/(2h).

Expected modeled difference is D*sqrt(q)+o(sqrt(q)) IF the declared invoices
are realized as exact leading charges and the prior moment hypotheses hold.
Subtracting two implementation upper bounds alone cannot establish actual
cost ordering. This gate is therefore an accounting screen pending a realized
backend, not a completed proof about executable work.

For merged m=1 it simplifies to

    [(1-f)b-a]*gB > a*delta_gather+f*z*h
       +rho*[3-(1-f)*sqrt(2)]+(1-f)*(vC-vMerged)/(2h)

for a favorable candidate ledger. Since[(1-f)b-a]>0, sufficiently large shared
field prices relative to fixed other prices give an open favorable symbolic
region for every finitely enumerated admitted control. Sufficiently large rho
gives an unfavorable region even at merged m=1. Neither region is calibration,
a strongest-baseline comparison, or a way to declare an attack by choosing
convenient arbitrary weights.

Under the existing thickened-graph assumptions, root generation costs
O(q^(3/10)*n²), workspace O(q^(1/5)), and enumerator setup, prime search,
row-base updates, batching and final waste are o(sqrt(q)). Seed scanning needs
its OWN O(q^(3/10)) capacity table; quadratic scans or extra sqrt(q) head
clearing are not free. H019 transposed ellH=n² gives polynomial setup,
O(sqrt(q)/n) inverse overhead and O(sqrt(q)/n²) full advances. Required common
certification remains charged unless separately bounded.

Decision: no new experiment or implementation admitted. A concrete backend
with justified prices and finite capacities is the missing premise. Further
generic hash lemmas do not decide this sign. The exponent remains1/2 and
verified executable improvement remains NONE.

Final independent audit accepted the fixed-fallback algebra and both capacity
ratios, and emphasized that strict thresholds give leading slack while equality
needs rounded finite accounting. It also accepted the signs of the common
field-price and node-lifecycle coefficients. Root and reviewer explicitly
reject subtracting two upper bounds as a proof of actual speedup. This closes
the H036 paper gate; no further generic packet optimization is commissioned.
