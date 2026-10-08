# H028 finite layout gate and progression duplicate bound

2026-10-08. Paper analysis only; no new numerical run, Lean claim or complete
work improvement. Root proposed the progression lemma below; native Astra and
Sol independently checked its orientation, inverse, zero-key and wrap cases.
Astra separately proposed finite sizing and three concrete layout alternatives.
Sol's full-cost review remains pending. Claude prior-art r1 returned; root
corrected its source-access gap using the already-read GWZ published mirror,
and NEW independent r2 is pending. Raw r1 is retained separately.

## Why another solver trial is not yet admitted

The completed diagnostic's literal finite setup loses all12 cases. This does
not reject larger sizes. Two binary Miller chains for Gprime and Qprime suffice:
propagate h alongside the already-paid point construction of offsets, centers
and strides. Do not charge an independent Miller chain at every initial point.
Candidate-specific generator randomization still costs a scalar multiplication;
the exact-x comparator must not be forced to do it.

For an illustrative, untuned k=ell=8 block (136 generated records), under
H019's regular arithmetic ledger and hypothetical S/M=4/5,I/M=8,A/M=0,

    Cx = 2569/680 M per key,
    regular saving = 64/85 M per key,
    saving minus 10% of Cx = 2551/6800 M per key.

Root checked these fractions against the accepted block formula. These are
operation prices, NOT measured hardware rates. If L is common per-key lookup
and storage cost/M and DeltaL the candidate's additional per-key cost/M, a
necessary budget for obtaining the targeted10% saving in this optimistic
regular ledger is

    DeltaL + 0.1 L + other extra cost/key < 2551/6800.

The complete comparison also includes startup, exceptional branches, terminal
block overshoot and verification. Finite savings must be compared at the actual
stopping times; do not assume both randomized solvers stop at the same index.
The conditional sizing suggestions around q~2^28 to2^30 are NOT admitted
fixtures or forecasts: they omit specified layouts and exact finite startup.
No challenge generation, benchmarking or frozen-probe rerun has occurred.

## Stronger local theorem controls same-side duplicates

The global second moment alone does not imply that same-side keys are iid.
However H028's local theorem says: for every nonzero T, at most TWO ordered
pairs of distinct nonidentity points U,V with U-V=T satisfy h(U)=h(V).
This gives a useful deterministic bound for a progression

    P_i = A+iB, 0<=i<m<q, B!=O,

with actual infinity dispatched and removed from key matching. For m>=2:

1. Equal h unordered pairs oriented by i<j have difference P_j-P_i=(j-i)B.
   There are m-1 possibilities, at most2 ordered pairs for each. This contributes
   at most2(m-1) unordered pairs.
2. Opposite h pairs with P_i!=-P_j produce TWO distinct ordered equal-h pairs
   (P_i,-P_j) and (P_j,-P_i), both at nonzero difference
   T=2A+(i+j)B. At most2 ordered pairs per T means at mostONE original unordered
   pair per T. Sums run from1 through2m-3; reduction modulo q only identifies
   possibilities. Contribution at most2m-3.
3. Exact inverse pairs have T=0 and are excluded from step2. Negation pairs
   distinct nonidentity points disjointly, contributing at most floor(m/2).

Canonical key equality means equal OR opposite h. Zero h can make these cases
overlap, which only overcounts. Therefore the total unordered canonical-key
collision pairs are at most

    4m-5+floor(m/2).

For m=0 or1 the bound is0 instead. Dropping infinity or using any subset of a
fixed enclosing progression cannot increase its pair count; the bound is in
terms of enclosing length m, not automatically the subset size. H019 completed
prefixes have the required progression form. Arbitrary unions, repeated records
or unrelated streams are not covered without additional accounting.

If each insertion compares each earlier equal-key record at most once, total
same-key insertion comparisons are O(m) on such prefixes. This does NOT bound
different keys sharing a hash probe cluster, justify ordinary universal hashing
for constant-time linear probing, or make the finite comparison constant small.
Translated giant prefixes can contain inverse points. The x comparator may
retain one representative per exact x key, but cannot assume all inserts unique.

## Concrete layout choices and remaining decision

Astra's first layout review proposed:
- Balanced tree on distinct keys plus prepend-only duplicate index lists:
  deterministic logarithmic dictionary work, output-sensitive cross matching;
  additional duplicate-head pointer per distinct key and index/next per duplicate.
- Universally hashed distinct-key dictionary plus those lists: expected constant
  lookup conditional on independently chosen hash and fixed geometric stream;
  hash evaluation, collisions, resizing, slack and duplicate metadata paid.
- Geometric sorted runs: compact sequential storage, but logarithmic movement
  and multiple-run search/merging work. No demonstrated advantage here.

Its initial warning that nothing controlled same-side clustering was corrected
by the progression lemma above. The correction does not establish a cost win.
All layouts must compare against a competent x implementation, not force it to
carry candidate-only lists or archives. Packing index and pointer fields requires
explicit bit widths, alignment and access costs; semantic fields are not words.

Root also proposed a simpler candidate for review: prepend EVERY record into
an ordinary chained hash bucket, without same-side lookup, then scan the opposite
bucket and compare exact keys before verification. This avoids a separate
per-distinct-key duplicate-head structure. It needs a key/index/next per record,
charged independent hashing, capacity/resizing and honest baseline comparison.
Its complete finite ledger has not yet been independently accepted. No numerical
experiment is admitted from this proposal alone.

Next decisive work is a frozen explicit record/hash/resize contract whose finite
weighted ledger can meet the margin above, followed by matched stopped synthetic
solvers if justified. Best supported generic exponent remains1/2; verified
complete-work improvement NONE. Broad ideation and retained rejected candidates
remain part of the active goal; this is candidate-specific analysis, not generic
proof infrastructure.
