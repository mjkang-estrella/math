# W002 Lens A — Coordinator intake

2026-10-08. **SUBMISSION READ; new deductions UNACCEPTED pending review.**
Verified COMPLETE classical factoring complexity improvement: **NONE**.

The constructive task completed with no pending child runs. The coordinator read
all 414 report lines and the input inventory/source notes, verified all 17 frozen
input records and 27 delivery entries, and preserved an identical submitted
draft. Only the current mutable research/STATE.md differs from the input
inventory; its saved snapshot verifies. No mathematical experiment was run.

Report and identical submitted-draft SHA-256:
35ae0bb4b0412f7a5a1d3a26c5e1d554b32df614e6c05437de3d355e5d90872f.

## Provisional mathematical reading

The proposal explicitly changes the interface from H030's arbitrary-modulus
product to a divisor-of-input product-or-factor procedure. It retains H029's
original row IDs and promises, with paid small-factor preprocessing. The
proposer derives e<8K<M, uses a further paid factorial stage through 8K, and
then identifies interval nonunit residual products with intervals containing
a zero residual. Recovery from any such original zero row uses
A_minus*A_plus=4kM and 1<=A_minus<=A_plus<M. The conditional product reduction
has logarithmically many queries and preserves original prime multiplicities.

The concrete HullProbe is a different factor-or-UNIT interface. It covers the
linear factors by a containing integer interval, caps the tested prefix at
ceil(sqrt(M)), and returns any verified factor found there. If the cap truncates
the hull, a hit is guaranteed because the smaller factor is at most sqrt(M).
Thus it must not report UNIT after a truncated unit prefix; the proof says that
case is impossible. Full gcd descent follows only one unresolved integer
interval and must split before a singleton because each tested integer is
strictly between 0 and M. This is not a claimed location of a descriptor row.

The full query is claimed to construct Theta(M^(1/4)) dense coefficients before
checking its product gcd. The claimed complete N_0^(1/4)*poly(log N_0) envelope
therefore fails the sub-1/5 target by an actual specified-construction cost,
not by interpreting an upper bound as a lower bound. It is a known factorial
search in this form. The parent found no immediate algebraic contradiction
while tracing these steps, but this is not acceptance or an independent audit.

## Independent review obligations

1. Check every constant and boundary in (5)-(7), including ceiling conventions,
   K=16, nonzero residual units after the second stage, and why e<M suffices for
   recovery before that stage. Do not use numerical sampling in place of proof.
2. Check arbitrary original row intervals, partial sign endpoints, duplicates,
   original-coordinate decoding, zero rows with y=0, all gcd outcomes, the
   reachable-modulus restriction and restoring the input's multiplicities.
3. Check HullProbe's interval clipping, capped-prefix UNIT reasoning, padding
   semantics and paid full-gcd descent. A padding hit need not be an original
   row, but must return a directly verified proper factor.
4. Check the complete bit/memory/access ledger: both factorial stages, primality,
   descriptor generation, monic remainder trees over composite rings, no hidden
   inverses, tail arithmetic, every repeated product query and width bounds.
   Validate the degree-written lower bound only for the specified execution
   order on continuing inputs. Verify the family of continuing semiprimes and
   distinguish M-scale from N_0-scale costs.
5. Check the prior-art relationship and the exact closure scope. No general
   product lower bound, faster zero decision, N-only polynomial factoring,
   new factoring exponent or success oracle follows. Suggest only necessary
   repairs, or a genuinely distinct decisive reopener if one is supported.

No revision is requested or applied before review. There are no prior review
rounds or proposer responses for this submission. The report's lack of a
sub-1/5 realization is not a claim of impossibility for residual products.
The other two W002 researchers remain live and independent; do not read their
drafts or duplicate their tasks.

[Submission](W002-paired-residual-products.md),
[preserved original](W002-paired-residual-submitted-draft.md),
[input inventory](W002-residual-inputs.json),
[source notes](W002-residual-source-notes.md).
