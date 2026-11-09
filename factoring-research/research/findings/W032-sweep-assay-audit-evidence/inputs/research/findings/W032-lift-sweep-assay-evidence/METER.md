# Frozen meter and execution contract

One execution, in the fixed group order. Candidate arithmetic is in `assay.py`;
`run_once.py` verifies the freeze and supervises the same global wall deadline.
No source is imported for numerical inspection before this execution. Syntax
inspection with `ast.parse` is permitted and performs no assay computations.

Each successful substantial integer primitive emits one consecutive event to
`events.jsonl`, beginning at 1, with phase/group, exact operands and result,
operand/result absolute bit lengths, and elapsed time. Primitives: addition,
subtraction, multiplication, floor division, remainder, divmod, gcd, modular
inverse, absolute value, bit length, and each integer comparison actually used.
`divmod` is one native quotient-and-remainder primitive with two result widths.
`math.gcd` and `pow(a,-1,M)` are explicitly native gcd/inverse primitives: their
internal iterations are NOT individual events. They are not claimed to be
constant bit-cost. No ordinary or modular positive power is a primitive:
binary powering charges every multiply, reduction, exponent divmod and loop
comparison. Pair multiplication charges its five products, two sums and two
reductions individually. Horner evaluation charges square, reductions, every
product and every sum. Coefficient/weight/threshold construction is charged.
Primality uses exact trial division with charged trial products, comparisons,
remainders and increments. Sorting uses stable Python sort with an instrumented
`__lt__`: every threshold comparison is charged, including failed comparisons.
Ties are grouped by charged equality tests before the single aggregate update.
Coverage, interval lengths, value bounds, probability fractions and all numeric
reference computations use the same meter. There is no factor-selected event.

List/dict/set indexing, iteration over predetermined lists/ranges, iterator
advance and bookkeeping counters, allocation, JSON/UTF-8 serialization, string
labels, exception handling, clock reads, instrumentation's bit-width extraction,
event IDs/statistics, and file/hash integrity administration are not arithmetic
events. They do consume wall time. Set/dict hashing/equality used to count
distinct values is separately declared administration; it is not a bit-cost
claim. Numeric tests affecting the mathematical computation are metered, not
silently treated as administration. Index arithmetic in static ranges is also
administration; numeric formula arithmetic is metered. The summary includes
counts of records, operations by phase/type and maximum widths. No squared-width
proxy or fitted exponent is used. Events are a diagnostic, not bit complexity.

Before each primitive, a 20,000-event global cap and the global deadline are
checked. The 20,001st primitive is not executed. Failed primitive attempts have
their own error record; no success event is invented. One second of the 60-second
global cap is reserved for terminal recording: new computation is stopped at
59 seconds. The runner kills the process at 60 seconds if needed. All input
verification, prime generation, setup, candidate work, controls and JSONL output
are timed. Terminal status/output flushes are included in the runner's elapsed
time. Post-execution reading, report composition, and delivery hashes are
administrative sealing, with no further numerical assay work permitted.

Every completed primitive/interval/tie/control point is written immediately.
`records.jsonl` begins with planned group/control records. On a cooperative stop,
partial objects and every stopped/unstarted group/control remain in `status.json`
and final records. Hard kills retain the initial plans and partial records; the
runner labels them incomplete rather than assuming zero work. A failed control
stops this execution as a correctness failure. A failed unit branch retains all
initial gcds, makes its sweep/controls inapplicable, and advances only to the next
already fixed group. A discovered proper sweep gcd never stops the family.

Each threshold-to-threshold interval is recorded, including zero-net tied
updates. Adjacent intervals with equal c are additionally merged into maximal
constant segments. Every interval gcd is retained. Full coverage is checked by
adjacency and total length; probability is length-weighted, never interval-weighted.
Probabilities are eligible for the stated finite interpretation only when all
required controls and verification for the group pass.
