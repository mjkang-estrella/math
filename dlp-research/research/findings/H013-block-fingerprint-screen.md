# H013 block-index fingerprints: storage saved, replay paid

2026-10-08. Native Astra /root/h007_additive_relations supplied the card; root
narrows its hashing assumptions below. No experiment, new engine, asymptotic
improvement or measured constant saving. Other reservoir/checkpoint/multi-target
join suggestions duplicate H002 and are not renamed as new hypotheses.

Generate M babies iG and split into blocks of length L (take L|M for clarity).
Store w-bit fingerprint plus floor(i/L) and one full point checkpoint per block.
Traverse Q-jMG. Every matching record triggers literal consecutive replay of
its block and exact point comparison. Retain every equal fingerprint record.
A genuine match recovers i then d=i+jM modulo q; final group check required.
Setup includes all baby additions, fingerprints, sorting/indexing and checkpoints.

For an exact expected-cost calculation, fix T_miss giant points outside the
baby set independently of fingerprint randomness. Use a fingerprint family
with EXACT collision probability2^(-w) on each distinct pair (e.g. strongly
pairwise-independent uniform outputs), with paid construction/evaluation. Mere
universal hashing gives an UPPER bound and cannot establish the necessary lower
threshold below. No hash-independence from adaptively selected queries is assumed.

There are M*T_miss distinct cross-pairs. Linearity gives expected false records
M*T_miss/2^w. Each causes a full L-step unsuccessful replay in this literal
per-record procedure, hence expected extra additions proportional to
M*T_miss*L/2^w. If T_miss=Theta(q/M), this is Theta(qL/2^w). This traversal
length is a stated average-case/regime assumption, not every target's cost.

Keeping false replay within O(T_miss) requires2^w=Omega(M L). Main record bits
are M*(w+ceil(log2(M/L))), so their leading per-record count is at least
2log2 M up to additive constants. The omitted log L label bits return as extra
fingerprint bits. Checkpoints add O((M/L)*log q) bits plus directory/storage
overhead, and genuine-hit replay adds O(L) operations. Explicit caching or
batching of repeated block hits changes the operation and needs its own ledger.

This is not a universal constant-factor impossibility. A competent full-label
truncated-key baseline also pays verification. If its false-match verification
cost is V group operations, its analogous threshold is2^w0=Omega(M V), giving
roughly2log M+log V record bits. Block replay could save additive O(log log q)
bits when V is polylogarithmic, before checkpoints and timing effects. No complete
byte-and-operation comparison currently predicts a material crossover.

K targets multiply both miss traversal and false replay by K; the threshold is
unchanged. Charge shared M-step setup once, every target traversal and exact
verification. This is ordinary table amortization, not a new multi-target gain.

Proposer prior-art leads: https://eprint.iacr.org/2021/899 for truncated lookup
tables, and https://eprint.iacr.org/2015/605 for improved BSGS comparison.
The former's bounded-range setting is not a full-range cost theorem. Root has
not adopted source-specific novelty statements from these leads. No benchmark
until a complete matched ledger predicts a material saving; no broad lower bound.
