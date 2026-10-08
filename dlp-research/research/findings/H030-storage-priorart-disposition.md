# H030 storage: known hierarchy, no new complete-work result

2026-10-08. Opus raw review in H030-filter-priorart-opus-raw.md. Root directly
read the source below; native Astra separately reviews the report's new
recursive asymptotic extension. No executable experiment or Lean claim.

## Primary implementation evidence

Root read [keyhunt.cpp](https://raw.githubusercontent.com/albertobsd/keyhunt/main/keyhunt.cpp)
on2026-10-08, including lines1120–1145,1228–1284 and4232–4309. It constructs
smaller tables by successive ceiling division by32, has three Bloom levels,
and uses smaller-range searches after filter hits. The final level searches
a table with truncated abscissa and index, then tries signed recovery and
point verification. This establishes prior implementation of the index-free
filter plus smaller recovery-table mechanism; it is not a correctness audit
or throughput measurement. No software was executed, installed or targeted.
The current main URL is mutable; no historical first-invention date is claimed.

Card A must therefore be compared against tuned hierarchical compression,
not solely an uncompressed/truncated-key-plus-index table. Novelty of its
basic recovery mechanism is not supported. A useful finite improvement could
still exist, but needs an actual differing operation, layout or parameter
advantage with matched complete cost. No such verified delta is supplied.

## Review scope and unresolved assertions

Accept the need to charge unsuccessful signed searches and filter construction,
seed independence, rebuilds and probe time. Approximate universality alone
does not justify every quoted Bloom/cuckoo formula. Root's independently
reviewed partitioned construction in H030-partitioned-filter-screen.md gives
one explicit valid guarantee and exposes its own paid field-hash build loss.

Opus's replacement finite density ratios/cache costs are not accepted numerical
results. Its new arbitrary-depth O(1)-bits hierarchy requires independent math
and complete-cost review: exact interval coverage/clipping, leaf lookup costs,
independence across levels, false alarms and construction storage matter.
Likewise its quoted primary hash/filter theorems are source leads until their
exact hypotheses are reconciled; the accessed-code evidence above is narrower.
Do not turn 'known' into a proof of no performance benefit, or a random target
shift into an unproved universal repair for seed-adaptive queries.

Disposition: no Card A numerical run or Lean infrastructure now. Retain it as
a known-class memory tradeoff requiring a new concrete advantage to reopen.
The literal field-hash variant already has a scoped asymptotic setup loss;
other filters are not disproved. C2 remains the leading live hypothesis.
Main estimate unchanged: generic exponent1/2, verified improvement NONE.
