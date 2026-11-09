Implementation proof notes, not a manuscript.

For any complete w, lastSplit_cut characterizes the cut after all splits. Every split at one-based position |u|+1 in u++m::v lies at or before lastSplit, which is attained when positive. Consequently the suffix after the cut contains only combines.

At each deterministic prefix u, the literal BlockEvent requires full three-letter no-split blocks with high-token starts. event_step proves that its complete-word set partitions across existing children of length |u|+3. The children have disjoint cylinders. Induction proves literal_event_mass exactly, including the base cylinder and low-token exits. The disjoint forest at depth r has mass fixedBlockMass; r9 bounds it by (1-p)^q.

An executed suffix longer than 3q+n+3 has high-token starts at every required three-step position, by r9 long_combine_suffix_high. long_suffix_event consumes three letters per step and proves membership in the literal event. For r=lastSplit, the complete-word length estimate gives 0≤r≤3N. Thus the actual tail event is included in the union of 3N+1 fixed-r literal events. Finite subadditivity gives the stated rational bound. No probabilistic conditioning at the random cut is used.
