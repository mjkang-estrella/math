# Nut8 assembly status

The unconditional theorem `Nut8.no_cubic_8circulant_nut : Nut8.Target` compiled strictly as `nut8_target per_support`. Its printed axioms are exactly propext, Classical.choice and Quot.sound. PerSupport and all 194 support bundles compiled. All 287 regenerated certificate modules compiled; the certificate count remains 9,172.

Development validation: leanchecker passed for Nut8Final; the complete 1,024-module proof closure audit passed 128/128 shards and inspected 46045 local declarations, including generated declarations, full types, opaque-accessible bodies, flags and transitive axioms. All 18/18 negative controls passed, including existing-olean refusal. No audit module occurs in the proof closure.

Six observed compilation fixes are recorded with before/after hashes and failure/passing receipts: FiniteSupport162–166 only raise maxRecDepth from 4096 to 8192; PerSupport replaces an unused singleton simplification with explicit empty-list membership and or_false. Other inherited sources, all r6p modules and NutInterface are byte-identical. Input hashes match before and after.

Final acceptance validation remains incomplete. The corrected source-only packet was extracted into the new empty fresh-final directory; 12/1,151 strict rebuilds passed there. Final all-module leanchecker, audit and negative-control phases remain pending. The earlier extracted replay is historical evidence and is not final validation of the corrected packet. See GAPS.md for the precise next step. No acceptance or count credit is asserted. No background jobs remain.
