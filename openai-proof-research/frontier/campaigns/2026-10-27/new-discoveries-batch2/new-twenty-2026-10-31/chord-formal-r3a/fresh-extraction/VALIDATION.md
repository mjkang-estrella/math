# Validation receipts

Exact machine-readable status, source hashes, line counts, audit totals and
remaining hypotheses are in results.json, generated only after the fresh replay.
All calls retain unique timestamped full logs. The original strict rebuild is
logs/initial-build.log. The fresh serial replay and audit receipts are under
fresh-extraction/logs/. The full per-declaration audit is
fresh-extraction/audit.jsonl; local and upstream totals are reported separately.

The independent regression reports no mismatch through five chords for either
the ±1 deletion equation or the proposed C-successor swap normalization. It
covers 4,948,900 actual deletion/assignment triples, including the empty annulus.
The negative controls reject a zero empty-boundary count, the wrong Euler offset,
and the identity in place of the surgery operation. Finite regression does not
close either generic surgery Prop.

Only the permitted axioms occur transitively in local imported declarations.
The source evaluator and all 41 inherited modules are unchanged; compare
frozen-before.sha256 and frozen-after.sha256. No acceptance is claimed.
