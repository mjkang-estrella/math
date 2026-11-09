# SUMMARY — r14 start-support lane (sealed)

One small pure base-state fact, really compiled, really kernel-checked, sealed.

- `Bun.startST_support` in `src/BunStartSupport.lean` (imports `BunState`; existing
  `startST`/`sval` used as-is): for all `n j k`, `w : Asg n j`, `sigma : Bool`,
  `k ∈ sval sigma (startST n j w) → k = j`. First component is `{j}`; second is
  `{j}` or `∅` per the vertical bit when `j < n`, else `∅`.
- Build: exit 0 under runner caps (wall 798 ms, peak group RSS ~1.7 GiB sampled).
  receipt/1794011809072540936_lean_BunStartSupport.json
- Axioms: exactly [propext, Classical.choice, Quot.sound]
  (logs/1794011884638815943_audit_bunstart_support_axioms.log, verbatim:
  'Bun.startST_support' depends on axioms: [propext, Classical.choice, Quot.sound]).
- leanchecker on module BunStartSupport: exit 0.
  receipt/1794011815767791160_leanchecker_BunStartSupport.json
- Post-checker hashes identical to build receipt:
  source c99ead1ea5d55cb194cb7e0b124afb89c36f92dc3e33dde6c9fae0ad8401c9d2
  olean  317e7ae93d5070d6ff1af5e7bf3057d9827e4b3e3e0ac0cb8fba3a092c51fc8b
- Frozen inputs 717/717 before (zero mismatches); after in frozen-after.json.
  Bootstrap receipt preserved. Three failed-attempt receipts retained.
- Credit 0 for 382297; campaign 52/60 beyond 39 prior, unchanged.
- Everything beyond this one fact remains unpaid; see CHECKPOINT.md for the
  explicit unpaid list. No future-tense claims: all artifacts above are on disk now.
