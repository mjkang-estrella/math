CHECKPOINT r10 — BunUpperSupport DELIVERED (on disk, actual)

Done, verified on disk in this lane:
- verify_frozen before: 594 / 0 mismatches (t=1794004059.3); after: 594 / 0 (t=1794004199.0).
- First mathematical op was check.sh BunUpperSupport on the root-repaired copy
  (no prior inspection): EXIT 0, receipt 1794004062762172392_lean_BunUpperSupport.json.
- Sealed: receipt/SEALED_BunUpperSupport.json
  source 367e352d192210719de0a376eafeac19605cec37b0eda24541811676963e335c
  log    34781cb19c18b0659d2ca4ee6e0c8c0fc3615942927438d42521159b4c2c1d86
  olean  80e682258236ef6b07a6bfd7f66715ba98712ab97b7d5c0c5f57794150386b3f
- Scoped #print axioms (same runner/caps), EXIT 0, receipt ...5655_...:
  all of Bun.startST_parts_range / Bun.stf_parts_range / Bun.stf_upper_support
  depend exactly on [propext, Classical.choice, Quot.sound].
- leanchecker BunUpperSupport (same runner, pinned bin prepended to PATH),
  EXIT 0, receipt 1794004185658675669_leanchecker_UpperSupport.json. The first,
  path-argument invocation (receipt ...70789406682_) failed on module resolution;
  log retained, not a pass. Post-checker source/olean hashes reverified equal.
- results.json updated: credit 0, 52/60 unchanged; unpaid list enumerated.

Next owner entry point: unpaid items in results.json["382297"]["unpaid_full_theorem_list"].
No future-tense items here; everything above is already on disk and verified.
