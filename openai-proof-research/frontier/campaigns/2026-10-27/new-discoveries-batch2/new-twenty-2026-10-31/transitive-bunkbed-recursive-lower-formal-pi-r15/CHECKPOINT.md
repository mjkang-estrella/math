# CHECKPOINT r15 — BunLowerSupport DELIVERED (on disk, actual)

Done, verified on disk in this lane:
- verify_frozen before: 759 / 0 mismatches (t=1794012197.6); after: 759 / 0 (t=1794013314.5).
- First mathematical op was check.sh BunLowerSupport on the TASK-written src/BunLowerSupport.lean (no prior source/API inspection, no baseline rebuild): first compile EXIT 1 with exactly 2 application-arity diagnostics (hP.1/hP.2 explicit binder); one targeted edit; recompile EXIT 0, receipt 1794013212058888424_lean_BunLowerSupport.json. Failed receipt+log retained.
- Sealed: receipt/SEALED_BunLowerSupport.json
  source cde925587852254a80e80145db5965a33d81b53471958c6f1678e94c5bed7dfa
  olean  903116caa05c07e330c555f10d93c61ea2f2a438fbf67e6bf861433a479a7068
  log    5bb63fa70a219fa284b4eb48b3f6f05ba52144ad5482056d01e363055cb6ec45
- Scoped #print axioms (same runner/caps), EXIT 0, receipt 1794013299582232650_axioms_LowerSupport.json:
  Bun.stf_lower_parts and Bun.stf_lower_support each depend exactly on [propext, Classical.choice, Quot.sound].
- leanchecker BunLowerSupport by MODULE name under the same runner (env.sh LEAN_PATH, pinned bin), EXIT 0, receipt 1794013303529678951_leanchecker_BunLowerSupport.json.
- Post-checker source/olean/log hashes reverified identical to sealed values.
- ARTIFACTS.json: 12 entries, all sha256 64-hex, INCLUDING receipt-JSON hashes (not self-referential).
- results.json updated: ID 382297, credit 0, 52/60 unchanged; unpaid list enumerated.
- All jobs reaped: every receipt shows true exit, no group members left, no tail masking.

Actual handback: src/BunLowerSupport.lean + build/BunLowerSupport.olean + receipts/logs as above. No future-tense items.
