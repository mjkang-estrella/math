# SUMMARY — r12 update-lower lane (sealed)

One small pure-update lemma, really compiled, really kernel-checked, sealed.

- `Bun.stepU_lower_closed` in `src/BunStepLower.lean` (imports `BunState`; existing
  `stepU`/`sval` used as-is): if `u` bounds both input finsets and `u <= m`, then any
  `k` selected by `sval sigma (stepU m R S x y z)` satisfies `u <= k`.
- Build: exit 0 under runner caps (wall 809 ms, CPU 0.751 s, peak group RSS ~1.7 GiB).
  receipt/1794008524687485694_lean_BunStepLower.json
- Axioms: exactly [propext, Classical.choice, Quot.sound].
  receipt/1794008635916000062_audit_stepU_lower_axioms.log:
  'Bun.stepU_lower_closed' depends on axioms: [propext, Classical.choice, Quot.sound]
- leanchecker on module BunStepLower: exit 0.
  receipt/1794008668703256235_checker_bunsteplower_mod.json
- Post-checker hashes identical to build receipt:
  source 54a3573910df26b0e30c3aee458e5a505fc7a1e3acc068ff58bc75c31a975934
  olean  a2d7ee4c34f5297e655af0aa67c69227a68877fcb01c19c9ec6ceeb1c3b520d4
  log    abe0c3280bf76b64d6262987d674f9c27c8fb2fff721e735c336b8b76615dbdd
- Frozen inputs 657/657 before and after; bootstrap receipt preserved.
- Credit 0 for 382297; campaign 52/60 beyond 39 prior, unchanged.
- Everything beyond this one helper remains unpaid; see CHECKPOINT.md for the
  explicit unpaid list. No future-tense claims: all artifacts above are on disk now.
