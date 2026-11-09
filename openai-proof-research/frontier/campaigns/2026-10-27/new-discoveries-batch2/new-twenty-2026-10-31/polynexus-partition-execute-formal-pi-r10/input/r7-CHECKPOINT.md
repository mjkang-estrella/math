# CHECKPOINT — polynexus-count-repair-formal-pi-r7 — 2026-11-07 (in progress)

## Completed this lane (all exits are true runner receipts under receipt/)

1. bootstrap.py — printed full AGENTS/TASK chain. receipt bootstrap-receipt.json.
2. verify_frozen.py before — {"count": 756, "mismatches": []}. frozen-before.json.
3. Entry reader r7: root-r6-integration.json + r6-latest-Count-failure.json
   (receipt 1794072969984917365) and r6 Count failure log + pristine Count source
   (receipt 1794073005806949864).
4. FIRST NEW PROOF WRITE (before any API/probe/recon/baseline): targeted repair of
   src/PolynexusCount.lean. Prior failed SHA 8eb81266258a2a34...248fe8 (exit 1,
   9 diagnostic sites). Repaired source SHA
   139d65a061a5888369abb837f6acfdd9dd682466920ac6b524cfec34b0c6d73d.
   Repairs: membership destructuring via Finset.mem_image/.1 (raw rintro on Finset
   mem fails: Quot.lift not inductive); pair-injectivity via show+Prod.mk.injEq
   (rw of projections into non-beta-reduced goal); duplicate Finset.card_range
   removed; legLin self-reference termination fixed (ih, not legLin m); legSq
   have-chain arithmetic rebuilt with omega/ring closures; rangeOne trailing ring
   removed (rw closes by rfl). Definitions and all theorem statements unchanged.
5. Strict check: receipt 1794077272626330173, exit 0,
   olean SHA 233aa1daf3085d7461005547968289f0973a165d5bf06944312f99e9d2992d3f
   (build/PolynexusCount.olean, own lane).
6. Kernel checker PolynexusCount: receipt 1794077286656136832, exit 0.
7. Axiom audit audit/CountAxioms.lean via audit.sh: receipt 1794078563248470833,
   exit 0. All 9 new declarations (PLegFib, PLegFib_mem, PLegFib_card, PLeg_card,
   rangeOne, legLin, legSq, PNZ_card, PNZ_card_sq) depend only on
   propext, Classical.choice, Quot.sound.
8. Recon (post-repair, per r7 order): input/NEXT-PI-BRIEF.md + literal352496.json
   read (receipt 1794077339241910852); declaration inventory of the six green
   modules (receipt 1794077392603836584); Pairs head read (1794077416053045743).

## Module state

Seven sources in src/, all strict-green in this lane or carried green from r6
recorded receipts (root-r6-integration.json): Diag d6377c54..., Src cf772ca9...,
Prod ffb8a9e7..., Close 9c3ff367..., SrcPrd deb8bae7..., Pairs b3fbc0b6...,
Count 139d65a0... (repaired this lane). Own build contains PolynexusCount.olean
only; the six dependency oleans resolve READ-ONLY from the completed r6 build
per the root DEV exception (env.sh LEAN_PATH), no legacy build writes.

## Remaining unpaid (exact), per NEXT-PI-BRIEF modules 7-10 + closeout

- Module 7: PLeft/PRight zero-pair partition; transposition involution card.
- Module 8: gap bijection; D_n = sum_{e+f<=n-2} (n-e)(n-f)C(n-e-f,2) as card.
- Module 9: evaluation 720D = n(n-1)(n+1)(n+2)(19n^2+19n+6) (equivalently
  4C(n+4,6)+11C(n+3,6)+4C(n+2,6)); 36T^2 = n^2(n+1)^2(2n+1)^2.
- Module 10: additive core 120psi + n^7 + (n+1)^3 = (n+1)^7 + n^3 via
  psi + 2D = T^2; literal 120*psi = (n+1)^7-n^7-(n+1)^3+n^3 for n>=1; n=1 case.
  (Numerically verified: psi_1=1, psi_2=17, psi_3=118 against T^2-2D.)
- Full all-declaration transitive axiom audit incl private/generated bodies;
  negative controls; clean extracted source-only replay (separate env, no
  legacy build path, rebuild all seven from pinned upstream); results/352496.json,
  SUMMARY.md, full receipt/log SHA manifest with terminal self-exclusions;
  frozen-after check. Independent review, manuscript, root acceptance: unpaid.

## Integrity notes

- No unchanged failed recompiles: every check followed a source change.
- r6 lane touched only through its recorded receipt/log/olean hash paths and
  READ-ONLY build oleans; no writes outside this lane.
- Protected lanes code-loop-sets-formal-pi-r5, flat-balance-refutation-formal-pi-r3:
  untouched except frozen hash-only paths.
- credit 0; accepted 52/60 unchanged. No acceptance claimed for anything above.
