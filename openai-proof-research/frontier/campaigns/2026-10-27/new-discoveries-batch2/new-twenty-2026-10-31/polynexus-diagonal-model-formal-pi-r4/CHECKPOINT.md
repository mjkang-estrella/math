# Checkpoint 1 — 2026-11-07 (agent-local, lane-internal)

Lane: polynexus-diagonal-model-formal-pi-r4 (Pi spark/GLM-5.3-Flash-EXL3, high).

DONE
- bootstrap.py EXIT=0 (receipt bootstrap-receipt.json preserved), verify_frozen.py before: 409/409 match, no mismatches.
- Read (runner receipts, unique true exits): literal352496.json, MODEL-AND-BRIDGES.md, NEXT-PI-BRIEF.md, REVIEW.md, root-model-integration.json.
- src/PolynexusDiag.lean: faithful coupled-diagonal model. PCnd (bounds + coupling s+a=r+b), PBlk entry =1 iff common-offset t<=e (PCnd_iff_t), entry dichotomy, occupied common-offset entries, corner, nonzero, full-length B(0,0,n-1) identity entries diag/offdiag + PBlkId matrix equality.
- Strict build check.sh PolynexusDiag: EXIT=0, no warnings (receipt 1794051245215672708, then checker 1794051256445153775 EXIT=0).
- Scoped #print axioms (audit/audit_PolynexusDiag.lean): PBlk none; PBlk_eq_one_iff, PBlkId, PBLK_ne_zero: propext, Quot.sound only. Allowed set.

NEXT
- Module PolynexusSrc: signed source triples, dictionary, injectivity.
- Then PolynexusProd, count modules, final endpoint 120*psi=(n+1)^7-n^7-(n+1)^3+n^3.
