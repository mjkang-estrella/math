# r15 SUMMARY — crown-coordinate-map-formal-pi (Pi GLM5.3Flash, no children)

Status: **sealed auxiliary compiled module `CrownVCoordMap`; no acceptance; credit 0; campaign 52/60 unchanged.**

## What was done
1. `bootstrap.py` run first (receipt `bootstrap-receipt.json`, preserved, never rerun).
2. `verify_frozen.py before` → 768/768, 0 mismatches (frozen-before.json).
3. First mathematical operation: wrote `src/CrownVCoordMap.lean` and ran supplied `check.sh CrownVCoordMap`. Two failed attempts (true receipts preserved), then strict success.
4. Sealed source/olean/log/receipt hashes immediately; no expansion past the seal.
5. Scoped audits, same capped runner (`runner.py`, CPU120s/wall140s/devguard130/AS12GiB, affinity ≤2, MALLOC_ARENA_MAX=2):
   - `#print axioms` on all 8 declarations via `audit/CrownVCoordMapAxioms.lean` → exactly `[propext, Classical.choice, Quot.sound]`, exit 0.
   - `leanchecker` kernel recheck of the sealed olean → exit 0 (needed PATH prepinned for its internal `lean` spawn; three failed probes' receipts preserved).
6. `verify_frozen.py after` → 768/768, 0 mismatches (frozen-after.json).

## The module (namespace CrownV, imports CrownVAlg only)
- `coordKill (T : Finset (V n)) : PolyRing n K →+* PolyRing n K` — genuine variable-killing endomorphism built from `MvPolynomial.eval₂Hom` with coefficient hom `MvPolynomial.C` and variable function `q => if q.1 ∈ T then 0 else X q`.
- Theorems: action on `C` (fixes coefficients), action on `X q` (if-form), fixes `X (v,b)` for `v ∉ T`, action on existing `xx`/`yy` (if-form), and annihilation `coordKill (xx v) = 0` and `coordKill (yy v) = 0` for `v ∈ T`.
- All `n : Nat` (incl. 0), all `T` (incl. ∅, full), all `CommRing K` characteristics; noncomputable via allowed instance/choice path only.

## Sealed hashes (sha256)
- src/CrownVCoordMap.lean `a7b8f67a535953d5aba5313f3a24b4a028691266fa157db2cfa29a0d34ea7206`
- build/CrownVCoordMap.olean `cc94d8451c1eacd592284677dedf2f2cd6e7f03574afe9cad09ade430bc7e8fa`
- true compile receipt `receipt/1794000388003300228_lean_CrownVCoordMap.json` (exit 0, wall 1051 ms)

## Honest limits / exclusions
- NO kernel equality (neither inclusion), NO primality, NO polynomial induction, NO fullside/local-v — all unpaid; exact list in `results.json → 369163.unpaid_remaining_theorems`.
- r14 uncompiled sorry-draft NOT imported, compiled or copied; historical text only under `references/`.
- Dev LEAN_PATH import reuse only; no fresh extracted all-source replay; baselines read-only, not rebuilt.
- r8 state-bounds and Sol r356 untouched (no read/hash/glob/poll). No network/git/shared writes.

Evidence: `ARTIFACTS-MANIFEST.json`, `results.json` (ID 369163), `CHECKPOINT.md`, receipts and logs under `receipt/` and `logs/`.
