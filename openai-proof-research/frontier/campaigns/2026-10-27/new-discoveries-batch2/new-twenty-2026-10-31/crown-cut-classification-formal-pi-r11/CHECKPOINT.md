# Checkpoint r11 — complete (Pi GLM5.3Flash high, no children)

## Frozen verification
- `verify_frozen.py before`: count 616, mismatches [], stamp 1793983082.8822806.
- `verify_frozen.py after`: count 616, mismatches [], stamp 1793987802.8691204.

## Compiled modules (all true exit 0, receipts with source/olean/log SHA; latest successful per module)

| module | stamp | source sha256 (16) | olean sha256 (16) |
|---|---|---|---|
| CrownVFamCutB | 1793983095862326977 | 9db7895dc5ce9a59 | 185327627317d700 |
| CrownVConv1 | 1793986706841447880 | 6c8cb46d3e5bd12d | 381091dc822f6f90 |
| CrownVConv2 | 1793987452816963126 | 67cdd18506abf04b | 7bb9487fe4fc3622 |
| CrownVConv3 | 1793987757647490354 | 865d74288a8fb0bf | 2af00e2a9dbd8331 |

Full hashes in `results.json`. Current on-disk sources match the receipt hashes
(verified). Failed intermediate attempts keep their own receipts; only
latest-success counts. No processes left running.

## Mathematical content (all kernel-checked, exit 0, warningAsError)

1. `CrownVFamCutB.cutsetFam_of_valid (hn : 4 ≤ n) (f) (hf : FamValid n f) :
   Cutset (famCut n f)` — forward direction; root's repairs compiled unchanged
   on first attempt; `FamValid` = True on zero/fullX/fullY/delX/delY, `i ≠ j` on mix.

2. `CrownVConv1` (tools, on r9 bridge):
   - `cutWitness`: cut-set membership ⇒ two `univ∖T`-neighbors nonconnected (via `vcut_witness`).
   - `notSameC_Xcommon/_Ycommon`: a nonconnected same-side pair has no common
     opposite-side neighbor in D (else 2-path) — the only force used of `¬SameC`.
   - `exists_third`, `sameC_refuteX/_Y`: four-step rerouting paths
     `b_k-a_m-b_r-a_k-b_m` and mirror, killing two-survivor shapes (n ≥ 4).

3. `CrownVConv2` (shape finalizers): `famEq_fullX/_delX/_fullY/_delY/_mixed` —
   explicit T-descriptions ⇒ `∃ f, FamValid n f ∧ famCut n f = T`; mixed uses
   `inl/inr_mixKeep_mem` from B. No redefinition of Cutset/Fam anywhere.

4. `CrownVConv3`:
   - `validFam_of_cutset (hn : 4 ≤ n) {T} (hT : Cutset T) :
      ∃ f, FamValid n f ∧ famCut n f = T` — full converse, all n ≥ 4, arbitrary T,
      empty case included (`zero`), no enumeration, no extra hypotheses. Case
      split: T meets X / Y / both; both ⇒ witness index sets chain to
      X-survivors = Y-survivors = the 2-element witness pair ⇒ mixed shape;
      one-sided ⇒ 4-branch survivor count with refutation of the 2-survivor case.
   - `cutset_iff_fam (hn : 4 ≤ n) (T) : Cutset T ↔ ∃ f, FamValid n f ∧ famCut n f = T`
     — combines both directions via `cutsetFam_of_valid`.

## Axiom audit
`audit_axioms.lean` (lane file; run once with the lane LEAN_PATH, taskset 2 cores,
timeout 140, MALLOC_ARENA_MAX=2; exit 0): `validFam_of_cutset`, `cutset_iff_fam`,
`cutsetFam_of_valid`, `vcut_ccnt_iff`, `cutWitness`, `famEq_mixed` all depend
exactly on `[propext, Classical.choice, Quot.sound]`. No sorry/admit/new axioms/
unsafe/native_decide anywhere in the new sources.

## Scope of this handback / unpaid obligations (credit 0; 52/60 unchanged)
Done here: mixed-family completion (B), full converse classification, combined iff,
axiom audit of the six declarations above.
NOT done (exact remaining debt for the full 369163 endpoint):
- No EMPTY-source extraction and strict rebuild of all modules without old paths.
- No independent statement-fidelity review; no checker replay of A/B/Conv* beyond
  the axiom audit above; no negative-control runs.
- Actual J/Pc structure, all-field arbitrary-homogeneous degree 0..3 exclusion
  (incl. char 2), quartic exact colon witnesses, full VIs4 — all unpaid.
- No paper, no manifest audit of module-origin/private inventory, no
  opaque-aware body/safety pass, no unabridged type inventory.
