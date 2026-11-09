# SUMMARY — flat-balance-refutation-formal-pi-r4 (MathDB 352972)

Status: **COMPLETE** (kernel-checked endpoint, audited, clean replay done).
Credit: 0 (awaiting independent review + root acceptance). Campaign: 52/60 unchanged.

## Result

Literal Lean refutation of MathDB 352972 ("balanced-graph conjecture for flat
graphs", source: Hossein Teimoori Faal, arXiv:2112.09721, Conjecture 2 / eq.(14)
notion of `D_clique`): the universal statement over all finite simple graphs
is FALSE, witnessed by the finite simple graph K_{3,3} on `Fin 3 ⊕ Fin 3`:

- `FlatBalance.not_flat_balanced_conjecture : ¬ FlatBalancedConjecture` where
  `FlatBalancedConjecture := ∀ (V : Type) (hV : Fintype V) (G : SimpleGraph V),
  @Flat V hV G → @Balanced V hV G` (finite simple graphs; own `SimpleGraph`
  structure with `adj_symm`/`adj_irrefl`).
- `FlatBalance.flat_not_balanced_exists` — the existential counterexample
  (`K33`, flat, not balanced).
- `K33_flat` (every edge in ≤ 2 triangles; in fact 0), counts
  `c_0=1, c_1=6, c_2=9, c_k=0 (k≥3)`, parity sums `6/10` (c_0-convention) and
  `6/9` (positive-index), discrepancies `Int.natAbs(6-10)=4 > 1` and
  `Int.natAbs(6-9)=3 > 1`; `K33_not_balanced`.

No planarity/no-isolated-edge extra hypotheses; no polynomial/answer-proxy; all
bridges (finite support/range/cardinality, parity split, Nat→Int natAbs) explicit.

## Verification (all under provided capped runner, pinned Lean 4.34.1 / mathlib d13f23b7, -j1 -M3500 -DwarningAsError=true)

1. Repair of the four saved production error clusters (250; 258–260; 318–320;
   390) in the draft `ad57bf76…`; strict build + kernel checker EXIT 0.
2. Endpoint (sums/discrepancies/negation/∃) added; strict build EXIT 0 with zero
   diagnostics; kernel checker EXIT 0.
   src `4a4ca90e72d35f516ca4f84f9ab3fcb1e49527f5625278ed67ba2cabbeed889d`;
   olean `aeb27a12…`.
3. Audit `audit/Audit352972.lean`: `#print axioms` — every endpoint-relevant
   theorem depends exactly on `[propext, Classical.choice, Quot.sound]`
   (K33 structure lemmas: `[propext]` only); definitional bodies printed.
4. Negative controls `audit/Controls352972.lean` (9): nonvacuity (6 vertices,
   real edges), exact-count sensitivity (≠8, ≠0), convention separation
   (4 ≠ 3, ≠4, ≠0), pointwise refutation `¬(Flat K33 → Balanced K33)`,
   contrapositive shape, flatness provable. All kernel-checked.
5. Source safety: no `sorry/admit/axiom/unsafe/partial/native_decide/extern/
   implementedBy` in lane source.
6. Clean extracted source-only replay (`extracted/`): identical source SHA,
   empty-build strict rebuild EXIT 0 and kernel check EXIT 0 at pins; imports
   pinned upstream only.

Frozen set verified before AND after: 791/791, no mismatches.

## Artifacts

- `src/FlatBalance.lean` (+ pristine frozen copy `input/pristine-FlatBalance.lean`, draft SHA preserved in TASK/results)
- `build/FlatBalance.olean`, `extracted/{src,build}`
- `audit/Audit352972.lean`, `audit/Controls352972.lean` + logs/, receipt/ (13 receipts, hashes in `SHA-MANIFEST.json`)
- `results/352972.json`, `SHA-MANIFEST.json`, `CHECKPOINT.md`

## Exclusions / non-goals

No network, git, installs, child agents, preview tools; protected lanes
(code-loop-sets-formal-pi-r5, polynexus-count-repair-formal-pi-r7, older formal
bodies) untouched beyond the frozen hash list. Independent formal/source review
and root acceptance remain separate; no self-credit taken.
