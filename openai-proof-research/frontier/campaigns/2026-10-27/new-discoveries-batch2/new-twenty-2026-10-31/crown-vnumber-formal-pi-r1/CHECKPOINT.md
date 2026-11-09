# CHECKPOINT — crown-vnumber-formal-pi-r1 (implementation lane)

## Verified working (this session)
- Toolchain: `scripts/env.sh` (LEAN_PATH), `scripts/check.sh <Mod>` (caps: 2 cores, 6GiB RSS — OK for targeted imports; full `import Mathlib` EXCEEDS 6GiB cap — use targeted imports only).
- **Lean 4.34.1 syntax quirks learned**:
  - Module docstring BEFORE imports is an ERROR ("invalid import... beginning of file"). Imports first, always. `public import` used by mathlib sources; plain `import` works for our modules.
  - `∀ x y ∈ s,` multi-binder membership notation FAILS to parse → write `∀ (x y : V n), x ∈ s → ...`.
  - String interp in run_cmd: `s!"..."` (with bang).
  - Axiom audit: `Lean.collectAxioms name : CoreM (Array Name)` (returns the array directly).
  - `Finset.card_fin` doesn't close `Finset.univ.card = k` → `by simp`.
  - Dot-notation on `SameC` abbrev can resolve to wrong lemma (SameC.trans recursion); use explicit `Relation.ReflTransGen.trans` / name lemmas `SameC.trans'`.
  - `open Classical` at top; comp/comps/ccnt are `noncomputable` (filter needs DecidablePred of a Prop).
- `src/CrownVGraph.lean` — COMPILES (build/CrownVGraph.olean). `V n = Fin n ⊕ Fin n`, `vx/vy`, `cadj` (a_i~b_j iff i≠j), `SEdge s`, `SameC s := ReflTransGen (SEdge s)` (path in s), `comp s a` (finset), `comps s`, `ccnt s`, `comp_self/subset/mem_comps`, `comp_eq_of_sameC`, `SameC.symm/trans'/single`, `cadj_symm`.
- `src/CrownVCount.lean` — COMPILES. **`ccnt_le (f : V → Fin k) hedg hconn : ccnt s ≤ k`** (blocks edge-closed + pairwise-connected via SameC) and **`ccnt_le_lower (x : Fin k → V) hx hdiff : k ≤ ccnt s`** (pairwise ¬SameC) — plus `notSameC_comp_ne`.
- Axiom audit (tmp/axaudit.lean pattern): 10 CrownV defs, 0 nonstandard axioms.

## The 8 cut-point cases (math, verified by hand — implement next)
Notation: T ⊆ V, s := Tᶜ (as Finset), s⁺ := insert v s. Cut(v): ccnt s > ccnt s⁺. n ≥ 4.
| # | T | v | ccnt s | ccnt s⁺ | cut? |
|---|---|---|--------|---------|------|
| 1 | X=all a_i | a_j | n (isolated b's) | 1 (star via a_j) | YES (n≥2) |
| 2 | X | b_j | n | n (b_j already present) | no |
| 3 | X∖{a_i} | a_j | 1 (Y + a_i star) | 1 | no |
| 4 | X∖{a_i} | b_j | 1 | 1 | no |
| 5 | Y=all b_i | b_j | n | 1 | YES |
| 6 | Y | a_j | n | n | no |
| 7 | Y∖{b_i} | * | 1 | 1 | no (both v) |
| 8 | A∪pair(A), |A|=n−2 (A⊆X-indices; T removes a_i,b_i for i∈A plus nothing else) | any v∈T | see below | see below |

Case 8 detail (the M_{ij}-family complement): T = {a_i,b_i : i∈A} ∪ ... — CHECK exact form against root ORDINARY-PROOF.md P_{A∪A'} prime / Liwski Thm 3.3 form `A ∪ {i+1 : i ∈ A}, |A| = n−2` (source vertices 2i−1,2i ↔ a_i,b_i; "i+1" = the partner b-vertex). s = two survivors p,q (indices ∉ A... n−2 removed ⟹ 2 survivors? NO: |A|=n−2 removed pairs leaves 2 X and 2 Y? — recheck: T removes a_i AND b_i for i∈A? Then s has 2 a's + 2 b's: comps = 2 (the two matched pairs, if p≠q pairs are (a_p,b_p)?? crown has NO a_p b_p edge! pairs a_p~b_q... — VERIFY against source before coding: the claim is ccnt s = 2, ccnt s⁺ ∈ {1,2}, cut iff v makes it 1.) **This case needs source re-reading first.**

## Implementation pattern per case (machine already built)
- Upper: give f : V → Fin k; `hedg` from `cadj` case analysis; `hconn` needs explicit SameC witness chains (`SameC.single` + `trans'`).
- Lower: witnesses x i + `hdiff` via: SameC into Y-only region forces reflexivity (no Y–Y edges: `cadj (inr _) (inr _) = False`) etc.
- Useful helper to add: `sameC_of_edges`-style chain builder; `SameC` in Y-set is refl-only lemma.

## Remaining pipeline (after cases)
1. `CrownVCases.lean`: 8 case lemmas, each `Theorem cut/cut-not` in form: hypothesis T = ... (as Finset eq) → cut-criterion value.
2. Cut-point family ⇔ source definition: `P_T(G) ⊇/⊆` via colon-ideal membership characterization; equivalence theorem `vnumber_eq` (least degree of homogeneous f with (J_G : f) = P_T) — source def in crown paper v2 `/tmp/crownv2.txt` P_T def + root proof sec on localv.
3. Degree-4 witnesses: f = specific binomials per source §; colon = P_T exact; homogeneous degree 4; no deg<4 (lower bound via valuation/monomial-order argument from source).
4. `localv_{P_T}(J_G) = 4` main thm + audits (`audit/` dir, leanchecker per module, no sorry etc).

## Lane hygiene state
- frozen-inputs.json: 79/79 verified earlier this session (re-verify at end).
- Files created: src/CrownVGraph.lean, src/CrownVCount.lean, src/Smoke.lean, scripts/*, logs/*, build/*.olean/.ilean, tmp/.
- Nothing outside lane touched.
