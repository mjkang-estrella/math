# crown-vnumber-formal-pi-r4 CHECKPOINT

Updated: 2026-11-06 (r4, in progress — NOT final)

## Status: IN PROGRESS — all five modules 0..Cut compile strict; classification/endpoint NOT written

## Compiled modules (strict `-DwarningAsError=true`, exit 0 receipts in `receipt/`)
| module | src sha256 | olean sha256 | receipt |
|---|---|---|---|
| CrownVGraph | 8e5e3195bd7c72a1 (identical to r3) | build/CrownVGraph.olean | 1793951444425546364 |
| CrownVCount | bd236fddbb423b03 (identical to r3) | build/CrownVCount.olean | 1793951444619483932 |
| CrownVSide  | cfcaf195fa7dd34e (identical to r3) | build/CrownVSide.olean | 1793951444815052738 |
| CrownVAlg   | 01e65104c89fd9b3 (identical to r3) | build/CrownVAlg.olean | 1793951445029868730 |
| CrownVCut    | b475fd55b46b6cad | d6e4e2520a488db0... (see below) | 1793952189458248906 |

CrownVCut r4 repair record (root integration r3 listed 36 errors, exit 1, 3 `sorry`):
- `Submodule.sub_mem` takes the submodule as FIRST explicit arg (r3 passed proofs only).
- `Finset.notMem_empty` / `Finset.notMem_erase` / `Finset.mem_univ` have EXPLICIT
  arguments; bare-name uses were Pi-vs-Prop mismatches.
- `mixKeep` final insert lacked the `Finset` tail; now 4 vertices + `∅`.
- `famCut` erases from `(Xside n)`/`(Yside n)`, not `n.erase`; mixed arm `mixKeep i j`.
- Family cases bound via `case name k =>`; every case goal first rewritten to the
  concrete cut by new `rfl`-lemmas `famCut_*`/`famPrime_*` (avoids reliance on
  match reduction inside elaboration).
- All three r3 `sorry`s (mix case) replaced by real proofs: both-kept uses the
  kept-set edge, killed-X uses `minor_mem_Pc_left`, killed-Y `minor_mem_Pc_right`.
- No `sorry` token in code (only the docstring mention). Exit 0, 0 errors.

## Frozen verification
- frozen-inputs.json: 313/313 sha256 verified BEFORE any mathematical input read
  (0 missing, 0 mismatch). Re-verify after handback planned.

## Proven so far (CrownVCut content)
- `Fam n` six-constructor index; `famCut`, `FamPrime = Pc (famCut f)`.
- `minor_mem_Pc_left/_right` (killed-endpoint minors), `minor_mem_Pc` from CrownVAlg.
- `inl/inr_notMem_mixKeep`, sdiff membership helpers.
- `minor_mem_FamPrime`: every crown edge minor lies in every family prime
  (inclusion `J ⊆ P_τ` for all six families).

## Remaining (unproved; next worker continues here)
1. CrownVClass: `Cutset` per paper Def 2.2 (T=∅ or every t∈T cut vertex of
   G[(V∖T)∪{t}]); classification Cutset T → ∃ f, famCut n f = T (only ∅, X, Y,
   X−a_i, Y−b_i, V−{a_i,b_i,a_j,b_j} occur; mixed is symmetric i,j).
2. CrownVSep: exact-separator lemma (paper 3.1) on the six-family intersection
   + irredundance/incomparability; radicality of J or a direct colon route.
3. Multihomogeneous component + retraction/contraction (paper 4.1, 4.2).
4. Degree≤3 exclusion per family (paper 5.1, 5.2, 6.1, 6.2, 7.1, 7.2) — all
   fields, char 2 included; support computations on actual monomials.
5. Quartic witnesses per family (paper section 8) with EXACT colon at every P_T.
6. Assembly `VIs (Pc T) 4` for every Cutset T (paper 9 / Thm 1.1), via the
   classification bridge.
7. Endpoint audits, negative controls, leanchecker, fresh extracted replay,
   SUMMARY/PROOF/final manifest.

Full endpoint NOT complete. No certificate claims. credit 0.

## Runner
scripts/run.sh + check.sh as r3 (exit propagation, 120s CPU/140s wall kill+reap,
AS 12GiB, affinity 0,1, sampled group RSS guard 6GiB, MALLOC_ARENA_MAX=2).
Probe receipts: 1793951613399345078 (signature probe), logs kept.

## Update (r4 session 2): CrownVCut repaired + CrownVClass founded
- CrownVCut: exit 0, 0 errors, src b475fd55b46b6cad..., olean d6e4e2520a488db0...
  (full repair record above).
- CrownVClass NEW: exit 0, src ed0204e2b5192007..., olean 0f300e1f80d3bab5...
  Contains: sameC_eq_or_step (path head-decomposition via core
  Relation.ReflTransGen.cases_head), sameC_eq_of_forall_not_sEdge,
  `VCut S t` (cut vertex of G[S∪{t}], path form; component-count equivalence
  documented, not yet proven), `Cutset T` (paper Def 2.2 verbatim).
  Note: needs `Mathlib.Data.Fintype.Sum` for `Fintype (Fin n ⊕ Fin n)`; without
  it `Finset.univ (V n)` fails to synthesize (probes 1793953332308942719,
  ...47445094, ...5131213536).
- frozen-inputs.json re-verified AFTER: 313/313.
- Signature probes confirmed: Submodule.sub_mem (submodule first), Finset.notMem_empty
  /notMem_erase explicit args, Ideal.mul_mem_left/right arg orders.

## Still remaining (precise)
1. Classification theorem: Cutset T -> ∃ f : Fam n, famCut n f = T. Hard part:
   extract crossed pair from `VCut (univ∖T) (a p)` (path hits a_p, split into
   S-path segments), then global case bash on survivor index sets
   A=X∩S, B=Y∩S. Known answer: (A,B) = (∅,all),(all,∅),({i},all),(all,{i}),
   ({i,j},{i,j}) plus T=∅. Key sub-lemma: b_q,b_r SameC in S iff reachable
   via A-alternating path; isolation arguments via sameC_eq_of_forall_not_sEdge.
2. Then per family: VIs (FamPrime f) 4 requires separator lemma + degree bounds
   + witnesses (see results.json remaining_bridges).
