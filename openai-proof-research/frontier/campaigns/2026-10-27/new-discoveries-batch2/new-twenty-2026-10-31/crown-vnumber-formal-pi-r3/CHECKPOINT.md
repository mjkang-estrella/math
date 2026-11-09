# crown-vnumber-formal-pi-r3 CHECKPOINT

Updated: 2026-11-06 (in-progress, NOT final)

## Status: IN PROGRESS — graph side complete, algebra/classification/endpoint NOT yet written

## Compiled modules (strict warningAsError, exit 0 receipts in receipt/)
| module | src sha256 (prefix) | olean |
|---|---|---|
| CrownVGraph | see audit/src-hashes.txt | build/CrownVGraph.olean |
| CrownVCount | see audit/src-hashes.txt | build/CrownVCount.olean |
| CrownVSide  | see audit/src-hashes.txt | build/CrownVSide.olean |

Notes:
- CrownVGraph restructured from r2 copy: `vidx`/`isX`/`sideX`/`sideY` moved here;
  `cadj` defined componentwise (vidx unequal + opposite sides) instead of a
  2-argument match, so its recognizing iff-lemmas are robust. Semantics identical
  (crown a_i~b_j iff i≠j, opposite sides); r2 Count proofs carry over unchanged.
- CrownVSide fully rewritten; r2 version's failures (defeq matcher, binder/induction
  issues, filter/card, unused-simp) are all gone; new swap/closure/existence API.
- Runner scripts/run.sh+check.sh: real exit propagation, no tail-piping, wall hard-cap
  140s kill+reap group, CPU 120 ulimit, AS 12GiB, affinity from actual mask (0,1 here),
  group-RSS sampled guard 6GiB, MALLOC_ARENA_MAX=2, argv/env/no-secret receipt.

## Frozen verification
- frozen-inputs.json: 240/240 sha256 verified BEFORE any math-input read.

## Remaining (unproved, to be done in this lane)
1. CrownVCut: cut/classification module — components of G−T, cut set structure,
   P_T as actual ideal (kills T-coords + 2x2 minors in completed components),
   identification of the explicit prime family, radical/primality bridge.
2. CrownVAlg: MvPolynomial ring on V, edge-generated J, homogeneity, total degree,
   exact colon J:I, homogeneous-minimum local v definition.
3. Degree-4 witness + no smaller homogeneous exact-colon witness (all fields, n≥4, char2).
4. Endpoint theorem + audits + negative controls + SUMMARY/PROOF/results.

Full endpoint NOT complete. No certificate claims. credit 0.

## Update (CrownVAlg compiled)
- CrownVAlg.lean exit 0 (-DwarningAsError=true): PolyRing/xx/yy/minor, edgeFinset+mem_char,
  edgeMinorSet/J, minor_mem_J(+_of_cadj), coordGens/compMinors/Pc, xx/yy/minor_mem_Pc, Pc_le,
  elcolon/ExactColon, homogeneity lemmas (thomog_X/mul/sub/add/smul/totalDegree), VWitD/VIs.
- src sha256 CrownVAlg 01e65104c89f...; olean b6b86ff8b98d...
- Key API facts pinned: Finset.filter is Prop+DecidablePred (classical + noncomputable);
  mem_homogeneousSubmodule (d, poly) with sigma R implicit; homogeneousSubmodule sigma R explicit;
  Ideal.neg_mem_iff takes I explicit; K-mvars in PolyRing-typed statements need ascription.
- Remaining: CrownVCut (cut classification), CrownVMain (witness/lower bound/endpoint).
