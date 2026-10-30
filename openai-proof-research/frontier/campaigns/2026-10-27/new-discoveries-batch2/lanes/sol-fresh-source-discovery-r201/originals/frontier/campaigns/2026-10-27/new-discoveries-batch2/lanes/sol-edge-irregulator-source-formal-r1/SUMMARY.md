# INCOMPLETE — source refutation not delivered

Solo implementation in this lane only. Credit **0**; campaign **7/37** unchanged. Root's ordinary MATH, substantive and bounded current-prior/source adoption is an input, not a formal conclusion. No manuscript, acceptance or ledger edits.

## Checked component

Five mathematical modules compile under pinned Lean4.34.1, `-j1 -M2700 -DwarningAsError=true -DautoImplicit=false`:

- `Source.lean`: actual `SimpleGraph.deleteEdges`, retained-subgraph degrees, unordered `Sym2` edge finsets, and valid deletion subsets. Deleting every edge proves existence. `minimum` is `Nat.find`, with attained witness and minimality. `minimum_le_iff` proves the real-bound equivalence; `source_minimum_equivalence` closes minimum versus existential deletion formulations on all `Fin n` graphs.
- `Gadget.lean`: literal graph on `Unit ⊕ (Fin t × Fin 6)`, exactly the stated edges, symmetry and looplessness, `vertex_card t : Fintype.card (Vertex t) = 6*t+1`, and `graph_connected t : (graph t).Connected`. These hold without a t≥2 premise; no t=1 deletion optimum is asserted.
- `Edges.lean`: injective indexing by `Fin t × Fin 8` of actual unordered edges, surjectivity onto the graph edge finset, and `edge_card t : (graph t).edgeFinset.card = 8*t`.
- `Boundary.lean`: closed kernel-`decide` 256-state diamond/path certificates and their combined cost inequality. These quantify over all eight retained bits, so both choices of cx are covered. No hub degree enters. These remain local arithmetic certificates, not an arbitrary-graph deletion lower bound.
- `Degrees.lean`: exact retained-neighbor finsets for every private vertex and arbitrary deletion finset, generic three-point filtered cardinality, and `degree_a` identifying the actual retained degree of a with the mask expression. The five other private degree formulas were attempted but are absent from the checked component.

The literal target definition printed in `logs/AuditPrint.log` is:

```lean
EdgeIrregulator.SourceClaim : Prop :=
  ∃ c : ℝ, 1 ≤ c ∧ ∀ (n : ℕ) (G : SimpleGraph (Fin n)),
    G.Connected → ∃ S, EdgeIrregulator.Valid G S ∧
      (S.card : ℝ) ≤ (G.edgeFinset.card : ℝ) / 3 + c
```

**There is no primary refutation endpoint.** In particular `¬ EdgeIrregulator.SourceClaim` is not proved or implied by a component PASS.

## Exact remaining obligations

1. Finish the actual retained-degree identifications for b,c,d,x,y and derive `DiamondOK (mask S i)` and the xy constraint from `Valid (graph t) S` for arbitrary S.
2. Relate each local arithmetic deletion cost to the cardinality of the corresponding subset of actual edges, then sum disjoint charges. The absent global lower theorem is:
   `∀ (t : ℕ) (S : Finset (Sym2 (Vertex t))), Valid (graph t) S → 3*t ≤ S.card`.
3. Define and verify the deletion witness ab,ad,xy in every block, including its cardinality3t, retained hub degree t, and all five retained degree-pair inequalities for t≥2. Consequently prove the absent exact theorem:
   `∀ t : ℕ, 2 ≤ t → minimum (graph t) = 3*t`.
4. Transport this genuine graph on `Vertex t` to the source vertex model `Fin (6*t+1)`, preserving connectivity, edges, deletion cardinality and actual degrees/minimum.
5. Use Archimedean t>3c and the exact edge count to close the unconditional primary endpoint `source_refutation : ¬ SourceClaim`, with no residual gadget or graph premise. That endpoint needs its own full replay and audit after implementation.

No conditional stand-in for the missing primary endpoint is advertised. Remaining independent review/paper/root acceptance gates are untouched.

## Sources and provenance

Read candidate `PROOF.md` in full, preliminary and r2 reviews, root ADOPTION, ancestor/batch AGENTS and campaign context. All79 original candidate files were hash/membership checked before copying and again after implementation, as were all79 private copies: `freeze-before.json`, `freeze-after.json`. Work used own ordinary copies under `inputs/`.

Publisher Conjecture1 and definition: Bensmail et al., *Graph Irregularity via Edge Deletions*, WALCOM2026, DOI10.1007/978-981-95-7127-7_24, printed356/physical4. PDF SHA256 `574aaf95e9d6e94273d2ebc15704bb1209537625d7e59b5282d9a130efb1ceae`. Copied visible page was inspected; it says unequal retained degrees. Text extraction drops the negation stroke and is not used to change the definition. No new prior-art clearance or global priority claim.

Lean binary SHA256 `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`; absolute path and all package pins in `pins.json`. Mathlib revision `d13f23b723b8a846827a245b89c10fc7d3f11612`. All9 packages (mathlib plus8) and the binary were checked; replay independently rechecks them and1057 actual imported package olean hashes. Package revisions were read from local metadata without any Git command.

## Replay and audit

`edge-irregulator-component.zip` is deterministic with fixed ZIP timestamps/modes and no oleans or other compiled artifacts. It contains the successful mathematical sources, audit sources, replay/guard, pins, dependency hashes and frozen inputs. `manifest.json` binds the entries; `archive-sha256.txt` binds the archive. Failed probes remain outside the component under `probes/` with sources, logs and resource receipts.

`verification-fresh/` is a fresh extraction, initially without own compiled artifacts. Its `replay-receipt.json` has status **COMPONENT_REPLAY_PASS_SOURCE_INCOMPLETE**, not source PASS. All five modules and both audits are rebuilt serially. `OriginAudit` exhaustively enumerates89 unique actual module-origin declarations, including private/generated declarations, crosschecks module-data membership, prints full actual types and transitive axioms, and rejects every unsafe/partial/axiom flag. `AuditPrint` executes literal `#check` and `#print axioms` for all89 names using exact kernel identifiers, including numeric private names. Its sole linter exception is `linter.auxLemma false`, necessary because the audit deliberately references generated auxiliary declarations. The axiom union is exactly propext, Classical.choice, Quot.sound; all89 unsafe/partial/axiom flags are false. No mathematical source uses proof holes, added axioms, unsafe code, native_decide or unchecked executable proof.

To reproduce into a previously nonexistent destination, run `python3 replay.py edge-irregulator-component.zip /absolute/path/to/fresh-destination`. Run with the supplied `replay_guard.py` if external helper supervision is wanted; the extraction and its generated outputs must remain in this lane.

All compile receipts in `logs/` and extracted `verification-fresh/logs/` record limits and sampled RSS. Lean memory cap2700MiB, process-group RSS2800MiB, CPU210s/wall230s, nominal45ms sampling, approved AS∞ for Lean only. Python helpers AS512MiB/groupRSS512MiB, BLAS1, CPU210s/wall230s and40ms sampling. No resource cap was raised; no resource guard kill occurred. Unsampled transients and scheduler delays are not excluded. One failed helper startup tried to reset an inherited hard AS limit and was rejected; the failed receipt is preserved and the helper was corrected. Lean elaboration/import/linter failures and the degree-c heartbeat timeout are preserved, not represented as successful proofs. No git operations, children, browser/contact/network actions, external posts, shared writes or other-lane writes occurred.
