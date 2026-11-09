# MathDB 352827: partial formal handback

Status: incomplete; zero accepted credit; root decides. The requested unconditional theorem `mathdb_352827 : ¬ SchrijverUnitGap` is not proved. The packet proves `mathdb_352827_conditional` assuming exactly the following explicit Lean propositions:

```lean
def LowerCertificateBridge : Prop :=
  (SG 27 12).Connected ∧ ∃ a b, 8 ≤ (SG 27 12).dist a b

def UpperCertificateBridge : Prop :=
  (SG 28 12).Connected ∧
    ∀ a b, ∃ p : (SG 28 12).Walk a b, p.length ≤ 6
```

Completed: literal Finset-subtype graph definitions, integer-valued unit-gap statement, Mathlib diameter bridges, conditional refutation, Bool mask validity with soundness, Bool label and parent checkers with soundness, walk induction for lower distances, parent-walk construction and connectivity. Concrete mask validity checks and validation results are described in results.json after replay.

The own compressed-coordinate generator independently recomputes both target graphs, all rotation representative trees, complete distance labellings and explicit witnesses. It cross-checks every label in the review certificates. These computations are not substituted for Lean proofs.

Next round:

1. Prove that gap-compressed enumeration exhausts literal stable Finsets, and prove the bitmask encode/decode bijection below 2^n. Cardinality alone is not an enumeration completeness proof.
2. Prove rotations act as graph automorphisms of the literal graph and align rotation of masks with the Finset action.
3. Generate small separate kernel decision modules for each local label or parent check; aggregate their proved soundness using the completed generic lemmas. The existing JSON contains all needed parent and depth data.
4. Transfer one spanning tree to prove connectivity for each graph; transfer the n=27 label and explicit pair to LowerCertificateBridge; transfer all n=28 representative parent trees to UpperCertificateBridge.
5. Remove the conditional endpoint's two hypotheses, then conduct fresh full replay and independent statement-fidelity review. Exact diameter equalities are optional; the bounds 8 and 6 suffice.

No r=2 theorem is used. No git, child agents, shared edits, uploads, external messages, network requests or browser tabs were used. Sources and other lanes remain read-only. The generic process wrapper was copied from nut-formal-r5p/scripts/run_capped.py after reading it; mathematical generation/checking code is this lane's own. An early attempt imposed a 6 GiB virtual-address cap and failed to map an existing mathlib file; subsequent runs use the required sampled private RSS cap. Failed build logs are retained. Early brief/source read-only shell calls preceded the cap wrapper; all Lean and numerical processes used resource caps.
