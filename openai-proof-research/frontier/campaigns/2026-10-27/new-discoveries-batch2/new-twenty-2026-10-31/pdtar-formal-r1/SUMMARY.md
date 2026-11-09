# MathDB 353203 — incomplete formalization

No acceptance or credit is claimed. Root decides. The full literal iff endpoint has not been proved. The delivered theorem `PDTAR.mathdb_353203_conditional` is explicitly conditional on six unproved Props in `PDTAR/Remaining.lean`.

Completed source modules are Defs, Basic, FortDuality, KstFamily, Core (partial core results only), Remaining (Prop specifications), Endpoint (conditional assembly), and Fidelity. They include literal simultaneous power-domination rounds, monotonicity and PD up-closure, finite stabilization, fort duality, fort facts F1–F3, K1–K3, fort-covering and two-intersection lemmas, pair forts, and the sum-type partition/no-isolation bridges. Each module compiled strictly before moving to the next. None of the uncompiled predecessor skeletons was imported.

The pair-fort theorem is general for arbitrary ordered parts A,B, requiring card A at least 3 and card B at least 2. Mirror statements are obtained with `completeBetween_swap`. Core Lemma 1(b), the cross-degree lemmas 3–5, completeness Lemma 6, and independence Lemma 7 remain unformalized. The general reduction and all uniqueness/non-uniqueness small cases remain unformalized. The work is a reusable partial certificate, not a formal solution of the conjecture.

The source zip, resumable replay script, manifest, statement correspondence, resource receipts, declaration audit, expected-failure controls and extracted build are delivered. See results.json for final validation counts and exact source hashes. The audit has 100 local declarations including generated/private declarations; it finds zero safety or axiom-budget violations. Permitted transitive axioms are only propext, Classical.choice and Quot.sound.

Next-round plan:

1. Prove no-isolation from the completed fort-covering/two-intersection lemmas. Add neighbourhood helper lemmas for F1 and F2 using exact set inclusion, and derive cross_nonempty and no_cross_leaf from pair_fort, symmetrically.
2. Formalize the three steps of PROOF.md Lemma 5 separately: the hub structure from cross-degree 1, its mirror, and the pair-counting conclusion card A = card B = 3. Derive cross-degree at least 2 away from (3,3).
3. Formalize Lemma 6 with four distinct vertices on the large side and two pair-fort applications, then Lemma 7 to close CoreRemaining. Keep helper modules below the per-process caps.
4. Formalize the generic up-closed-family reduction: co-singleton PD sets (already proved), TAR degree/order invariance, induced cube intervals, irrelevant-set flips, rank preservation, and the co-singleton vertex bijection propagated down by intersections. Then transport H along that bijection to prove ReductionRemaining. The survey supplies the full proof; no published assertion is currently a Lean theorem here.
5. Discharge EdgeRemaining, StarsRemaining, ThreeThreeRemaining and TwoRemaining. Use source arguments or structural finite cases, never enumeration of all six-vertex graphs. Prove the K(2,t) added-edge counterexample PD-family equality and non-isomorphism; handle K(1,2) against K3; transport the swapped orientations.
6. Replace the conditional endpoint with a theorem named mathdb_353203 with precisely the requested signature, rebuild from a fresh source archive, repeat all audits and add a negative K(2,3)-uniqueness control. Request independent statement-fidelity review through root, without self-acceptance.
