# MathDB 366521: 3-extendability conjecture for optimal 1-embedded graphs on the Klein bottle

- Problem: https://mathdb.com/p/366521
- Source: https://mathdb.com/p/366521/3-extendability-conjecture-for-optimal-1-embedded-graphs-on; https://arxiv.org/abs/2501.02726v2
- Outcome: **REFUTED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `Klein366521.conjecture25_false`, `Klein366521.conjecture25_false_of_euler_zero`, `IndependentReplay.weak_topology`, `IndependentReplay.expanded_source_counterexample`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `PAPER-v1.md`
- Lean source: `klein-extendability-accepted-proof-packet-20261115-v1.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Root bounded SUBSTANTIAL editorial adoption, independent BORDERLINE preserved: the specific reflected quotient makes the separating equator cut both parity-compatible and saturated by an admissible3-matching, leaving two odd components. Canonical augmentation and elementary odd-component obstruction alone do not furnish this exact compatibility. A full source-native routine specialization is explicitly developed in the contrary review; no authenticated older whole-target counterpart or decisive routine-subsumption theorem was established. No new framework/unbounded counterfamily is required for a finite exact refutation, and no worldwide priority is certified. not_claimed: independent substantial-credit verdict; cleanprocess; worldwideabsence; unread publisher/companion fidelity; universal Euler-invariance theorem; homological Eulercomparison; separate global manifold instance; audit upstream truth
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Refuted: the 3-extendability conjecture for optimal 1-embedded graphs on the Klein bottle, Conjecture 25 of the source. The reflected-rectangle quotient Klein bottle carries a connected simple graph with 12 vertices, 8-regular with 48 edges, optimal and 1-embedded with Euler characteristic 0, in which the three-edge matching joining vertex pairs 1-5, 3-9 and 7-11 extends to no perfect matching, the residual vertices forming two odd triangles. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

Refutes the exact source Conjecture25 that every8-regular optimal1-embedded graph on the Klein bottle is3-extendable. The literal reflected rectangle quotient [0,4]x[0,3], (0,y)~(4,y), (x,0)~(4-x,3), carries a connected simple12vertex8regular48edge graph with actual continuous injective edge arcs, good transverse1-embedding and canonical valid CW Euler characteristic0, hence48=4*12-4*0. Matching{{1,5},{3,9},{7,11}} has three edges,12>=8 and no perfect matching contains it: residual vertices form two odd triangles. Even-order witness and literal surface/drawing predicates; no torus-only theorem or odd-order loophole.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER-v1.md. The complete Lean source is in klein-extendability-accepted-proof-packet-20261115-v1.zip.
