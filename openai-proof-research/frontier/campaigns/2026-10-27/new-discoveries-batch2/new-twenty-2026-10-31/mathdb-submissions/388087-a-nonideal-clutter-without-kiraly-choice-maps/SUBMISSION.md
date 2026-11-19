# MathDB 388087: A nonideal clutter without Kiraly choice maps

- Problem: https://mathdb.com/p/388087
- Source: (not stated in record)
- Outcome: **REFUTED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `KiralyClutter.counterexample and KiralyClutter.kiraly_conjecture_false`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `manuscript.pdf`
- Lean source: `proof-packet.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. qualified bounded prior-art and subsumption review; no worldwide-priority certification remaining_literature_limits: Lutolf–Margot catalogue full body unread; chronology does not exclude old subsumption; publisher versions not independently audited where author manuscripts used; current MathDB solution/comment state inaccessible under inherited403; finite citation/search coverage; later unindexed/inaccessible papers unknown not_claimed: minimal nonideality as Lean theorem; smallest counterexample; new underlying Lehman matrix; publication or journal peer review; new credit for typo correction
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Refuted: the direction of the Kiraly choice-map characterization claiming that every nonideal clutter admits choice maps. An explicit clutter of eleven triples on eleven elements has a fractional extreme point in its covering polyhedron, hence is nonideal, yet no pair of choice maps on the clutter and its blocker satisfies the membership and intersection-exclusion condition; nonexistence is by a finite branching certificate. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

11-element nonideal clutter has no p,q on clutter and full blocker satisfying membership and singleton-intersection exclusion; refutes intended nonideal-implies-choice direction

## Body (paste into the MathDB body field)

Use the written proof in this folder: manuscript.pdf. The complete Lean source is in proof-packet.zip.
