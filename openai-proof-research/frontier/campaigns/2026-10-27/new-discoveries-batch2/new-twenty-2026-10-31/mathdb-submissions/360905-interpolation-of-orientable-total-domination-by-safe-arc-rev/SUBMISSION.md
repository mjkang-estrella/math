# MathDB 360905: Interpolation of orientable total domination by safe arc reversals: a proof of the Hansen-Lai-Yue conjecture (JCMCC 1999; Anderson-Dravec-Johnston-Kuenzel Conjecture 3.1, arXiv:2311.16307)

- Problem: https://mathdb.com/p/360905
- Source: Hansen-Lai-Yue, J. Combin. Math. Combin. Comput. 29 (1999) 159-181, final conjecture p. 181; Anderson-Dravec-Johnston-Kuenzel arXiv:2311.16307v1 / Discrete Appl. Math. 382 (2026) 48-59, Conjecture 3.1; MathDB 360905
- Outcome: **PROVED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `OrientableTotalDomination.conjecture_true : OrientableTotalDomination.Conjecture, where Conjecture := for every finite vertex type V and Boolean adjacency G with nonempty spectrum and every c with lower G <= c <= upper G, c is in spectrum G; spectrum G is the set of minimum total-dominating-set sizes over valid (positive indegree) orientations of G, with total domination by in-neighbours`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `paper.pdf`
- Lean source: `Lean-packet.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Qualified bounded comparison; not worldwide priority remaining_literature_limits: Chartrand-VanderJagt-Yue, Congr. Numer. 119 (1996) print-only and unread; DAM 382 (2026) version of record unread; Holley-Lai-Yue (Congr. Numer. 1996) unread; bounded citing-work coverage (OpenAlex rate-limited) trust_limits: Prebuilt upstream Mathlib oleans trusted; leanchecker shares the installation not_claimed: Priority; Publication; Any statement about infinite graphs
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Proved: the Hansen-Lai-Yue interpolation conjecture for total domination, restated as Conjecture 3.1 by Anderson, Dravec, Johnston and Kuenzel: in every finite graph that admits a valid orientation, every integer between the smallest and the largest total domination number of its valid orientations is itself the total domination number of some valid orientation. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

The full conjecture for all finite graphs admitting a valid orientation: every integer between dom_t(G) and DOM_t(G) is the total domination number of a valid orientation.

## Body (paste into the MathDB body field)

Use the written proof in this folder: paper.pdf. The complete Lean source is in Lean-packet.zip.
