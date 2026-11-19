# MathDB 354228: Symmetric-shell labellings of complete full trees with even branching: proof of the even case of the Bača-Semaničová-Feňovčíková-Lai-Wang local antimagic conjecture (Fundamenta Informaticae 185 (2022), Conjecture 6.1)

- Problem: https://mathdb.com/p/354228
- Source: Bača-Semaničová-Feňovčíková-Lai-Wang arXiv:2204.04479v2 / Fundam. Inform. 185 (2022) Conjecture 6.1 (even case); MathDB 354228
- Outcome: **PROVED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `Antimagic.Round7A.mathdb_354228 : ∀ {V} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj] (t n : ℕ), 2 ≤ t → Even t → 1 ≤ n → FullTree G t n → IsLeast (spectrum G) (numLeaves G + 1) ∧ chiLA G = numLeaves G + 1; with the model companion Antimagic.Round7A.even_case : IsLeast (spectrum (tree t n)) (t^n + 1); Labeling = edge bijection onto 1..|E|, weight = incident label sum, IsLocal = adjacent weights distinct, chiLA = least colour count, FullTree = rooted full t-ary tree certificate with all leaves at depth n`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `paper.pdf`
- Lean source: `source.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Qualified bounded comparison; not worldwide priority remaining_literature_limits: Sarath-Prajeesh 2023 (diameter-3 and certain diameter-4 trees) closed access and unread; could overlap at most depth two; Premalatha-Arumugam-Lee-Wang (Local antimagic chromatic number of trees - I) closed access and unread; bounded arXiv and OpenAlex screens; Google Scholar, MathSciNet and zbMATH not consulted trust_limits: Prebuilt upstream Mathlib oleans trusted; leanchecker shares the installation; the audit covers the 1,414 local declarations (axioms and metadata), not a full upstream closure inventory; the depth-two binary case is the source's Figure 5 and the depth-two t >= 4 case is built from the source's Lemmas 2.2 and 2.9 (credited as such) not_claimed: The odd case (proved in the source); Priority over the unread closed-access tree papers; Publication
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Proved: the even case of the local antimagic chromatic number conjecture of Baca, Semanicova-Fenovcikova, Lai and Wang for complete full trees. Every complete full t-ary tree with even t >= 2 has local antimagic chromatic number equal to one more than its number of leaves, t^n + 1 at depth n, with exactly that many vertex sums; the endpoint also covers every finite graph carrying the structural full-tree certificate. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

Bača, Semaničová-Feňovčíková, Lai and Wang, Conjecture 6.1, even case: for every complete full t-ary tree T with t ≥ 2 even, χ_la(T) = l + 1. Proved for every even t ≥ 2 and depth n ≥ 1, for every finite graph carrying the full-tree certificate.

## Body (paste into the MathDB body field)

Use the written proof in this folder: paper.pdf. The complete Lean source is in source.zip.
