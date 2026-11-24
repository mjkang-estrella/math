# MathDB 346587: The half-length uniqueness conjecture for bi-roots

- Problem: https://mathdb.com/p/346587
- Source: Giuseppa Castiglione, Gabriele Fici and Antonio Restivo, “Primitive Sets of Words”, arXiv:2005.10668 (2020). https://arxiv.org/abs/2005.10668
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `BiRoot.half_length_biroot_unique`, `BiRoot.weighted_primitive_intersection_add_three`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. The journal text of the source (Theoretical Computer Science, 2021) is unread; its abstract still states only the square-root uniqueness result. One reviewer (GPT-6.1 Sol) left eligibility in doubt until the journal body and a complete list of citing papers are read; root then obtained the citing list from Semantic Scholar (one work in two versions, Echi, Khalfallah and Kroumi on primitive words with non-primitive product, a different question; saved as public-claim-100/s2-citing-346587.json), and the cross-model reviewer had read Castiglione and Holub 2020 on 3-maximal monoids, which gives no length bound. The Lean theorem is for finite alphabets, the source's setting; the statement for an arbitrary alphabet follows by restricting to the letters used, a reduction not in Lean. Cross-model confidence: mathematics 0.85, not routine 0.75, overall 0.7. No second cross-model lane read the finished Lean; the file with the literal definitions is byte-identical to the one that reviewer read.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved. A primitive word has at most one bi-root (primitive pair generating it) whose total length is less than half the length of the word; more strongly, two distinct bi-roots of a primitive word w have total length at least |w| + 3. This settles the half-length and additive conjectures of Castiglione, Fici and Restivo, Primitive Sets of Words (arXiv:2005.10668). The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $w$ be a primitive word. A **bi-root** of $w$ is a primitive pair $\{x,y\}$ whose concatenations include $w$. **The half-length uniqueness conjecture.** The word $w$ has at most one bi-root $\{x,y\}$ such that

$$
|x|+|y|<\frac{|w|}{2}.
$$

The preceding theorem proves the analogous uniqueness statement under the stronger bound $|x|+|y|<\sqrt{|w|}$. The supplied text presents the half-length bound as a problem related to the first conjecture, but gives no resolution.

## Summary of the result

A primitive word w over a finite alphabet has at most one bi-root of at most half its length: if X and U are primitive pairs (two-element bases of 2-maximal submonoids) that both generate w, and twice the total length of each is below |w|, then X = U. This is the half-length uniqueness conjecture of Castiglione, Fici and Restivo, who proved uniqueness only under a square-root length bound. The proof establishes their additive conjecture in a stronger form: two distinct primitive pairs generating the same primitive word have total length at least |w| + 3. It folds the two generator graphs, glues them along the path of w into a graph of rank at most 3, shows that in rank 3 a cycle of the incidence graph would give w a period, so that the incidence graph is a forest and the bound follows by counting, and treats the remaining case by recoding w through first returns and a weighted induction on length that changes the alphabet. Lean states primitive words, generated submonoids, 2-maximality and primitive pairs literally.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
