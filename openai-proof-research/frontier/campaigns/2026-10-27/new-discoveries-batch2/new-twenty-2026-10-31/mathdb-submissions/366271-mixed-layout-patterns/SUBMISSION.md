# MathDB 366271: The forbidden-pattern characterization conjecture for one-stack one-queue layouts

- Problem: https://mathdb.com/p/366271
- Source: David Haun, Laura Merker and Sergey Pupyrev, “Forbidden Patterns in Mixed Linear Layouts”, arXiv:2412.12786 (v1 2024, v2 2026), Conjecture 31 (Conjecture 27 of v1); extended abstract in STACS 2025. https://arxiv.org/abs/2412.12786
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `Pool039.haun_merker_pupyrev_conj31`, `Pool039.sq_characterization`, `Pool039.onePage_characterization`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. Modest result: the new argument for part (i) is about a page and a half of elementary interval geometry plus a finite enumeration, and part (ii) is routine; the cross-model reviewer puts 0.60 on a specialist calling part (i) not routine. ProbXiv (HTTP 402), MathSciNet and zbMATH were not checked. No second cross-model lane read the finished Lean: root compared the final theorem and every definition it uses with the endpoint the Claude Opus reviewer had written (identical), and the GPT-6.1 Sol final check compared the definitions and all 20 pattern tables with the source's Figure 19.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Proved. Both forbidden-pattern characterizations of Haun, Merker and Pupyrev's Conjecture 31 (arXiv:2412.12786) hold: an ordered matching with a fixed layout has a 1-stack 1-queue layout iff it avoids the 12 patterns of Figure 19a, and a one-page mixed layout iff it avoids the 8 patterns of Figure 19b. The key step: every matching without a 1-stack 1-queue layout contains one with at most six edges. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let an ordered matching have a fixed non-separated layout. A **$1$-stack $1$-queue layout** uses one stack and one queue, and a **mixed layout on $1$ page** uses one page that is a stack or a queue. **Forbidden-pattern characterization conjecture.** The ordered matching admits a $1$-stack $1$-queue layout if and only if it avoids the 12 patterns depicted in Figure 19a of the source, and admits a mixed layout on one page if and only if it avoids the 8 patterns depicted in Figure 19b.

## Summary of the result

Both characterizations of Conjecture 31 hold for every finite ordered matching. The content is part (i): with the vertex order fixed, deciding a 1-stack 1-queue layout is a 2-SAT problem, whose contradiction cycles can be arbitrarily long, so 2-SAT alone gives no finite obstruction set. The proof shows that for intervals, three-edge forcing configurations plus propagation decide colourability, and that the geometry of intervals shortens every contradiction path to at most one link. Hence every matching without such a layout contains one with at most six edges, and an enumeration of the 11,465 matchings with at most six edges gives exactly the 12 patterns of Figure 19a. Part (ii) is routine (a failure needs a crossing pair and a nesting pair, at most four edges; also the source's Lemma 27). Lean defines ordered matchings on natural-number endpoints, layouts as the source does, and containment as an injective edge map preserving every endpoint comparison; the figure patterns are literal endpoint tables; no size cap enters the statement.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
