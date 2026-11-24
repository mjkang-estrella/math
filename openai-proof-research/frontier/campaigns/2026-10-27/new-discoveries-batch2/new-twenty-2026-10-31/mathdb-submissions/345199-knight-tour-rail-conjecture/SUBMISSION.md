# MathDB 345199: The Rail Conjecture for knight's tours

- Problem: https://mathdb.com/p/345199
- Source: Ian Parberry, “Tourneys and the Fast Generation and Obfuscation of Closed Knight's Tours”, arXiv:2001.06044 (2020), Rail Conjecture (Section 4). https://arxiv.org/abs/2001.06044
- Outcome: **REFUTED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `Rail.rail_conjecture_false`, `Rail.rail_conjecture_false'`, `Rail.tours_without_rails`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. Ω is read in the standard computer-science sense (at least c·n for all large n), as Parberry uses O-notation throughout; under the Hardy–Littlewood reading (not o(n)) one would need few-rail tours for every large even n, and the formalized family covers sides ≡ 4 (mod 8) only (the Sol family sides ≡ 0 (mod 12)); the final checker judged that reading implausible here. The construction Lean certifies (zero rails) was found at the Lean stage by a Claude Opus 5.5 lane with a SAT search and is not the 104-rail family the cross-model review read; correctness rests on the kernel. A SAT-found periodic pattern plus a strip-insertion induction is engineering in the classical tradition of knight's-tour constructions; cross-model reviewer: not routine 0.55; final checker about 0.6. Credit: GPT-6.1 Sol for the first refutation, Claude Opus 5.5 for the zero-rail family and the Lean proof. Because GPT-6.1 Sol hit its usage limit, the final check was by a separate Claude Opus 5.5 lane, the same model family as the packager.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Refuted. Parberry (arXiv:2001.06044) conjectured that every closed knight's tour on an n×n board has Ω(n) rails (pairs of edges that can be switched with their complementary pair). For every t ≥ 0 the (60+8t)×(60+8t) board has a closed tour with no rails at all; an earlier family with exactly 104 rails on boards of side 252+24t also refutes it. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let an $n \times n$ knight's tour be a closed knight's tour on an $n \times n$ board, and let a **rail** be the structure defined by the preceding discussion: a pair of edges that can be switched with their complementary pair while preserving vertex degrees. **Rail Conjecture.** An $n \times n$ knight's tour has $\Omega(n)$ rails.

## Summary of the result

The conjecture is false: for every t ≥ 0 the (60+8t)×(60+8t) board has a closed knight's tour with no rails at all. The first refutation, by a GPT-6.1 Sol lane, was a periodic family on boards of side 252+24t with exactly 104 rails, which reduces connectivity to a fixed cycle; a Claude Opus 5.5 review cleared it. The Lean lane (Claude Opus 5.5) certified a stronger construction instead: a periodic template found by a SAT search gives a single 60×60 rail-free tour, and an induction that inserts one 8-column or 8-row period preserves the Hamiltonian cycle and the absence of rails, using two local conditions checked on the reference board. Lean defines the knight graph, the tour as a Hamiltonian cycle (Mathlib's Walk.IsHamiltonianCycle), a rail literally as in the source's Section 4 (an unordered pair of tour edges (v0,v1), (v2,v3) such that (v0,v2) and (v1,v3) are knight moves not in the tour, without a 'parallel' condition, which only enlarges the rail set and so makes zero rails the stronger statement), and the conjecture as ∃ c > 0, ∃ N, ∀ n ≥ N, every closed tour has at least c·n rails; it proves the negation. The SAT output is only data checked in Lean.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
