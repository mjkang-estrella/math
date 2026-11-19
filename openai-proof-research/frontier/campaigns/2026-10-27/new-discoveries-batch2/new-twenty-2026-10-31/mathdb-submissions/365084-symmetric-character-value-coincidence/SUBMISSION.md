# MathDB 365084: The finite-cycle character-value coincidence conjecture for symmetric groups

- Problem: https://mathdb.com/p/365084
- Source: David A. Craven, “On the irreducible character degrees of symmetric groups and their multiplicities”, arXiv:2410.01726 (2025). (https://arxiv.org/abs/2410.01726)
- Outcome: **PROVED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoint `LiteralColoring.finite_cycle_character_value_coincidence`; axioms limited to propext, Classical.choice, Quot.sound; independently extracted and replayed from `LEAN-SOURCE-APPENDIX.md`.
- Written proof: `PAPER.md` (independently reviewed, no theorem-affecting gaps).
- Novelty: bounded literature and registry review only; no worldwide-priority claim. User may overrule. Katriel 1997 (ScienceDirect S0012365X96000994) and the Taylor & Francis final of Craven are unread; withdraw if either proves the joint coincidence.
- Produced with AI assistance (GPT-6.2 Sol and Claude Opus 5.5 investigators, independent AI review); not human peer reviewed.


## Summary (paste into the MathDB summary field)

Proved: for every d >= 0 and k >= 1 there is an explicit bound such that for all larger n, the symmetric group S_n has k distinct irreducible complex characters whose values agree on every permutation moving at most d letters. Applied to a fixed finite set of test permutations, this gives the character-value coincidence conjecture recorded as Craven's Conjecture 3.5; the indexing partitions may share one hook multiset. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $X$ be a finite set of permutations, and let $k\geq 1$ be an integer. For a permutation $g\in S_n$, its cycle type is the multiset of lengths of its cycles.

**Finite-cycle character-value conjecture.** For all sufficiently large $n$, there exist $k$ distinct irreducible characters of $S_n$ whose values on permutations $g\in S_n$ coincide for all $g$ whose cycle type belongs to $X$.

The conjecture asks for arbitrarily large collections of distinct irreducible characters that cannot be distinguished by their values on any prescribed finite set of cycle types. The source contrasts it with an adaptive procedure for determining characters from values and gives computational examples, but leaves the conjecture open.

## Summary of the result

MODEST_BOUNDED (close call): uniform joint high-order moment construction giving k distinct irreducible characters of S_n agreeing on bounded support for all large n; Craven 2007 and Xiong supply ingredients but no inspected body gives the joint coincidence.

The complete proof is in `PAPER.md`; the complete Lean source is in `LEAN-SOURCE-APPENDIX.md`.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
