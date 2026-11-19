# MathDB 372486: Nian–Tsujie–Uchiumi–Yoshinaga limit conjecture for q-deformed graphic arrangements

- Problem: https://mathdb.com/p/372486
- Source: Tongyu Nian, “A generalization of q-deformation of graphic arrangements to simplicial complexes”, arXiv:2601.06546 (2026). (https://arxiv.org/abs/2601.06546)
- Outcome: **REFUTED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoint `QArr372486.Refute.ntuy_conjecture_false`; axioms limited to propext, Classical.choice, Quot.sound; independently extracted and replayed from `LEAN-SOURCE-APPENDIX.md`.
- Written proof: `PAPER.md` (independently reviewed, no theorem-affecting gaps).
- Novelty: bounded literature and registry review only; no worldwide-priority claim. User may overrule. Revisit if a published graph-case refutation predating 2026-11-17 is found.
- Produced with AI assistance (GPT-6.2 Sol and Claude Opus 5.5 investigators, independent AI review); not human peer reviewed.


## Summary (paste into the MathDB summary field)

Refuted: the polynomiality clause of the Nian-Tsujie-Uchiumi-Yoshinaga conjecture for q-deformed graphic arrangements. Some simple graph on 33 vertices has, over the prime fields, characteristic values of its q-deformed arrangement given by no polynomial in q and t; the witness lies in an explicit family of 2^26 graphs and is identified only existentially. The limit clause alone is not addressed. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $G=([[200~\ell], E)$ be a simple graph on $\ell$ vertices, and let $\mathcal{A}_G^q$ be its $q$-deformation of graphic arrangement. Write $\chi(\mathcal{A}_G^q,t)$ for its characteristic polynomial and $\chi(G,t)$ for the chromatic polynomial of $G$. **Nian–Tsujie–Uchiumi–Yoshinaga conjecture.** The characteristic polynomial $\chi(\mathcal{A}_G^q,t)$ is a polynomial in $q$ and $t$ satisfying

$$
\lim_{q\to 1}\frac{\chi(\mathcal{A}_G^q,q^s)}{(q-1)^\ell}=\chi(G,s).
$$

This conjecture proposes that the chromatic polynomial is recovered from the characteristic polynomial of the $q$-deformed arrangement in the limit $q\to 1$.

## Summary of the result

MODEST_BOUNDED (close call): the polynomiality clause of the NTUY conjecture fails for a graph witness; Glynn seven-arc prior covers the simplicial analogue only, no public graph proof found. MathDB 366210 is an alias of the same endpoint and earns nothing separately.

The complete proof is in `PAPER.md`; the complete Lean source is in `LEAN-SOURCE-APPENDIX.md`.

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
