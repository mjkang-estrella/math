# MathDB 345190: The unlabelled bridge-addable fragment-size conjecture

- Problem: https://mathdb.com/p/345190
- Source: Colin McDiarmid, “Connectivity for an unlabelled bridge-addable graph class”, arXiv:2001.05256 (2020). (https://arxiv.org/abs/2001.05256), Conjecture 3
- Outcome: **REFUTED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `BridgeFragment.mathdb_345190`, `BridgeFragment.mathdb_345190_real`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. The formalized class differs in detail from the one in the discovery proof (the paper proves the formalized one; an independent referee re-derived every inequality). The first stage starts near 2^86 vertices, so no direct numerical confirmation at true size is possible; scaled-down copies were checked. The same class refutes the sibling record MathDB 345191 (Conjecture 4), which is not claimed separately. Bounded literature search; both papers citing the source treat the unlabelled conjectures as open.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Refuted. There is a single decomposable, bridge-addable class of graphs, nonempty at every order, for which the mean fragment size under uniform sampling of unlabelled n-vertex members is unbounded. This contradicts Conjecture 3 of McDiarmid, arXiv:2001.05256. The class is built from a staged family of bridgeless cyclic-layer graphs with very many isomorphism types. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $\mathcal A$ be a class of graphs that is **bridge-addable**, meaning that adding an edge between vertices in distinct components preserves membership, and **decomposable**, meaning that a graph belongs to $\mathcal A$ if and only if each of its components does. For a graph $G$, define its **fragment size** by

$$
\operatorname{frag}(G)=|V(G)|-\max\{|V(C)|:C\text{ is a component of }G\}.
$$

Let $\tilde{R}_n \in_u\tilde{\mathcal A}$ be sampled uniformly from the unlabelled graphs in $\mathcal A$ on $n$ vertices. **Unlabelled bridge-addable fragment-size conjecture.** For each such graph class $\mathcal A$, there is a constant $c_{\mathcal A}$ such that, for each positive integer $n$,

$$
\mathbb E[\operatorname{frag}(\tilde{R}_n)]\leq c_{\mathcal A}.
$$

The labelled analogue has a uniform expectation bound, while the source gives an unlabelled example showing that the expectation can grow linearly for a particular class; the conjectured bound remains open in general.

## Summary of the result

McDiarmid's Conjecture 3 (the expected fragment size of a uniformly random unlabelled n-vertex graph from a decomposable, bridge-addable class is bounded by a universal constant) is false: there is one fixed isomorphism-invariant, decomposable, bridge-addable class of graphs, with members at every positive order, whose mean fragment size over isomorphism classes of n-vertex members is unbounded in n. The class consists of graphs whose bridgeless pieces are single vertices or members of a staged family of cyclic-layer graphs with very many isomorphism types; the bound obtained is of order t^2/6 at stage t. The first stage begins at about 2^86 vertices, so the effect is invisible at any computable size (below 2^85 vertices the class is exactly the forests).

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.
