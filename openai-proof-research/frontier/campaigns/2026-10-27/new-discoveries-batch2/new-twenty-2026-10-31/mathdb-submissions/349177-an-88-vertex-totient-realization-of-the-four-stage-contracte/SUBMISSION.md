# MathDB 349177: An 88-vertex totient realization of the four-stage contracted nanostar: a counterexample to the Ghanbari-Alikhani nanostar conjecture (arXiv:2012.12492; Math. Gazette 2023)

- Problem: https://mathdb.com/p/349177
- Source: Ghanbari-Alikhani arXiv:2012.12492v1 / The Mathematical Gazette (2023), DOI 10.1017/mag.2023.57, final Conjecture (p. 271); MathDB 349177
- Outcome: **REFUTED**
- Formal verification: Lean 4 with Mathlib, kernel-checked; endpoint(s) `R162.not_conjecture349177 : ¬ R162.Conjecture349177, where Conjecture349177 := ∀ k, 4 ≤ k → ¬ Realizable (nanostar k), Realizable t := ∃ finset A of positive integers with treeGraph t ≃g phiGraph A (vertex set the iterated-totient orbit of A, undirected loopless edges n - phi(n)), and nanostar k the contracted-hexagon dendrimer tree (three copies of arm (k-1); arm (j+1) = two path vertices then a branching vertex with two copies of arm j)`; axioms limited to propext, Classical.choice, Quot.sound.
- Written proof: `paper.pdf`
- Lean source: `proof-source.zip`
- Novelty: bounded literature review only; no worldwide-priority claim. Qualified bounded comparison; not worldwide priority remaining_literature_limits: citing work 'A graph related to the Tau function' (DOI 10.1063/5.0315935) full text unread; Rashid et al. J. Chem. 2020 unread; bounded registry and citing-work screens trust_limits: Prebuilt upstream Mathlib oleans trusted; leanchecker shares the installation; the D_k family is the contracted-hexagon reading of the cited recursion; the source draws only D_2 not_claimed: Realizability of all stages k >= 5; Minimality of the labels; A general realization method; Priority; Publication
- Produced with AI assistance and independent AI review; not human peer reviewed.


## Summary (paste into the MathDB summary field)

Refuted: the Ghanbari-Alikhani conjecture that no nanostar dendrimer grown through four or more stages is a G_phi-graph, the graph of an iterated totient orbit. At stage four, 23 explicit generator sets yield an 88-vertex tree realization of the four-stage contracted nanostar. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Result

Ghanbari-Alikhani final conjecture: no nanostar grown at least four stages is a G_phi-graph. False at stage 4: 23 explicit generators give an 88-vertex orbit tree with centre 1024 isomorphic to D_4.

## Body (paste into the MathDB body field)

Use the written proof in this folder: paper.pdf. The complete Lean source is in proof-source.zip.
