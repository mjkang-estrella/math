# MathDB 369595: The edge-redundant rigidity conjecture for complete graphs in $\ell_\infty^d$

- Problem: https://mathdb.com/p/369595
- Source: James Cruickshank, Sean Dewar and Derek Kitson, “Algebraic connectivity in normed spaces”, arXiv:2508.00134 (2025). (https://arxiv.org/abs/2508.00134), Conjecture 5.4
- Outcome: **REFUTED**
- Formal verification: Lean 4.34.1 with Mathlib, kernel-checked; endpoints `CDK.not_edgeRedundantlyRigid_K8`, `CDK.not_conjecture`, `Review369595.cdk_source_refuted`, `CDK.K9.k9_edgeRedundantlyRigid`; axioms limited to propext, Classical.choice, Quot.sound; sources extracted from `LEAN-SOURCE-APPENDIX.md` and rebuilt independently.
- Written proof: `PAPER.md`
- Novelty: bounded literature and registry review only; no worldwide-priority claim. Computer-assisted: the unsatisfiability certificate is checked by a checker proved sound in Lean and evaluated in the kernel; the generated certificate modules are reproducible from the scripts and inputs in this folder. The journal version of the source (Linear Algebra Appl. 739, 2026) is unread. The extension of the positive result to n >= 10 is proved on paper only.
- Produced with AI assistance and independent AI review; not human peer reviewed.

## Summary (paste into the MathDB summary field)

Refuted. The complete graph K_8 is not edge-redundantly rigid in three-dimensional l-infinity space, so the conjecture of Cruickshank, Dewar and Kitson that K_n is edge-redundantly rigid in l-infinity^d for all n >= 2d+2 fails at its first open case d = 3, n = 8. The proof is computer-assisted: a reduction to colour classes of the framework, seven forbidden four-point patterns, and an unsatisfiable propositional instance whose certificate is checked inside the Lean kernel. K_9 is edge-redundantly rigid in the same space. The proof is formally verified in Lean 4 with Mathlib and kernel-checked with only the standard axioms propext, Classical.choice and Quot.sound. It was produced with AI assistance and independent AI review, with a bounded literature search and no human peer review.

## Problem statement as recorded on MathDB

Let $d\geq 2$, let $n\geq 2d+2$, and let $K_n$ denote the complete graph on $n$ vertices. A graph is **edge-redundantly rigid** in a normed space if it has a framework that is infinitesimally rigid and remains infinitesimally rigid after deleting any edge. **Edge-redundant rigidity conjecture.** For every $d\geq 2$ and every $n\geq 2d+2$, the complete graph $K_n$ is edge-redundantly rigid in $\ell_\infty^d$.

The preceding proposition rules out $K_{2d+1}$, so the conjecture asserts that the stated threshold is sufficient as well as necessary. The supplied excerpt gives no evidence that the conjecture has been resolved.

## Summary of the result

The complete graph K_8 is not edge-redundantly rigid in three-dimensional l-infinity space: no well-positioned placement of K_8 remains infinitesimally rigid after the removal of every single edge. This refutes the conjecture of Cruickshank, Dewar and Kitson that K_n is edge-redundantly rigid in l-infinity^d for all n >= 2d+2, at its first open case d = 3, n = 8. The proof reduces the property to a condition on the three colour classes of the framework (every colour class meets every cut twice), derives seven forbidden four-point patterns from the geometry, and shows the resulting propositional instance unsatisfiable; the certificate (12,876 steps) is checked inside the Lean kernel by a verified checker. K_9 is edge-redundantly rigid in l-infinity^3 (proved in Lean), and so is K_n for every n >= 10 (proved in the paper only).

## Body (paste into the MathDB body field)

Use the written proof in this folder: PAPER.md. The complete Lean source is in LEAN-SOURCE-APPENDIX.md.

## Certificate files in this folder

`lean/` contains all 20 Lean modules, including the eight generated certificate
modules. `certificate/` contains the hash manifest and regeneration scripts.
Follow the commands in §7 of `PAPER.md` to regenerate the intermediate files
and verify the resulting Lean modules against the manifest.
