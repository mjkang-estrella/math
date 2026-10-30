# Algebra lane discovery and formal results

Scope: only this lane; no shared indexes, commits, other lanes, or external posts were changed. Two distinct MathDB question IDs have complete algebraic outcomes below. They are **not two newly solved open problems**: one is an independently proved algebraic assertion, and one is a formal certificate of a previously published counterexample mechanism. Count each source question once, irrespective of its number of lemmas. No PDF was produced.

## 1. MathDB 366458 — four fusion properties for arbitrary ground sets

- UUID: `8e281476-1a49-4899-9c80-9a26f780eec0`.
- [MathDB question](https://mathdb.com/p/366458); [API](https://mathdb.com/api/posts/8e281476-1a49-4899-9c80-9a26f780eec0).
- Primary source: Gatica and Bustamante, *σ-Sets and σ-Antisets*, [arXiv:2501.00047v1](https://arxiv.org/html/2501.00047v1), Definitions 1.2, 1.4, 1.8, 1.12; Theorem 1.6; Conjecture 3.2. The later [Qeios v2](https://www.qeios.com/read/FWQK6T.2) also retains Conjecture 3.2.
- Exact task: for every A⊆N, show closure of the integer space under fusion, a unique two-sided identity, a unique two-sided annihilating inverse for every element, and commutativity.
- Outcome: all four assertions hold for every ground type, without a finiteness hypothesis. A signed subset is a disjoint pair (P,N). Its inverse is (N,P), and fusion is
  `((P\M)∪(Q\N), (N\Q)∪(M\P))` for inputs (P,N),(Q,M).
- Full written proof and source-encoding discussion: [proof.md](sigma-fusion-366458/proof.md).
- Full certificate: [SigmaFusion.lean](sigma-fusion-366458/formal/SigmaFusion.lean), especially `generated_is_fusion`, `generated_space_exact`, and `conjecture_3_2`. All four quantified claims are bundled in the final theorem. `translation_not_injective` and `nonassociative_at_nonempty` clarify that the four claims do not give a loop in the usual quasigroup sense.
- Coverage limit: this proves the complete four-part algebraic conjecture using the source's explicit signed-set/fusion semantics. It does not build a foundational model of the paper's nonstandard σ-set class theory. That foundational task is neither assumed as a custom axiom nor claimed.
- Prior-solution check: the retrieved MathDB API had zero solutions/replies/formalizations. Targeted live web search found the original and Qeios version retaining the conjecture, not a general proof. This is a limited search, not a worldwide-priority assertion.
- Duplicate: MathDB **318649** (UUID `99eaf732-34f3-4873-a3c7-141afe38f55a`) asks the same four properties from arXiv:0906.3120. It is recorded as a related duplicate, **not counted again**.

## 2. MathDB 373182 — continuous nonlinear solution of the Matkowski equation

- UUID: `c483bf58-1787-4351-ac80-a7d1c8831aaf`.
- [MathDB question](https://mathdb.com/p/373182); [API](https://mathdb.com/api/posts/c483bf58-1787-4351-ac80-a7d1c8831aaf).
- Primary source: Tibor Kiss, *A Counterexample to Matkowski's Conjecture for Quasi Graph-Additive Functions*, [arXiv:2602.15548v1](https://arxiv.org/html/2602.15548v1), equation (1), the introduction's Matkowski conjecture (attributed to Remark 8/Conjecture 2 of Matkowski), Proposition 1 and **Corollary 1**.
- Exact equation: `f(f(-x)+x)=f(-f(x))+f(x)` for every real x. The proposed classification requires linearity on each half-line, with further slope restrictions.
- Outcome: `f(x)=min(max(x,0),1)` is continuous, solves the equation at every real x, and has no representation by two half-line slopes, even with all restrictions on the slopes removed. The complete counterexample refutes the proposed classification, rather than just a restricted subcase.
- Full proof: [proof.md](matkowski-373182/proof.md). Certificate: [Matkowski.lean](matkowski-373182/formal/Matkowski.lean), theorem `continuous_nonlinear_counterexample`.
- **Prior art/status correction:** MathDB's retrieved API says `open` and has no replies, but its own cited primary paper explicitly disproves the conjecture. Our example is an elementary instantiation of Kiss's Corollary 1 with slope zero on the negative half-line. The contribution is a complete formal certificate and explicit worked example, **not a new disproof**. The certificate also avoids relying on the possibly unintended source condition that the two slopes differ.

## Screening and exclusions

The archived API lists cover all 982 algebra-tag records, all 154 inequality-tag records, all 31 functional-equation records, and selected number-theory pages. Many algebra records are encyclopedia theorems marked solved. These are not candidate new outcomes.

- **364540**, Briggs polynomial inequalities: rejected as an open discovery. The exact primary source arXiv:2408.16185v1, introduction after equations (1) and (2), explicitly attributes existing proofs to Bränden and Fan–Wang. MathDB's open label is stale.
- **372794**, coefficient positivity of h(t,a;r): exact API already contains a full positive-generating-function proof posted by Shivam Patel on 2026-08-20. Do not assert a new proof/discovery from this lane.
- **333392**, quadratic-form arithmetic functional equation: exact statement read; no elementary general-k proof obtained. Not counted.
- **322631**, cyclic analytic functional equation: exact statement read; analytic cyclicity hypotheses make an elementary algebra certificate unsuitable. Not counted.
- **352508**, converse generalized-binomial inequality: exact statement read; no full real-exponent proof obtained. Not counted.
- Matrix and graph questions were excluded as assigned elsewhere.

## Verification

Both packages reuse the premagic certificate's pinned build/audit pattern. Lean is 4.34.1; mathlib revision is `d13f23b723b8a846827a245b89c10fc7d3f11612`; all transitive dependency revisions are checked against `pins.json`. Each fresh build removes stale local object files, treats warnings as errors, prints every local definition/theorem type and its axiom dependencies, and permits only `propext`, `Classical.choice`, and `Quot.sound`. No `sorry`, custom axiom, or `native_decide` occurs in either proof file. Both complete builds passed; see each `formal/build/audit.json` and `Checks.log`.

Reproduce from repository root:

```sh
python frontier/campaigns/2026-10-25/twenty-proof-algebra-lane/sigma-fusion-366458/formal/rebuild.py
python frontier/campaigns/2026-10-25/twenty-proof-algebra-lane/matkowski-373182/formal/rebuild.py
```

The scripts also accept explicit `--lean-bin` and `--mathlib-packages` arguments. Their defaults locate the supplied workspace caches; fresh network bootstrap was not tested. Source snapshots and retrieval hashes are in `sources/`.
