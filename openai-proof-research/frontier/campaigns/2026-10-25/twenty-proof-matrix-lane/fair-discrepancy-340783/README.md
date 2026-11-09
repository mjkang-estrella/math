# A full counterexample certificate for MathDB340783

Status: complete Lean certificate of the counterexample, including every positive discrepancy tolerance and every reflexive interpretation of the source's approximate-energy relation. One distinct MathDB question. This is a formal verification of a **previously posted counterexample**, not a new mathematical discovery.

Primary question: [MathDB340783](https://mathdb.com/p/340783/the-fair-discrepancy-propagation-conjecture-for-fully-balanc), UUID `88c8529c-45dc-484e-b014-26cd054e51f0`. Primary paper: Agama and Kibiti, *Balanced matrices*, [arXiv:1810.07542v3](https://arxiv.org/html/1810.07542v3), Definition 3.1, Conjecture 6.6 and Remark 6.7. The exact API response and versioned paper are saved in `../sources/`.

## Statement and proof

For a real matrix, let the row and column energies be the sums of squares, the row mean be the arithmetic mean, and a row be ε-fair when every entry differs from its row mean by less than ε. The question asks whether ε-fairness of one row of a fully balanced matrix forces it for all rows.

Take

```
A = [5 5 5
     1 5 7
     7 5 1].
```

Every row and column energy equals 75, and all entries are positive. The first row has mean 5 and deviations zero. The second row has mean 13/3 and its first deviation is 10/3. Thus ε=1 disproves the implication. For any ε>0, use εA: energies remain identical, the first row remains perfectly constant, and the second deviation is 10ε/3>ε.

## Fidelity of the formal statement

The source uses an unspecified `≈` in Definition 3.1 and an apparent upper-index typo for vertical balance. We neither assign an invented numerical meaning to that notation nor rely on the typo. `ExactBalanced` requires nonzero A and equality of all row energies and all column energies. This is a stronger condition, satisfied by the source's own equality examples. `BalancedWithin` additionally supports every positive absolute energy tolerance. Most generally, `BalancedBy R` accepts any relation R on real energies, and the final theorem works for **every reflexive R**. Thus any interpretation of `≈` that includes equality admits the counterexample. A nonreflexive or otherwise unstated definition is not claimed to be formalized.

`FairRow` quantifies over every column and uses strict `< ε`, matching the source's prose interpretation. Nonzero, positivity, exact energies, row means, all tolerances and the negated universal exact-balance implication are proved, not assumed. The final relation-parametric theorem rules out propagation under any reflexive energy comparison.

## Attribution and novelty limits

The saved MathDB record contains Shivam Patel's counterexample reply `be21f974-e069-4a4c-b446-252e228a1119`, posted 2026-08-22T07:49:47.568226Z, with this same matrix and the scaling observation. It was read before implementation and is the mathematical source for the witness. The local contribution is the full kernel-checked implementation and explicit handling of the undefined approximate relation. MathDB's automatic summary calls the reply unverified; that database label is not a mathematical obstacle to checking it directly. No claim of worldwide novelty or first formalization is made.

## Validation

Run `python3 formal/rebuild.py` from any working directory. It checks Lean 4.34.1 and mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`, the dependency manifest and clean tracked dependency sources, builds into `formal/build`, and audits the type and transitive axioms of every declaration in `formal/Checks.lean`. Only `propext`, `Classical.choice`, and `Quot.sound` are allowed. No proof holes, custom axioms or native decision procedure is used. Precompiled dependency objects and the compiler remain trusted; no claim of rebuilding the dependencies is made.

Paper source is in `paper/main.tex`. No PDF was created. Original local code and prose are available under MIT and CC BY 4.0 respectively; third-party sources retain their original rights.
