# Independent review: MathDB376980 continuous minimum means

Verdict: PASS as a full counterexample to the literal classification of continuous symmetric means without an added strictness or analyticity hypothesis. No conclusion about a strengthened strict or analytic classification is approved.

Reviewer: parent integrator, independent of the agent who authored the mathematical and formal development. The exact integrated Lean source is unchanged from the author. A fresh isolated pinned audit on this parent copy passed all24 declarations with warnings treated as errors, Lean4.34.1 and the exact dependency revisions; only propext, Classical.choice and Quot.sound occur transitively.

Accepted exact sources:
- formal/InvariantMinimum.lean SHA256 `81ae87c69bd4bd9b40abd7d5cd1010744b2efd66a8e15fa4b7c53d1286b7c838`
- main.tex SHA256 `efda26351d3c9304a6e711e2faac1095e7860b4d5e9a4052e305cf6375368ec5`

## Full mathematical and formal review

The two witness functions are the actual binary and ternary minima on the positive real domains. Continuity is proved on the entire ambient finite real products before restriction; internality uses the actual source minimum/maximum bounds. Values remain positive on positive inputs, so every source substitution is legal. Symmetry quantifies over every permutation of Fin2 or Fin3. The proof does not replace full symmetry by a single transposition. Both source invariance identities, including the precise type1 argument order, hold by nested minimum identities and repeated-entry absorption.

The nonrepresentation conclusion covers the actual inverse arithmetic formulas, with binary denominator2 and ternary denominator3. InverseArithmeticPair explicitly requires inverse cancellation on positive inputs and that each average belong to the generator's image, exactly what a genuine inverse evaluation needs. No monotonicity is required in this enlarged class. The local bridge proves injectivity and both arithmetic conjugacy equations from these inverse formulas; they are not assumed as unsupported properties of an inverse. Applying the binary equation at1,2 forces h(1)=h(2), contradicting injectivity. Thus no generator of any monotone genuine inverse type can represent the pair. The final theorem bundles all mean hypotheses, both symmetries, both identities and the inverse-pair obstruction. It has no missing assumed source bridges.

## Actual primary-source scope

Read Horwitz's original PDF text at Section1 printedpp1–2 and Section7.4 printedp26, including surrounding paragraphs, not merely the MathDB summary. Section1 defines a mean to be continuous and internal, then separately defines strictness and isotonicity. The conjecture itself is Conjecture29 in the PDF (the HTML conversion calls it26). It classifies pairs of means satisfying both invariance types via inverse transforms of arithmetic means. It adds no strictness or analyticity condition. The surrounding motivation differentiates smooth logarithmic means; earlier theorems expressly add their extra assumptions, and this does not insert them into the conjecture's literal free-standing wording.

Accordingly the non-strict minimum pair is an admissible counterexample to that wording. It is deliberately not a counterexample to a strict or analytic formulation. All final prose, README, manifest and provenance preserve this limitation. The generator must have a genuine inverse; a generalized multivalued inverse would be a different conclusion, not what h^-1 ordinarily means. The zero-posted-solution observation is not used as evidence of novelty; the proof uses standard minimum properties and makes no discovery or priority claim.

## Paper and acceptance

The full TeX proof matches every formal step, especially the inverse-domain and injectivity bridge. Parent changed author/license, integration wording and the excessively long post identifier in the bibliography, without changing mathematics. All4 final PDF pages were rendered and individually inspected. No overfull text, clipping or unresolved references remain. This is one distinct source question outside the accepted ledger; helper lemmas and separate invariance identities add no extra count. Independent source and formal review PASS.
