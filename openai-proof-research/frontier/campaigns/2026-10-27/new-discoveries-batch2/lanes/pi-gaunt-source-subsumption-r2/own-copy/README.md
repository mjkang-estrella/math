# Unaccepted review packet: Gaunt's optimal Bessel tail bound

Read SUMMARY.md, main.tex/paper.pdf, and formal/OrderClassification.lean.
The full ordinary proof is in the manuscript. ORDINARY-PROOF.md preserves
the older asymptotic-based proof; OPTIMALITY-ROUTE.md describes the alternative
implemented directly in Lean. SOURCE-PRIOR.md preserves bounded initial
source/prior-art findings and unresolved access/subsumption objections.

Run `python3 verify_candidate.py` from this directory in the pinned workspace.
It asserts pins.json, creates a fresh temporary source directory, recompiles
all 14 modules and audits all 80 declarations. Only pinned upstream dependency
libraries are reused; no candidate prebuilt artifacts are accepted.

The endpoint proves both iff directions, including the zero-order boundary.
It defines K by the actual convergent DLMF10.32.9 integral, rather than
assuming Bessel properties of a surrogate function. There are no extra axioms
or residual analytic premises.

This packet has credit0. Integrated independent review, the actual journal
conjecture body and substantive novelty/classical-subsumption adjudication
remain pending. Nothing here is a worldwide priority certificate or a public
problem-status update. All tools/classical facts and helpers are uncredited.
