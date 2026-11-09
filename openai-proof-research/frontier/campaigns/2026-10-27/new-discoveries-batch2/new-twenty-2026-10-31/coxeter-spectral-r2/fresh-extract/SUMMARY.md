# MathDB330264, coxeter-spectral-r2

**Held partial result; zero acceptance credit. Campaign remains1/20.** The existing19-vertex candidate survives the bounded primary-source comparison; full RACG language semantics and independent novelty review remain uncompleted.

New work closes the actual graph and spectral formal gaps. Strict Lean4.34.1 builds prove both SimpleGraph witnesses are trees, their actual adjacency and complement Matrix.charpoly are equal over ℚ, and their intrinsic Mathlib line graphs have equal Matrix.charpoly. Rational similarity identities are checked rowwise by the kernel, then transferred through charpoly and graph-isomorphism theorems. No characteristic-polynomial output is assumed as a hypothesis.

The actual RACG is now defined via Mathlib CoxeterMatrix.Group/PresentedGroup. The forbidden commuting-pair shortening direction is proved in this actual group, and shortest-word cardinalities are defined from CoxeterSystem.IsReduced. The converse normal-form direction and the automaton/cardinality equivalence are NOT proved. The inherited length18 recurrence discrepancy (difference4) remains a separate, valid finite result. No redefinition equates it with shortest-word counts.

All successful theorem audits use only propext, Classical.choice and Quot.sound. `PartialEndpoint.lean` combines these results; `330264-r2-PARTIAL.zip` is explicitly partial, with dependency hashes and extracted replay receipts. See replay-receipt.json for final replay status. No full quantified MathDB negation is claimed.

`source-comparison.md` independently compares actual McKay1977 theorem/proof bodies, Godsil's cited2007 slide construction, supplemental Godsil–McKay1982 §2, the original source's equal/unequal-growth constructions, and a later numbered-graph-product paper's Theorems4.9/5.14 and proof bodies. The exact Godsil extension theorem differs already at10, so it does not directly supply this pair agreeing through17. General spectral constructions alone do not give unequal growth. No public/routine full refutation bridge was verified; this does not establish novelty.

Current source/registry evidence is dated and bounded. Same-session r10 registry/version receipts and r11 Palomar403/MathDB403 limits are reused. No denied-route retries, browser tabs, author messages or publication. No predecessor or shared file was changed. Root must separately review novelty/significance and any eventual full endpoint.

Next decisive work is a genuine presented-group normal form: a well-defined generator action on reduced words modulo adjacent commuting swaps, yielding the missing lower bound on length; then prove clique-state recognition and the exact count bridge. `FORMAL-GAPS.md` gives the precise obligations and a concrete action-based route. This turn made substantive new formal progress but did not complete that theorem.
