# Provenance and development

Read AGENTS, original r104 candidate §§3–5, complete t224g-implementation/rebuild.py, its lake configuration and initial support definitions, and t117q-formal-development-r1/rebuild.py lines1–90. Adapted the full T224G runner by module/namespace renaming; preserved its pinned Lean4.34.1 commit5045d0056413266e57c625dcd7c365b10e377c52 and mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 lock. Exact parent and helper bytes are bound in binding.json. No new source theorem is assumed by the Lean code.

First build: coefficient identities elaborated, but the runner rejected unused-premise warnings and an unclosed unnamed noncomputable section. Fixed the closing section and marked deliberately redundant premises with underscore names; no mathematical statement was weakened. The second full build passed. Controls were strengthened before that pass to display the relevant increment hypotheses explicitly.

Only the four real-inner-product/scalar support declarations are claimed. No custom axioms, sorry, admit, unsafe or native_decide are used. Standard propext, Classical.choice and Quot.sound are the reported dependencies. No independent review verdict is claimed. The completed contribution gate is not used as an analytic premise or as a formal result.
