# Terminal representation and normalized literal type law

2026-10-30. Both narrow mathematical obligations compile. Counts remain
9 additional /39 total /next40; root alone accepts/counts. Full mixing endpoint,
SourceClaim, manuscript, independent acceptance review and novelty remain HOLD.
No optional compression, shared edits, git, network, public or MathDB action.

All interfaces are in namespace LiteralGame. Inherited Literal.lean is
byte-identical; all 198 inherited actual declarations remain present.

Terminal.lean defines sourceIndices b by sorting source indices in decreasing
order and adding one. With F_i=Nat.fib(i+1), terminal_rep proves this list is a
mathlib IsZeckendorfRep, and sourceIndices_value proves its Fibonacci sum is
value b. terminal_eq_zeckendorf proves exact equality with
Nat.zeckendorf (value b), for every Positive terminal board. sourceIndices_inverse
recovers the entire board; terminal_unique proves equality of any two Positive
terminal boards with the same value. No arbitrary terminal is chosen to define
Z: Z N is literally (Nat.zeckendorf N).length, the unique source digit count.
terminal_card identifies board cardinality with Z. complete_combine_count
proves, for every Executes (initial N) ms b with Terminal b,
(ms.map combine).sum = N-Z N. All theorems include N=0, so in particular cover
the positive source domain.

Law.lean constructs a finite rational probability law. legalTypes is a Finset
of named Move values filtered by exact eligibility; mem_legalTypes proves
equivalence with existence of a literal Step. Each type occurs once, regardless
of indistinguishable token choices. next_step proves the canonical residual
update is that actual step. depthWeight uses empty terminal continuation mass1,
and live branch weight1/(legalTypes b).card. branches_disjoint proves distinct
first-type words disjoint; depth_normalized proves finite total mass1 by depth
induction and inverse-cardinality cancellation, without renormalization.

budget_zero_terminal and next_budget prove potential.toNat is sufficient:
no live branch can end at the cutoff. continuation_iff proves extensional
agreement with terminal Executes from every Positive board with adequate budget.
completeDomain uses the initial potential; domain_exact proves equality with
the inherited completeWords N, without restricting to a chosen strategy.

P N ms is depthWeight at that budget. P_normalized and P_nonneg prove the finite
probability axioms; P_outside gives mass0 off completeWords, and P_positive_iff
gives full support on ALL complete legal type words. P_point_mass states exactly
P N ms = ((legalCounts (initial N) ms).map (fun k => (k:Rat)^(-1))).prod
for every complete word. legalCounts recursively records the number of legal
TYPES at each successive canonical live board. execution_product and inherited
step_deterministic identify those boards with actual execution endpoints.
P_zero gives mass1 to [] and mass0 elsewhere; completeDomain_zero={[]}.

This is a normalized finite rational law, not an ENNReal/PMF wrapper. No
mathematical residual remains for the two stated finite endpoints. It does not
provide later measure/sigma-algebra, concentration, mixing or asymptotic results.

The combined certificate has 295 actual module declarations: 198 inherited and
97 added (including private/generated declarations and recursion/equation
auxiliaries). Inventory follows both types and bodies through 1526 constants;
Audit executes actual #check and #print axioms for every originating declaration.
Only propext, Classical.choice and Quot.sound are permitted. Inventory/Audit are
elaboration instrumentation, not additional mathematical axioms. Consult
audit.json, replay-receipt.json and verification-receipt.json for actual results.
Two fresh source-only extracted serial replays check the combined source and
remove their compiled artifacts. source-only.zip is deterministic. Source and
pin bindings, predecessor comparisons, bounded access and preserved failures
are documented in PROOF-SOURCES.md, provenance.json, bindings.json and FAILURES.md.
