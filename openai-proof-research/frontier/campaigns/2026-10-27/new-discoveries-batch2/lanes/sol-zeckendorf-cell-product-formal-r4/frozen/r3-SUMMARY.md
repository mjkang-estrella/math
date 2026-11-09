# Literal compression cells: partial component

30 October 2026. Counts remain 9 additional / 39 total / next 40. Root alone
accepts and counts. Full mixing, novelty and acceptance remain HOLD.
STRICT AUDIT HOLD: inherited LiteralGame.words._unsafe_rec is generated partial.
Preserving Literal bytes prevents removing it; no exemption is claimed.

Cells.lean preserves Literal.lean, Terminal.lean and Law.lean byte-identically.
All interfaces are in LiteralGame. There are no extra mathematical assumptions.

Proved universally, including N=0:

- C2 is literally Move.Ck 0. expandable_iff identifies PREMOVE eligibility
  with legal C2 and multiplicity of index 2 at least two. diamond_steps,
  diamond_compress and diamond_expand prove both executions end at the same
  multiset, with the exact converse eligibility.
- compress scans EVERY adjacent S2,C1 pair. compress_executes preserves legal
  execution and its exact endpoint; compress_complete preserves completeness.
  compress_head and compress_reduced check replacement boundaries, and
  compress_fixed/idempotent prove that reduced words are precisely fixed points.
- exhaustive_cells and cells_disjoint partition ALL complete words by their
  unique reduced complete word. This statement is not restricted to a sample,
  strategy, chosen terminal, finite N range or assumed abstract word law.
- markedSlots uses the boards BEFORE moves in the short word. expand_legal and
  arbitrary_subset_in_cell permit EVERY subset of these slots. expansion_compress
  proves compression back to the same short word. compression_is_expansion and
  cell_iff_expansion exclude ignored preimages. cell_subset_bijection proves
  that EACH cell word corresponds to EXACTLY ONE subset. expand_injective also
  rules out collisions. Finite subsets and their image are explicit in
  cellDomain_image.
- actual_local_weight proves the exact factor 1/b, where b is legalTypes.card
  immediately after S2, in arbitrary executed prefixes and complete suffixes.
  actual_expansion_weight proves the full actual rational P_N weight:
  P N (expand R E) = P N R * (selectedFactors (initial N) R E).prod.
  selectedFactors inserts 1 for unselected positions and 1/b_i for selected
  positions, evaluated along R's fixed canonical boards. No probability model
  is assumed in this bridge; inherited P_product is used.
- actual_cell_mass_sum identifies cellMass, literally the sum of P_N over the
  filtered actual completeDomain, with P N R times the powerset sum of those
  expansion factors. actual_cell_mass_pos proves its strict positivity.

EXACT RESIDUALS: the powerset sum is not yet formally evaluated as
product_i(1+1/b_i). The normalized conditional point-mass identity with
independent Bernoulli parameters 1/(1+b_i) is not yet proved. No formal theorem
in this packet asserts these two statements. This is therefore a PARTIAL
delivery of the requested component, despite the complete applicability,
partition, subset bijection and unnormalized weight bridge.

Empty convention: expansion of the empty subset is R; expand [] E is [];
markedSlots a [] is empty. A zero-slot cell contains only R by the proved
bijection. The finite sum uses the powerset containing the empty subset once,
and the selectedFactors empty-list product is 1. In particular N=0 uses the
inherited actual singleton empty-word law, without an exception to applicability.

The ordinary source and preliminary review supply motivation, not Lean premises.
No manuscript, concentration, sigma-algebra or asymptotic work was performed.
Audit, deterministic source-only archive, fresh replay receipts and separate
final verification are delivered alongside the source. An audit initially
detected compress._unsafe_rec as generated partial; explicit structural recursion and noncomputable
definitions remove code-generation partial auxiliaries for compress and Reduced. Failed sources and logs remain in attempt-* files.

Exhaustive inventory: 425 actual declarations (295 inherited), traversing
1889 type/body constants. Exactly the inherited words._unsafe_rec is partial.
No new Cells origin is partial or unsafe. This fails the requested strict gate.
