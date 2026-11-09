# Closed finite actual-cell product gate

30 October 2026. Counts remain 9 additional / 39 total / next 40. Root alone
accepts and counts. Full mixing, novelty, and discovery acceptance remain HOLD.

The narrow requested mathematical gate is CLOSED, with no residual bridge.
Product.lean imports the preserved Cells.lean. For every natural N and every
reduced complete word R, let S = markedSlots (initial N) R. preBoard is the
board BEFORE slot i along R; slotB is the actual legalTypes cardinality after
S2 from that board. Thus b_i is evaluated on the canonical short-word board,
not on an assumed probability model. slotB_pos proves b_i > 0 on every slot.

actual_cell_mass_product proves literally

    cellMass N R = P N R * product_(i in S) (1 + 1/b_i).

Here cellMass is the actual sum of P_N over the actual compression cell.
selected_product identifies the inherited selectedFactors list product with
the finite product over the selected subset. The inherited actual_cell_mass_sum
and the finite distributive product identity then evaluate the powerset sum.

actual_conditional_bernoulli proves for EVERY finite T contained in S:

    P N (expand R T) / cellMass N R
      = product_(i in T) p_i * product_(i in S minus T) (1-p_i),
    p_i = 1/(1+b_i).

actual_conditional_every_subset gives the same identity for EVERY set E contained
in S, using selected and unselected filters. This is the exact finite-product
meaning of independent Bernoulli coordinates on the proved actual cell.
The inherited cell_subset_bijection proves unique and exhaustive coordinates;
actual_expansion_weight supplies the actual P_N numerator. No independence or
abstract probability model is a premise. Positivity follows from the inherited
P_positive_iff and actual_cell_mass_pos. No division by zero is used.

actual_zero_slot_cell proves the actual domain is {R}, mass equals P N R > 0,
and conditional point mass is 1 when S is empty. All empty products are 1.
actual_N_zero explicitly proves cellDomain 0 [] = {[]}, cellMass 0 [] = 1,
and normalized mass 1. The general theorems have no N > 0 restriction.

Literal.lean uses ONLY the authorized ROOTPATCH: `def words` becomes
`noncomputable def words`. Terminal, Law, and Cells are byte-identical to r3.
Original archives remain unchanged. The 198/295 inherited safe claims are
superseded for their archived bytes. The first fresh combined compile/audit
passes on 424 declarations (197 Literal, 294 inherited across three modules,
130 Cells), traversing 1888 constants. Exactly words._unsafe_rec was eliminated.
The final five-module gate inventories 458 declarations including private and
generated declarations, traversing 1957 constants; every origin and transitive
dependency is nonpartial and safe, and only Std3 axioms occur. Audit helpers
are metaprogram instrumentation, not proof axioms. All #check/#print axioms
commands are built from actual environment Names. The harness exits nonzero
on forbidden flags/axioms and compiler errors, panic, or REJECTED diagnostics.

The deterministic source-only archive is freshly extracted, all five modules
compiled serially with pinned Lean, and strict inventory/axiom audits replayed.
Owned compiled objects are removed. Separate final guarded verification checks
manifest, sources, immutable originals/copies, replay and all nine package pins.
Receipts are authoritative for measured resources and exact hashes.

No concentration, sigma-algebra, asymptotic, manuscript, external retrieval,
public posting, MathDB, shared ledger, or git work was performed. This formal
component does not claim a new-to-literature mathematical discovery.
