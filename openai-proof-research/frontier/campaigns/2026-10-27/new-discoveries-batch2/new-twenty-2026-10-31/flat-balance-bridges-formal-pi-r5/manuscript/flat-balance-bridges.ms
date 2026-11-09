.TL
MathDB 352972: The Flat Balance Conjecture Refuted through Generic Finite-Graph Bridges
.AF MathDB 352972 formal certificate, lane flat-balance-bridges-formal-pi-r5
.AU
Formalization agent (pi), single lane, no children
.AI
Lean 4.34.1 (5045d0056413266e57c625dcd7c365b10e377c52); mathlib d13f23b723b8a846827a245b89c10fc7d3f11612
.AB
.no
This note documents the completed formal certificate for MathDB item 352972,
the flat balance conjecture for finite simple graphs. The refutation is
re-derived from a fully generic bridge layer over arbitrary finite simple
graphs: the c(0) = 1 convention, finite support and cutoff invariance of the
parity clique sums, an exact convention decomposition, integer and real cast
bridges for the discrepancy, and a generic contrapositive. All results are
machine-checked under warnings-as-errors with a strict kernel recheck and a
fresh source-only cleanroom replay. The environment audit enumerates 156
declarations with axiom closure exactly {propext, Classical.choice,
Quot.sound}. The controls record contains ten positive proofs.
.AE
.NH
Scope and corrected metadata (M1)
.PP
This certificate revises and completes the earlier author draft. Two
metadata corrections are recorded here and in results/352972.json.
First, the controls file audit/Controls352972Bridges.lean contains TEN
positive proof examples, every one a compiling proof; no failed compilation
is counted as a control. Second, the contrapositive control (C9) is proved
from the discrepancy hypothesis alone: it consumes no flatness hypothesis,
and no use of Flat is claimed for it. The earlier author files are preserved
untouched.
.NH 2
Source-level statements
.PP
The source layer (module FlatBalance, 502 lines) defines finite simple
graphs as a structure with a symmetry and irreflexivity proof, clique sets
as edge-complete Finsets of vertices, the clique counts c(k), the parity
weighted sums oddCliqueSum and evenCliqueSum over range (card V + 1), the
flatness predicate Flat (every triangle lies in a common bipartition
witness), balancedness Balanced as discrepancyNat at most one, and the
conjecture FlatBalancedConjecture. The K(3,3) witness on Fin 3 (+) Fin 3 is
exhibited flat with clique counts c(0) = 1, c(1) = 6, c(2) = 9, giving
odd sum 7 and even sum 10, discrepancy 3 under the positive-index
convention and 4 under the c(0)-inclusive convention; either exceeds one.
The literal endpoint not_flat_balanced_conjecture is the source refutation.
.NH
The generic bridge layer (R1)
.PP
The new module FlatBalanceBridges proves everything that follows over an
arbitrary finite simple graph G on any vertex type V; the witness is used
only at the final instantiation.
.NH 2
The c(0) = 1 convention, empty graphs included
.PP
Theorem cliqueFinset_zero: for every G, the 0-cliques are exactly the
singleton of the empty vertex set. Theorem cliqueCount_zero: c(G,0) = 1.
Both are unconditional in G, so they apply to the empty graph and to every
discrete graph; the convention is a theorem, not an assumption.
.NH 2
Finite support and cutoff invariance
.PP
Lemma cliqueFinset_empty_of_card_lt and cliqueCount_of_card_lt: no k-cliques
exist once card V < k, since every vertex Finset embeds in univ. The private
range-extension lemma sum_range_cutoff states that a finitely supported
summand has cutoff-independent partial sums. Consequently, for any cutoff
N with card V < N, the odd selector sum over range N equals oddCliqueSum G
(oddCliqueSum_cutoff), and likewise for the even selector with c(0)
included (evenCliqueSum_cutoff) and the positive-index even part
(evenCliqueSumPos_cutoff). The parity sums therefore have honest finite
support; no hidden divergence or convention-dependent truncation exists.
.NH 2
Convention separation by an exact decomposition
.PP
Theorem evenCliqueSum_decomp: evenCliqueSum G = c(G,0) + evenCliqueSumPos G,
pointwise in G, via the term split
(if d = 0 then c else 0) + (if d = 0 AND d > 0 AND d even then c else 0).
The two source conventions remain distinct objects; neither is substituted
for the other anywhere in the certificate. Theorem oddAddEvenCliqueSum
recombines the parity selectors into the plain clique-count sum.
.NH 2
Cast bridges and bound equivalence
.PP
natAbs_cast_abs: the integer cast of Int.natAbs z is the true |z| in Z; no
truncated natural subtraction enters any cast. natAbs_cast_real lifts this
to R for natural inputs, and discrepancyNat_cast_real transports the
discrepancy exactly:
 (Nat.cast (discrepancyNat G) : R)
   = |(Nat.cast (oddCliqueSum G) : R) - (Nat.cast (evenCliqueSum G) : R)|.
balanced_iff_absInt and balanced_iff_absReal: Balanced G agrees with the
absolute-value bound at most one, over Z and over R respectively. The
endpoint hypothesis therefore transfers through the cast layer without
reproof.
.NH 2
The generic contrapositive and the endpoint
.PP
not_balanced_of_one_lt_discrepancy: any finite simple graph whose clique
count discrepancy exceeds one is not balanced; the proof uses the
discrepancy hypothesis and nothing else. flat_not_balanced_exists_via_bridges
instantiates the contrapositive at K(3,3) using the source lemma
K33_discrepancy_gt_one, and not_flat_balanced_conjecture_via_bridges
re-derives the literal negated universal. The bridge layer is thus
formally connected to the source-level conjecture negation; no bridge lemma
is idle.
.NH
Machine-checked environment audit (R2)
.PP
audit/FlatBalanceEnvAudit.lean walks the elaborated environment of both
production modules and enumerates every declaration, generated and private
ones included: 156 declarations. Kind, definition safety, origin module,
full type, full value body when present, and the complete transitive axiom
closure are printed for each. The scan reports zero unsafe, zero partial and
zero opaque declarations. The union of axioms over all 156 declarations is
exactly {propext, Classical.choice, Quot.sound}. The transitive constant
closure of each endpoint refutation contains 14 local constants and the
axioms {Classical.choice, Quot.sound}; propext enters only through the
Finset extensionality used in the bridge layer itself.
.NH
Positive proof controls (M1)
.PP
audit/Controls352972Bridges.lean, receipted at
receipt/1794089496104554182, contains ten positive proofs.
.C1 C2: the generic empty-clique shape and c(G,0) = 1 for every finite
simple graph, empty graphs included; the witness instance c(K33,0) = 1 and
the zero-vertex instance.
.C4: generic finite support, no 7-cliques on six vertices.
.C5 C6: cutoff invariance instances for the odd and even selectors.
.C7: the exact convention decomposition instance.
.C8: the integer natAbs cast bridge.
.C9: the generic contrapositive instance; by the metadata correction its
proof uses only the discrepancy hypothesis.
.C10: the real bound-equivalence instance for the witness.
.NH
Cleanroom replay (R3)
.PP
The cleanroom under cleanroom/ starts from an empty build directory and
holds source-only copies of the two production modules; their sha256
digests equal the lane sources (recorded in source-hashmap.json). The
replay compiles both modules with -DwarningAsError=true -M3500 -j1 under a
two-CPU affinity and an isolated LEAN_PATH containing only the fresh build
directory and the pinned upstream libraries; the earlier lane's build
output appears in no path used by the replay. leanchecker re-verifies both
oleans at the kernel level. EXTRACTION-RECEIPT.json records the tool
version, dependency revisions, flags, and all hashes. The lane build
directory carries no legacy path in the final state.
.NH
Recorded failed attempts
.PP
Failed attempts are recorded with their receipts, not silently discarded:
the first cast section draft (implicit NatCast/Real elaboration) failed on
instance synthesis; a placeholder argument in the h4 cast step and a
misplaced Real import failed next; the first controls draft left one goal
open; the first environment audit draft used a nonexistent
DefinitionSafety constructor and a brace-escaping form. Each has a receipt
in receipt/ and a log in logs/, and each was fixed in place; no fabricated
failure is claimed anywhere.
.NH
Artifacts
.PP
results/352972.json (final record), MANIFEST-352972-final.json (sha256
manifest over sources, receipts, logs, cleanroom outputs, with named
non-circular exclusions), EXTRACTION-RECEIPT.json, source-hashmap.json,
audit and controls receipts. Independent audit and root acceptance remain
out of scope of this lane and are not self-credited.
