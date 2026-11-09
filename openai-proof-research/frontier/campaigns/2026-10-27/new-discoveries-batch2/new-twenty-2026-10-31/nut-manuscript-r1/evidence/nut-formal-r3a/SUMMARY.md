# r3a: Part A incomplete, zero credit

The requested `endpoint_of_finite (h : Nut8.FiniteObstruction) : Nut8.Target`
is NOT proved or declared. A3 remains incomplete. No result is self-accepted,
no Target inhabitant is claimed, and campaign counts remain unchanged.

Eight new proof modules establish A2 from the actual inherited graph hypotheses,
A4, nut connectivity, equivalence with the source cyclic-subgroup definition,
and the cubic cancellation/coherent-character lemmas. The extraction constructs
the actual labelled graph, derives translation invariance and the coordinate
character identity, gives an explicit injective linear quotient-kernel lift,
and proves real quotient nullity exactly one with a full nullvector.

The cofactor argument proves every principal minor nonsingular by inserting a
zero into a hypothetical minor nullvector, using symmetry and the full kernel
vector, then contradicting nullity one. It proves determinant zero and all
diagonal adjugate entries nonzero, with integer transfer. See WORK-NOTES.md for
the mechanism and statement-correspondence.md for exact scopes and edge cases.

The unresolved obligation is to assemble the exact frozen Admissible predicate
for this same quotient, including absolute neighbor counts, support connectivity,
paired shifts, shared semi-edge sign, entry bounds, and diagonal alternatives.
The character-coherence lemma already excludes opposite-sign contributions.
See GAPS.md for the precise remaining implementation work. No interface
inconsistency was found, and the interface was not weakened or replaced.

The fresh source-only extraction passed strict sanitized Lean rebuild and
leanchecker for all 20 modules. The complete audit covers 143 local declarations
including generated ones (48 new over r2), printing full types, bodies,
flags and transitive axioms. Only propext, Classical.choice and Quot.sound occur.
All four negative controls were rejected. The 44 replay calls used
155.41 summed wall seconds; peak sampled private memory was 2,271,924,224 bytes.
No resource cap was exceeded. Full receipts and logs are under fresh-extracted/logs;
the comprehensive audit is strict-R3Audit.log.

All 41 assigned input files were hash-bound before and after and copied with
SHA-256 identity. Every inherited Lean source, including Nut and the entire
FiniteGrammar dependency interface, is byte-identical. No edits were made to
r2 or r3b. No child agents, git operations, shared ledger edits, external messages,
network requests, browser tabs, publication or uploads were used. All writes
are inside this lane. The completed replay left no background jobs.

Deliverable: nut-r3a-source.zip, with portable replay.py and REPRODUCE.md.
A successful replay validates only this partial packet. The requested endpoint
and root acceptance remain mandatory; this packet receives zero acceptance credit.
