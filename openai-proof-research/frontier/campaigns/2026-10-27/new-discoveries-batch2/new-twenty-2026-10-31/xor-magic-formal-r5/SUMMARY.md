# MathDB 372205 — final assembly r5

The packet proves the corrected existence statement for every n ≥ 4, and the exact negation of the literal printed statement for every n ≥ 4. It also re-exports the inherited all-n and positive-n negations. Root acceptance and credit remain pending.

The final declarations are `XorMagic.corrected_all : ∀ n : ℕ, 4 ≤ n → CorrectedAt n` and `XorMagic.not_printed_each_ge_four : ∀ n : ℕ, 4 ≤ n → ¬ PrintedAt n`. No construction hypotheses remain. `FinalEndpoints` imports both.

The assembly transports matchings, proper colouring, indexed cycles, regularity, magic and the actual fixed-point lifted cycle walk through graph isomorphisms. The indexed outgoing certificate proves OmegaWalk for the next chosen slopes. The vertex representation is `Fin m` at each iteration; its literal bijective Bits labelling proves the correct order. Complement decompositions are supplied for every translation by the r4b disjoint block construction. Separate bases n = 4 and n = 5 give seeds at all n ≥ 4. For n ≥ 6, interpolation uses the n−2 seed. High-degree complements supply the remaining two open degrees and one closed degree. The direct base certificates handle n = 4 and n = 5.

All inherited Lean modules are retained byte-identically. Inputs are copied with SHA-256 identity and bound before and after work. The copied r4c and r4b packet hashes match TASK.txt. No git, network, shared ledger changes or child agents were used.

Validation receipts and final counts are appended below after the fresh extracted replay completes. This file does not self-accept the result.

The first replay completed all 107 strict Lean builds, then stopped at a uniqueness assertion in the Python audit-data checker. One lazy generated equation lemma appeared under two importing modules. Its complete type and body have identical canonical SHA-256 hashes in both reports. The checker now verifies this equality and records both occurrences without double-counting the unique declaration. The complete replay was restarted from a new empty extraction after this checker-only repair. No Lean proof source changed. The first attempt logs are preserved.

Fresh extracted sanitized strict replay passed: 107 builds, 107 leanchecker runs, 1468 local declarations fully audited, and 17 negative controls rejected. All 88 inherited modules are byte-identical, and all 101 bound source inputs and copies match their initial hashes. Peak private RSS: 5257736192 bytes. Longest bounded call: 36.882 seconds. No guard kills or background jobs remain. Existing-olean refusal and extracted source hash identity passed.
