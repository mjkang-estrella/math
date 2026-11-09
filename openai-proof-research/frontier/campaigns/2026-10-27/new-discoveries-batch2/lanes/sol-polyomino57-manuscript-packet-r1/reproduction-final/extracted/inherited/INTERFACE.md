All endpoint names below are in Polyomino57.Diagonal.FiniteProof.AllCases.

- remaining : RemainingCases
- finiteCases : FiniteCases
- universalContainer : UniversalContainer 11 witness
- eligible : EligibleSize 11 57
- minimum_le : minimumSize 11 ≤ 57
- source_refutation : ¬ SourceFormula

No residual hypothesis occurs in these endpoints. Witness and source semantics are the frozen definitions. The source formula predicts58 at11, while the witness has57 vertices.

New generic representation interfaces are in Polyomino57.Diagonal.FiniteProof.Packed: encode, encode_bit, encode_lt, decode, decode_encode, encode_decode, encode_union, encode_and, encode_nonzero, encode_disjoint, encode_complement, rowOf, rowOf_decode, submasks, encode_mem_submasks, unionCheck_sound, row_bounds, all_split, halfCheck, bitCheck_comm, halfCheck_sound. Frozen Packed.bits_certificate and FiniteProof.excludes are reused unchanged. Actual instantiated types and axioms are printed in the fresh FinalAudit log and parsed inventory; audit success is reported separately.

Per-case C... and R... namespaces expose certificate, original literal domain/group checks and case_a_b_e. F740, F830, F840 expose the three forced geometric cases. The packet module manifest is the consumed dependency closure, not every development attempt.
