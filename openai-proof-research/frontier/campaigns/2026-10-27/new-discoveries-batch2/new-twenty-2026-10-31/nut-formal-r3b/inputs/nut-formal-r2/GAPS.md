# r2: incomplete milestone, zero credit

Part A is not complete. There is no theorem `endpoint_of_finite`, no proof of
`FiniteObstruction`, and no inhabitant of `Nut8.Target`. The assignment explicitly
requires complete Part A and assigns zero credit to a partial packet. This packet
does not qualify. No result is self-accepted.

The shortest remaining decomposition is:

1. Finish A2 from the actual global labelling. Transport the graph through
   `nut_circulant_global_coordinates`; derive `TranslationInvariant` and the
   coordinate character identity from `nut_sign_character`. Symmetry is proved
   for a labelled graph satisfying translation invariance, and restriction to
   representatives solves C u = 0 once that coordinate identity is supplied.
   The coordinate identity is NOT assumed proved. Construct the graph-specific
   injective linear lift ker C → ker adjacency, prove nullity exactly one over
   the reals, and give the rational transfer. The lift has not been implemented.
2. Finish A3. Prove graph connectivity from the full one-dimensional kernel,
   quotient connectivity, paired shifts, shared semi-edge sign, and exclusion
   of cancellation on a double edge by fullness. Derive `Admissible` and prove
   that its `unsignedQuotient` equals the actual unsigned graph quotient.
   The current admissibility predicate is decidable but this graph bridge is
   absent. Its absolute row sum describes coherent double edges AFTER the
   cancellation exclusion; it is not the unrestricted raw contribution grammar.
3. Finish A4: prove the symmetric real nullity-one/fullness implication for
   every diagonal adjugate entry. The executable determinant and principal
   cofactor correctness theorems ARE complete. The rank/adjugate support lemma
   is not. Do not mistake four concrete matrix certificates for that lemma.
4. Compose 1–3 into `endpoint_of_finite : FiniteObstruction → Nut8.Target`.
   Defining `FiniteObstruction` alone does not complete this requirement.
5. Prove a finite normal-form completeness theorem. The Python generator uses
   a catalogue of 194 connected subcubic simple graphs, 669 augmentations, and
   a fixed positive spanning tree. There is NO Lean coverage theorem for that
   catalogue, augmentation algorithm, or switching normal form. A proper
   completeness proof must precede accepting a list of certificates.
6. Kernel-check all resulting representatives, compose the unconditional
   endpoint, and obtain independent root adjudication. Only four actual
   determinant/cofactor certificates are presently implemented in new Lean
   pilot modules. Do not count the inherited unverified list computations.

A useful simplification is experimentally supported: the unsigned pretest is
unnecessary for this larger normalized finite obstruction. Without the pretest,
all 9,172 signings already fail, including 964 singular matrices with a zero
principal cofactor. This is an exact integer Python calculation, not a Lean
proof and not evidence of formal enumeration completeness.

The entire `Admissible C ε s` predicate is NOT invariant under arbitrary
switching when ε = 1: switching a positive incident edge makes it negative.
For the future normal-form proof, use the larger ε = -1 grammar as an
obstruction overapproximation, or prove preservation only of the sign-free
structural clauses. Do not assert the suggested unrestricted invariance lemma.
