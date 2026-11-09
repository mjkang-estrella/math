# Round 1 handback — partial, not acceptance

MathDB 338887 remains unproved in Lean. No self-acceptance or credit is requested. The ordinary proof is updated with a uniqueness proof via Proposition 7.9 and Theorem 5.25, the §3.6 citation correction, and the explicit rotor-weight factor in inclusion–exclusion.

Completed Lean work:

- Signed ambient dynamics, natural configurations and their processing compatibility, advance then move, exact Definition 5.2 recurrence, common-descendant legal relation, source diverse-walk recurrent components.
- Level and weight invariance under firing, trajectories and legal relation.
- Legal relation equals mutual reachability between recurrent states; mutually reachable representatives define identical component sets.
- Finite level fibres and finite types counted by r and testCount, using a bounded-chip encoding.
- Exact conditional reduction of literal component cardinality to CycleTest counts.
- Conditional uniqueness as an ∃! statement about actual component sets; conditional source recurrent-component status.
- Conditional full endpoint, using exactly seven explicit Prop arguments. No cycle-test definition is substituted for recurrence.
- Kernel-decided small rotor conventions and wrong-weight rejection, plus a proof that zero-chip states fail recurrence.

Seven remaining Props (complete statements are in Reduction.lean and SourceSemantics.lean):

1. CycleTestBridge: source Definition 5.2 recurrence iff the facing-pair/Hamiltonian test for every natural-chip configuration on C_n, n ≥ 3.
2. CanonicalTest: the explicit representative satisfies the test and has weight i for every positive m. Its chip level is already proved.
3. ConnectedFibres: equal level/weight recurrent natural configurations have a common legal descendant. This is the substantive unproved uniqueness input.
4. RotationCount: invariance of testCount under adding m to the weight.
5. UnitCount: invariance under multiplication of the weight by every unit mod n. This is the substantial root-of-unity/transfer-matrix obligation, still entirely open in Lean.
6. ArithmeticOrbit: equal gcds imply j = u*i + b*m for a unit u and natural b.
7. AmbientBridge: signed recurrent configurations are nonnegative, and a recurrent representative's legal component contains a diverse infinite walk (the source Lemma 5.19 direction).

Next round should first discharge CanonicalTest and ArithmeticOrbit, then prove a direct cycle-specific recurrence/period-word characterization. Use it to settle CycleTestBridge and AmbientBridge. For ConnectedFibres, implement sink stabilization at v_0 and classify the resulting canonical rotor states by weight, or formalize the Laplacian quotient route in PROOF.md. Prove RotationCount with a finite rotation equivalence. UnitCount then requires the full matching/transfer-matrix/period-trace argument and Fourier injectivity; the current packet contains none of that analytic proof. Do not mistake the short conditional assembly for completion of those major tasks.

Validation is recorded in results.json and fresh-extraction/logs/replay-result.json. All original development failures are retained. The audit concerns all local declarations in the endpoint/control module import closure and their transitive axioms; pinned upstream executable tactic/compiler declarations are trusted, not certified safe. This is a candid limitation relative to any interpretation requiring flag inspection of the entire upstream import environment.
