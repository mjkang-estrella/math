# Proof

The retained explicit `tour` has 24 rows, each a permutation of four ranks. The finite theorem `tour_euler` checks injectivity, coverage of every permutation, and suffix/prefix comparison agreement at all cyclic adjacencies. Kernel reduction of `decide` verifies these assertions.

If a cyclic word w realizes tour, windows starting at positions 2, 5, 8, 10, 13, 15, 18, 20 and 23 respectively force

    w 2 < w 5 < w 8 < w 10 < w 13 < w 15 < w 18 < w 20 < w 23 < w 2.

These indices are zero based and additions use positions modulo 24. For example the last inequality uses window 23, offsets 0 and 3, whose second word position is 2. Each rank comparison is checked by `decide`. Transitivity and irreflexivity in any linear order yield a contradiction. This is `tour_not_realizable`.

Assume `Conjecture`. Specialize its universal quantifiers at n = 3, N = 23 and t = tour, and supply `tour_euler`. Its conclusion gives K, w : Fin 24 → Fin K, and Realizes tour w. Apply `tour_not_realizable w`. This proves the literal endpoint `MathDB356266.conjecture_false : ¬ Conjecture`.

Assume `ConjectureLinear`, make the same specialization, and extract A, a LinearOrder instance, w and its realization proof. Use the extracted instance in `tour_not_realizable w`. This proves `MathDB356266.conjectureLinear_false : ¬ ConjectureLinear`.

Separately, the 1992 printed CDG word is stored exactly and its reduced four-windows are listed explicitly. `cdg_euler` and `cdg_realizes` each use `decide`, establishing that both the hypothesis and the realization conclusion can hold for a complete S4 ordering. This excludes a vacuous Euler predicate or a systematically impossible realization definition.

No probabilistic search, numerical approximation, external program output, or unproved bridge is used by the endpoints. The correspondence document explains why the predicate's distinctness and coverage clauses already force factorial length. That general cardinality consequence is documented, rather than added as a formal theorem, as permitted in TASK.txt.
