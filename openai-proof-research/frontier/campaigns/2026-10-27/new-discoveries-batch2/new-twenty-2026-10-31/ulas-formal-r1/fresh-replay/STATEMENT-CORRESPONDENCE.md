# Statement correspondence — round 1

The source is the cached arXiv:1904.03398v1 text, lines 125–151 (definition) and 1729–1735 (Conjecture 6.1), under expanded-corpus-r130/sources. No new prior-art or publication claim is made here.

`geomStep k` has coefficient 1 at multiples of k. `G N` includes an extra `geomStep 1` and the factors indexed 0 through N−1, so part 1 has 2m colours and other powers of 2 have m colours. `C` is the coefficientwise stabilized product. `G_agree`, `coeff_G_stable`, `C_agree` and `c_eq_finite` prove stability, including for arbitrary powers m. Thus `c m n := coeff n (C^m)` is the actual generating-series coefficient.

`Conj61` uses the per-k reading P1. Even k ≥ 1, odd k ≥ 0 and n ≥ 1 are literal. All three equality sets are required to be infinite for each eligible k. `Conj61Some` keeps the universal bounds and asks for one eligible k in each sharpness clause. Using n ≥ 1 instead of n ≥ 0 in the infinite sets removes at most one point. Odd bounds include nonzero differences and inequalities for padicValInt, avoiding the zero convention issue.

The full manuscript theorem gives equality for every odd n for colours 1 modulo 4, and for colours 3 or 7 modulo 16; it gives equality for every n = 2 modulo 4 for colours 11 modulo 16. These are SUFFICIENT sets, not iff characterizations. The review explicitly notes extra even equality points for colour 3. Consequently the task's phrase “exact equality sets” cannot literally mean these are iff sets. This discrepancy needs root adjudication; this round does not strengthen the manuscript to a false iff statement. The never assertion for colours 15 modulo 16 is universal and exact.

`Remaining` lists exactly six unproved Props. The conditional full theorem includes all positive bounds and equality guarantees, the stronger +7 bound, and the never assertion. The conditional `mathdb_342364` refutes P1 by choosing k = 3 in the last clause. The conditional `conj61_some` proves P2 with even k = 1 and odd k = 0 in both clauses, constructing arbitrarily large odd witnesses. None is an unconditional resolution yet.
