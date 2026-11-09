# Library and source attribution

The authoritative manifest is provenance/lake-manifest.json: Mathlib plus eight
dependencies, all checked against installed HEAD and clean tracked tree/index.
No dependency is fetched. pins.json pins the executable SHA/version and unchanged
runner SHA. verification pins reports record actual runner search paths; Cli
has no compiled library directory and is correctly absent from LEAN_PATH.

Important Mathlib declarations used include
`sub_one_mul_padicValNat_factorial` (Legendre),
`sub_one_mul_padicValNat_choose_eq_sub_sum_digits'` (Kummer),
`succ_mul_catalan_eq_centralBinom`, `catalan_succ`,
`Nat.factorial_dvd_factorial`, `padicValRat.mul`, `.div`, `.pow`,
`Rat.num_or_den_zero_padicVal`, `PowerSeries.ext`, `PowerSeries.coeff_mk`,
`PowerSeries.coeff_mul`, `QuadraticAlgebra.ext`, `.re_mul`, `.im_mul`,
polynomial derivative/finite-sum/evaluation identities, and
`NonarchimedeanAddGroup.summable_of_tendsto_cofinite_zero`,
`IsUltrametricDist.norm_tsum_le_of_forall_le`, `Padic.norm_int_le_pow_iff_dvd`,
`Padic.norm_eq_zpow_neg_valuation`, and `Padic.valuation_ratCast`.
The frozen files are the authoritative exact uses; this list describes major
classical inputs rather than claiming a complete transitive Mathlib inventory.
Mathlib's tactic infrastructure is also used and is not a new proof tool.

The reciprocal-odd binomial valuation is Area's primary Theorem 1.4, internally
reproved in BinomialMoments/FiniteTransform/BinomialOddSum. The top formula
matches the primary computational observation, established here by the closed
source bridge and Catalan recursion. Neither that classical arithmetic nor the
known original-variable law receives separate novelty credit. The quadratic
midpoint representation, Riccati method, binary arithmetic, and triangular
odd-unit inversion are classical ingredients. The proposal is their full
shifted all-coefficient assembly, subject to final novelty adjudication.

The exact preprint titles and versions are recorded in paper.pdf, PROOF.md,
and the copied actual source bodies. No unidentified journal publication is
assumed or invented. Cached source live checks belong to the preliminary
review, whose full dated report is retained under provenance/; this lane makes
no fresh global or current novelty clearance.
