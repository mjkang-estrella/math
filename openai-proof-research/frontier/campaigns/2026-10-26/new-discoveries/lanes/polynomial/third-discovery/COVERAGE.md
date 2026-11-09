# Frozen full source nonvanishing coverage: MathDB368572

The complete seven-module supporting certificate is frozen and freshly replayed with pinned Lean4.34.1. The isolated owned replay is `replay/build/verified/audit.json`: PASS47 declarations, warnings as errors, only `propext`, `Classical.choice`, `Quot.sound`. The replay copies the parent/helper modules byte-for-byte and binds all seven SHA256 values. No proof holes, custom axioms, unsafe declarations, or native evaluator are used.

| Source/proof step | Module and declarations |
|---|---|
| Actual signed piecewise D_m and its zero support | parent `BergmanSource`: `D`, `D_nat_cast`, `D_support` |
| Actual source affine coefficient index | `sourceIndex`, `sourceIndex_divisible`, `sourceIndex_injective`, `sourceIndex_preimage` |
| All nonzero source terms reindexed with exact finite range and multiplicity | `source_row_reindex` |
| Literal Proposition1.10 double sum and normalization Q=z^(1−2n)P(z,z) | `sourceP`, `sourceQ` |
| Full source→compressed sum equality at every nonzero z | `source_exponent`, `sourceQ_eq_compressedQ` |
| Every triangular coefficient counts all ordered geometric-index pairs | helper `BergmanConvolution`: `pairFiber`, `card_pairFiber`, `triangle_sum` |
| Two-factor expansion and invertible complementary-pair reindex | `triangle_sum_two`, `reflect_quadruple_sum`, `triangle_sum_reflected` |
| Floor polynomials, exact carry uniqueness/existence, and adjacent difference | own `BergmanFloor`: `A`, `floor_le_index`, `carry_unique`, `carry_exists`, `A_difference` |
| At least one nonzero floor polynomial and strict positivity of the Gram sum | `A_zero_at_one`, `A_some_nonzero`, `gram`, `gram_pos` |
| Exact residue representative and integer height | own `BergmanResidues`: `representative_identity`, `representative_mod`, `representative_height`, `residue_unique`, `residue_iff` |
| Sum of each residue fiber equals the source floor polynomial | `fiber_sum`, `fiber_sum_all` |
| General finite fiber Gram identity, and four-index grouping | own `BergmanGram`: `finite_fiber_gram`, `four_sum_gram` |
| Literal compressed-sum term, reflected congruence and **integer** exponent | own `BergmanWeight`: `coefficientWeight`, `reflected_condition`, `reflected_exponent` |
| Integer negative powers become conjugates only after norm z=1 is supplied | `unit_power_difference`, `reflected_weight` |
| Exact source sum of squares, proved rather than supplied as hypothesis | own `BergmanSOS`: `triangular_sum_sos`, `compressedQ_sos`, `sourceQ_sos` |
| Full unconditional source nonvanishing theorem | `source_conjecture_368572` |

The final theorem quantifies over every natural m,n with 0<n<m, every coprime pair m,n, and every complex z with norm1. It concludes that the literal sourceQ value is nonzero. There is no supplied SOS, source-coefficient, exponent, genericity, or nonvanishing premise.

The formal endpoint currently concerns the exact source Laurent-normalized function, which is the source Q polynomial at all nonzero inputs. A separate ordinary-polynomial module and a multiplicity-allocation module are being prepared by the parent and independent reviewer; the mathematical degree/reciprocity/counting proof is already in `main.tex`. The final combined packet must bind those additional modules before claiming the punctured-disc multiplicity count as formally certified. Those extensions do not alter the seven frozen modules or create another counted discovery.

The complex-analytic consequence in the paper uses the actual source's published Bergman-kernel formula and an explicit realization of the products (z,z). The Lean packet does not formalize construction of Bergman spaces, proper maps, or kernels; no claim of such coverage is made.
