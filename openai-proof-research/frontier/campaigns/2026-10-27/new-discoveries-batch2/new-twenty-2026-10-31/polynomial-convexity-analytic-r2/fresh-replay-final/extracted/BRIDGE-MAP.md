# Ordinary proof to Lean correspondence

The source definitions remain byte-identical to the predecessor. E is all L-subsets of Fin n; tuples are all functions Fin d → E with repetition; coefficients use every inclusive prefix union. `SourceConjecture` remains a definition only.

| Ordinary bridge | Checked declaration | Scope |
|---|---|---|
| Exp(1) tail at t ≥ 0 | `expOne_tail` | Ici tail = ofReal(exp(-t)); no tail assumption |
| Clocks are nonnegative a.e. | `expOne_nonneg`, `clocks_nonneg` | Concrete finite product measure |
| Remove support intersection | `joint_survival` | Any real threshold vector, baseline-zero vertex maxima |
| Strict/weak survival convention | `lifetime_ne_ae`, `joint_strict_weak_ae`, `joint_strict_survival` | Every fixed tuple and threshold, even repeated edges |
| Scalar moments | `expOne_power_integrable`, `expOne_power_integral` | Every natural k, actual expMeasure 1; Gamma integral, k! |
| Coordinate moments | `clock_power_integrable`, `clock_power_integral` | Every coordinate of concrete product measure |
| Sum/lifetime integrability | `clockSum_memLp`, `lifetime_memLp`, `clockSum_power_integrable` | Lp argument replaces the elementary n^(d-1) bound |
| Weighted form moments | `linearForm_power_integrable` | Any signed real weights, every natural d |
| Mixed powers | `mixed_power_integrable`, `mixed_integrable` | Domination by clockSum^(d*k), arbitrary repeated edges |
| Product layer cake and Tonelli | `mixed_layercake` | Actual real mixed moment to actual finite-dimensional volume integral; uses measurable product-set sections |
| Scalar gap integration | `positive_rate_integral` | Positive real rate a, integral = 1/a |
| Factored gap integration | `gap_integral`, `gap_integrable`, `prefix_gap_integral` | Actual positive-orthant integral, positive prefix-cardinality rates |
| Coordinate-zero boundary | `volume_coordinates_nonzero` | All labelled coordinates nonzero a.e. |
| Chamber partition / gap transport / exponent identity | OPEN | See RESIDUALS.md |
| Integrate finite expansion | `integrated_expansion` | Actual model, no integrability hypothesis |
| Reindex / factorial | inherited `symmetrized_sum` | All d! labelled permutations; no stabilizer division |
| Convexity of moment functional | `concrete_integral_convex` | Concrete lifetime model; no assumed moment or integrability |
| Identify moments with coefficients / literal convexity | OPEN | No source endpoint theorem |

All exact local declaration types, including model definitions, generated declarations and assumptions of inherited generic helpers, appear in the fresh Audit.stdout. Only propext, Classical.choice and Quot.sound are permitted transitively. Prebuilt upstream mathlib and Lean oleans are explicitly trusted; checker processes attest local modules relative to them.
