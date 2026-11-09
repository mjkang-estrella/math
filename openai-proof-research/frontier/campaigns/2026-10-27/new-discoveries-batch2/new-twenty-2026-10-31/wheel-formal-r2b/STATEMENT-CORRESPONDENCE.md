# Statement correspondence

| Source or assigned obligation | Lean declaration | Exact scope |
|---|---|---|
| Wheel C_(2t+1) joined to a hub | wheel; wheelSquare | Unchanged r2a definitions; Option ZMod vertices; mathlib boxProd |
| Literal fractional colouring and infimum | FractionalColouring; fracChromatic | Unchanged r2a nonnegative real weights on all independent finite sets |
| Parametric lower bound | wheelSquare_fractional_lower | All natural t >= 1; unchanged r2a proof |
| Translation averages with repeated sets | indexedColouring; indexedColouring_total | Index weights are pushed forward by summing all equal independent sets |
| P0 shifts | family0; family0_independent; family0_rim_count | Exactly the requested even-residue differences; every shift independent; t shifts per rim vertex |
| P1 checkerboards | family1; family1_independent; family1_rim_count | Fin 2 supplies the two colours; exact rim count 4t² |
| P2 role pattern | family2; family2_independent; family2_rim_count | Nondeleted nonlast roles S or P1, final role P2; exact rim count t² + 1 |
| Mixed coverage counts | family2_mixedA_count; family2_mixedB_count; colour_coverage | F2 count tm; F1 count 2m evaluated in the complete coverage proof |
| Attaining colouring | attainingColouring; colour_coverage; attainingColouring_total | Literal FractionalColouring; exact coverage 1; exact objective formula |
| MathDB 371637 / source Conjecture 7.3 | wheelSquare_fractional_eq | ∀ t : ℕ, 1 ≤ t → fracChromatic (wheelSquare t) = (6t²+7t+3)/(2t²+t+1) |
| Inherited exact target | target_proved | Type is WheelFormal.Target, whose definition is unchanged |

The source context starts at t >= 2; the assigned theorem includes t = 1. No t = 0 equality is asserted. Source and prior-art correspondence is inherited from the read-only r2a and r1 records. This lane performs formal implementation and does not claim a new external source review.
