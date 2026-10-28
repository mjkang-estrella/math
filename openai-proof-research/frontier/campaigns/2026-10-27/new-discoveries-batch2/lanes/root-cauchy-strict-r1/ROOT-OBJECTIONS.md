# Root first-reading objections — credit zero

2026-10-28. Worker nomination is not acceptance, mathematical PASS, or formal PASS.
Preserve copied worker text for independent review; do not silently repair it.

1. Lemma3.2 and §6 multiply the row/column rescaling exponent by m. The correct
prefactor is (pi/sin(pi alpha))^m exp((1-alpha)(sum x_i+sum y_j)), with NO extra m.
Positivity of the prefactor survives, but the displayed equality is incorrect.
2. §5's Vandermonde factor is missing a factor product z_i^alpha: factoring powers
alpha*k+1 for k=1..m gives product z_i^(1+alpha), followed by powers0..m-1.
Nonvanishing survives, but the asserted identity is incorrect.
3. The claim |r_k(i)|<=C uniformly in k is false for negative x_i. Absorb this
exponential growth into a common convergence radius / choose U0 far enough to
make all tail arguments large. The normalized-tail domination needs an actual
bound after removing the leading exponent, not merely the original series bound.
4. A locally uniform limit of real-analytic functions need not be real analytic.
Use the common holomorphic slit-neighborhood series or an entire series in
x^(-alpha), with a proved infinite radius. Do not rely on the false general rule.
5. Theorem A outside mathlib is load-bearing. An abstract conditional strictification
lemma would NOT meet the user's literal Lean endpoint requirement.
6. The strongest substantive objection is a standard strict-composition / analytic
nondegeneracy theorem applied to the source's own Gram formula. Primary Karlin/Pinkus
theorem bodies and an explicit bridge matter; no inference from an open label or
absence of a named printed full endpoint. A routine generic corollary can fail our
standard even if its primary theorem is phrased with different objects.

These are review questions, not a claimed corrected proof or eligibility decision.
