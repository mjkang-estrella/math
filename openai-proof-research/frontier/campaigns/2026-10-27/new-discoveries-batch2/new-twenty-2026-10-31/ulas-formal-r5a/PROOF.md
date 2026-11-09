# Round 5A even proof

This is an implementation packet for root review, not acceptance. It proves EvenInitialization and EvenFormula. It makes no new prior-art or novelty claim.

The 21 round-4 modules are frozen byte-identically. In particular, Lemma R, invariant preservation and the exact readout are imported unchanged.

UlasEven5Pell identifies the parity pair of w^m with the first and second Chebyshev polynomials evaluated at s = 1 + 2Y. A first-order recurrence proves the Pell identity t_k² − (s² − 1)u_(k−1)² = 1. The Chebyshev composition law then proves t_(2k) − 1 = Y(1+Y)rho, where rho = 8u_(k−1)². The actual power-series transfer identities give transferDiff (2k) 0 = y(1+y) ev(rho + reduced (2k) rho). Thus there is no missing series-to-polynomial bridge.

UlasEven5Coefficients identifies the frozen binA with twice the Chebyshev U polynomial. Consequently [Y^E]u_(k−1) = 2^(2E) choose(k+E,2E+1). It also proves the integral identity

choose(k+a,2a+1)(2a+1)choose(2a,a) = k choose(k+a,a)choose(k−1,a).

UlasEven5Kummer proves nu2(choose(2a,a)) = sum(digits₂(a)) using the pinned Kummer theorem and binary shift. Since the digit sum is at most a, the identity gives nu2(k) ≤ nu2(choose(k+a,2a+1)) + a for a < k. Coefficients outside the range vanish. Hence 2^(nu2(k)+E) divides every coefficient u_E.

Convolution gives 2^(3+2nu2(k)+E) | rho_E. At E = 0, rho_0 = 8k² has exact valuation 3+2nu2(k). At E = 1 the two cross terms agree, providing an additional factor 2 and giving valuation at least 3+2nu2(k)+2. For i ≥ 2 the elementary inequality i+1 ≤ 2^i−1 makes the general coefficient bound strong enough for the exceptional coefficient at E = 2^i−1. This avoids any separate no-carries calculation for those indices.

UlasEven5Invariant proves the full invariant for rho at v = 3+2nu2(k). The frozen invariant_step gives the invariant at v+1 for reduced (2k) rho. Adding it preserves the invariant at v; this proves EvenInitialization. The frozen evenFormula_of_initialization then proves EvenFormula, including nonzero differences for every k,n ≥ 1.

UlasEven5Final has conditional full endpoints taking exactly the five remaining odd Props. Neither full conjecture reading is claimed unconditionally.

The earlier review corrections remain in force: operator integrality is proved; the odd interpolation estimate needs degree 4F+4 or the safe 4F+5; the corrected line-150 threshold is at least 8, not 11. This lane uses no odd interpolation argument and closes no odd Prop.
