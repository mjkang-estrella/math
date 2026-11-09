# Round 3 plan

1. Use the checked `sectionEven_C_pow_mul` and `Round2.diff_readout`; do not reconstruct F1, F2 or F4.
2. Introduce polynomial evaluation at y = X * geomStep 1. Prove that the full-series transfer of y(1+y)R is y(1+y) times the explicit integral binomial reduced operator (Lemma R). This remains the central gap; the series-level operator alone does not imply it.
3. Formalize the bit-length divisibility weight, with per-monomial gains, and the exact constant coefficient formula. Prove readout using the checked parity theorem.
4. Prove the Chebyshev Pell and odd half-angle identities, Kummer bounds and even invariant.
5. Prove the reduced low-coefficient identities and residue divisibilities; the checked diff_one_polynomial is an n=1 identity, not a substitute for the reduced operator bridge. The review's r_(0,1), r_(0,2) numerators are recorded in PROOF.md and input receipts.
6. Prove strict growth (hence all nonzero differences), discharge exactly EvenFormula, OddOneBound, OddThreeBound, OddOneEquality, OddThreeEquality, FifteenBound, and apply the frozen conditional endpoints.
7. Keep sufficient equality sets as ruled by root. Preserve all frozen module bytes. Repeat fresh serial replay, kernel checking and full declaration audit.
