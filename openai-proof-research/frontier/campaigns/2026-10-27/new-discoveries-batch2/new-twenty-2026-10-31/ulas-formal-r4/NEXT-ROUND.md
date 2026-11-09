# Round 5 continuation

1. Do not redo Lemma R: UlasBinomial.lemma_R_unconditional identifies the frozen
   reduced operator with the actual series transfer for every integer polynomial.
2. Close EvenInitialization. Prove the Pell factorization and Kummer estimates
   for rho = 8 U_(k-1)(1+2Y)^2; then prove the invariant for rho + reduced (2*k) rho.
   Invariant preservation, its iteration, exact readout and the resulting
   EvenFormula are already implemented in UlasInvariant.
3. For odd m, establish the half-angle initial representative and the crude
   coefficient bound. UlasInitialization links the initial constant to the
   frozen universal polynomial exactly, without interpolation. Coefficients
   1 and 2 and their residue bounds remain to be formalized.
4. Use diff_dvd_of_weighted, exact_readout and diff_ne_zero to finish the odd
   bounds and the stated sufficient equality sets. All six original Props are
   still open; UlasFinal4 is explicitly conditional on precisely those Props.
5. Repeat the strict source-only extracted replay and full closure audit after
   changes. Root alone decides acceptance; no credit is claimed here.
