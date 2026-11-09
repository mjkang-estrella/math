# CLOSED: finite concentration assembly

Solo implementation, 2026-10-30. No acceptance or novelty claim. Counts unchanged: 9 additional / 39 total / next 40; root alone accepts/counts.

All twelve inherited mathematical modules (Literal through Concentration) are byte-identical to frozen r7. The sole new mathematical module is Assembly.lean in namespace LiteralGame.

Mandatory endpoint A: `finite_bernoulli_interval`. For every finite index set S, rational parameters 0<=p_i<=1/2 and mu=2 sum_i (p_i:Real)>0, every integer a and natural width h, the finite product mass of a<=|T|<=a+h is <=4/mu+2(h+2)/sqrt(mu). `subsetWeight` is literally the product over S of p_i or 1-p_i according to membership in T; `subsetExpect` sums it over ALL subsets. Normalization is `subsetExpect_const`; no assumed moments, independence or conditional distribution is an endpoint premise.

Mandatory endpoint B: `actual_finite_interval`. For n>=1, N<F(n+1), M>0 natural, every integer a and natural h, the actual real mass sum over completeDomain N of (P N w:Real) times the length-interval indicator is <=(badMarksMass N M:Real)+4/L+2(h+2)/sqrt(L), L=2M/(2n+1)>0. `actual_finite_interval_tail` replaces the bad mass by the explicit real cast of the inherited rational finite tail. Every cast of the actual rational masses is explicit.

New intermediate endpoints: exact finite cardinality mean, second moment and variance; finite_card_chebyshev; fair_subset_card_law; fairAtom_good; fair_subset_interval; actual_bad_cell_mass; finite_thinning_expectation; concentration_error_antitone; actual_cell_interval; actual_cell_indicator_le_one. Thinning uses inherited `finite_thinning_vector`; the atom bound uses inherited `fairAtom_squared`; actual applicability uses inherited pushforwards, parameter bounds, mean lower bound and real mixture. No source-law reconstruction.

Intervals are closed integer intervals [a,a+h], a:Integer, h:Natural, so translated intervals and intervals outside support are included. The proof counts at most h+1 possible atoms and uses the allowed h+2 slack. The fair law includes empty S and j outside support. Generic A requires positive mu. Actual B includes N=0: `actual_interval_zero` records its exact deterministic interval mass; every zero-mark cell is bad when M>0, so no zero mean is divided by. There is no F(n)<=N premise.

Strict serial compilation, exhaustive owned-origin/transitive unsafe AND partial checks, Std3 axiom audit, fresh extracted source-only replay, deterministic source archive, artifact removal and separate final guarded manifest verification are recorded in audit.json, replay-receipt.json and verification-receipt.json. The receipts are authoritative for verification status. Failures are retained with exact attempt sources/logs/receipts.

No manuscript, suffix hazard, asymptotics, all-N limit, final mixing, external retrieval, Google request, browser, git, shared file or MathDB edit. Formal component closure is not independent adversarial acceptance or prior-art clearance.
