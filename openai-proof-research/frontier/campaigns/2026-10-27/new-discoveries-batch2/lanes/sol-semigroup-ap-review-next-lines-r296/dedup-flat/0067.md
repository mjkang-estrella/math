# r244 breadth: eight additional families screened, no nomination

Research date 30 October 2026. Bernstein is not counted here. These are eight distinct older source-question families screened, NOT eight surviving open questions or eight results. Two were retired after actual later proof comparison. Several others lack an adequate current closest-proof investigation; that requirement is explicitly incomplete. No famous solved problem was selected as a control, and no recent announcement is used as a substitute for a proof body. All identifiers below denote frozen primary PDF bodies from https://arxiv.org/pdf/IDENTIFIER. source-map.json gives hashes; chronology.json gives metadata dates separately from PDF interior dates. No worldwide priority or current registry clearance.

The compact history references in the r243 frozen history-screen.json were hash-checked before bounded keyword screening. history-exclusion-screen.json preserves hits. Positive-series Problem3 from1201.5156 was excluded before retrieval because r227 already treated it. The quasicrystal-word historical hit concerns polynomial approximation modulo ideals, not pinwheel diffraction. Continued-fraction hits concern hyperquadratic Laurent series, rational-numerator termination and TRIP-Stern paths; none is the prescribed lattice-polygon-angle problem below. Diversity hits concern maximum-diversity probability measures on balls and graph magnitude, not multiway metric embeddings. These distinctions are endpoint-specific and not a universal alias clearance. Period doubling and floor certificates were not attacked.

## 1. Lattice polygon angle compatibility (geometric/arithmetic)

**Original body:** Karpenkov,1712.01450v1, PDFp3, Problem2 (IKEA): classify all n-tuples of LLS sequences of angles that form integer n-gons, for arbitrary n. LLS consists of the alternating lattice lengths and lattice sines along the sail of a rational lattice angle (definitions pp1-3). The source reports the triangle classification and says the complete description is unknown for n>=4. This is not a claim about rational-numerator algorithm termination or empty-simplex classification.

**Actual comparison:** Blackman–Karpenkov–Dolan,2302.02720v3, published2023, Definitions1.15ff and Proposition3.14/3.19 with actual proofs in Sections4.3-4.4 (PDFpp23-24). Reversing generators of a simple rational cone yields congruences for adjacent-angle cosines modulo the lattice sine; cones of the same unit-edge simplex are handled by a change of canonical coordinates. This is a necessary local compatibility mechanism, not a closure/classification theorem for arbitrary polygons. No body-read current complete IKEA classification was found; latest proof coverage incomplete.

**Next mechanism:** encode each LLS angle by a unimodular transition matrix and impose a full cyclic product and oriented-edge closure. A collection of local congruences alone misses positive edge lengths and global convexity. First test n=4 exact rational edge feasibility; do not call a single quadrilateral a classification. DEFER, source-wide closure certificate missing.

## 2. Descent of ampleness through finite extensions (arithmetic geometry)

**Original body:** Bary-Soroker–Fehm,1106.1310v1, PDFp6, QuestionIV explicitly asks whether every virtually ample field is ample, alongside a separate weakly-ample implication. Ample means every smooth curve with a rational point has infinitely many; virtually ample means an ample finite extension exists. The precise selected subquestion is the finite-extension descent implication, not Shafarevich or Larsen.

**Actual comparison and retirement:** Srinivasan,1810.05184v1 (11Oct2018), Theorem3.7, PDFpp3-4, gives characteristic-zero L and quadratic M/L with finite C(L) for every genus>=2 curve in the stated class, while M is PAC. The actual proof constructs a tower of involuted finitely generated fields; Lemmas3.3-3.6 use factorization of maps from products to high-genus curves and restriction of scalars to preserve good extensions. The diagonal enumeration ensures every variety over the final extension receives points, including those not defined over the starting field. This answers the selected descent question negatively, before this campaign. RETIRE; neither the known counterexample nor the separate weakly-ample implication is nominated.

## 3. Symmetry of three-valued Weil spectra (finite-field arithmetic)

**Original body:** Katz,1805.10452v3, Conjecture10.5, PDFp17: for every finite field F and exponent d coprime to |F|-1, if W_(F,d)(a)=sum_(x in F) psi(x^d-a*x), a in F*, takes exactly three values, must those values be symmetric (0 and opposite nonzero values)? The minus/plus convention only permutes a. This is the author's recorded conjecture, distinct from Helleseth's power-of-two degree exclusion.

**Actual comparison:** Katz,1407.7923v3, Theorem1.5/Theorem4.5 with actual proof PDFpp8-10. Write the three values as 0,a,b; the incidence multiplicities of v^d+(1-v)^d and the p-parts of a,b give either valuations greater than [F:Fp]/2, or equal half-valuations and |a-b| a large p-power. The equal-valuation alternative is excluded in characteristics2,3. That proves divisibility restrictions, not a=-b in all characteristics. Reading this proof does not clear later symmetry results; current2.xml only returned three relevant older papers and is not a complete citation screen.

**Mechanism:** exploit all exact moment/incidence equations plus Galois constraints to force a+b=0; a computational list of exponent families does not settle all finite fields. DEFER as substantial number theory without a new elimination invariant. The older Helleseth question is not added as a second family.

## 4. Optimal distortion of finite diversities in ell_1 (metric geometry)

**Original body:** Bryant–Tupper,1712.01960v1, PDFpp1-2. A diversity delta on finite subsets is nonnegative, zero exactly on sets of size<=1, and delta(A union B)<=delta(A union C)+delta(B union C) for nonempty C. Determine the optimal general distortion f(n) into delta_ell1(A)=sum_coordinate max_(a,b in A)|a_i-b_i|, allowing arbitrary target dimension. Source Theorem1 proves f(n)<=n by the induced-distance coordinate map; metric lower bounds give Omega(log n). The source's full problem is an optimal bound, not mere existence of some f.

**Actual comparison:** Jozefiak–Shepherd,2303.04199v1, Theorems1.3-1.4 and actual algorithmic comparison proof Section4.5, PDFpp3,15-16. Diameter diversities have polynomial-time O(log n) distortion in O(log^2 n) dimensions. Low-cardinality-query algorithms cannot achieve O(n^(1-epsilon)) for arbitrary diversities unless P=NP. This is an oracle/computational obstruction and a special-class positive result, NOT an existential lower bound excluding all embeddings with arbitrary information. Also body-read1312.5408v3 Theorems17-18 identify the hypergraph packing-cut distortion bridge.

**Mechanism:** a cut-decomposition of the full diversity polytope, or a hypergraph dual certificate, must use all subset constraints. Pair distances alone cannot distinguish diversities sharing their induced metric. DEFER: attractive finite polyhedral objects but no uniform bound or extremal family. This is separate from earlier maximum-diversity measures on balls.

## 5. Two-sided Holder Green functions on a real Cantor set (analysis)

**Original question body:** Alpan–Goncharov,1612.00862v1, Problem3 PDFp4, records Volberg's question with permission: find compact K subset R and alpha>0 with C1 dist(z,K)^alpha<=g_(C\K)(z)<=C2 dist(z,K)^alpha uniformly sufficiently near K. This is a recorded seminar question; no earlier written Volberg question body was obtained. Problem1's arbitrary-modulus prescription is a different broader endpoint and is not separately counted.

**Actual comparison and retirement:** David–Jeznach–Julia,2303.02055v1, Theorem1.1, Section2.1 and Corollaries3.5-3.6, PDFpp3,8-13,21-22. The construction chooses small variable Cantor displacements on the line so the limiting logarithmic potential is flat on K. Corollary3.5 uses the boundary Harnack comparison with the Green function at infinity to obtain the two-sided distance power; the harmonic-measure equivalence follows in Cor3.6. The small-dimension construction resolves the selected existence question; it does not prescribe every modulus. RETIRE. This is a full-body comparison of a 2023 construction, not a new resolution announcement or a nominated rediscovery.

## 6. Absolutely continuous pinwheel diffraction (aperiodic geometry)

**Original session body:** Grimm's posed Problem2.3.2 in Adiceam,1604.06280v2, PDFpp5-6: for the unweighted control-point comb of the Conway–Radin pinwheel tiling (triangle sides1,2,sqrt5; the specified control point at(1/2,1/2) relative to the right-angle vertex), does its diffraction measure contain an absolutely continuous component? The distinct intensity-location classification Problem2.3.1 is not counted separately. Rotational symmetry leaves a possible singular measure on rings; absence of nonzero Bragg atoms does not imply absolute continuity.

**Actual comparison:** Grimm–Deng,1102.1750v1, Sections3-4, PDFpp4-6, derives rotational symmetry also for chirality-dependent weights and approximates radial diffraction by finite J0 Bessel sums from autocorrelation coefficients. The authors expressly qualify the apparent continuous component as numerical. This predates the2015 question session, and is not a current proof of the selected endpoint. current5.xml includes a2021 scattering/localization paper but that body was not read, so modern clearance is INCOMPLETE.

**Mechanism:** bound the radial autocorrelation's Fourier energy uniformly after removing the ring part; convergence of finite Bessel sums pointwise is not an L1-density certificate. DEFER; no quantitative tail/measure-decomposition bridge. Old polynomial-mod-ideal quasicrystal family was not reopened.

## 7. Stability transition for mass-perturbed Freud zeros (analysis)

**Original body:** Marcellan–Martinez-Finkelshtein–Martinez-Gonzalez,math/0512293v1, PDFpp10-11. For the orthogonality measure exp(-x^4)dx+lambda*delta_0 and the specified degree-n-dependent logarithmic external field phi_long=x^4/2, phi_short=(1/2)log(Q4(x,n)/x^2), the zeros are a critical energy configuration. Determine whether it is stable/global-minimizing; the source suggests a critical lambda0(n), small-lambda stability and large-lambda instability. The source's wording is partly heuristic, and it does not supply a fully quantified threshold conjecture for all parity cases. Odd-degree polynomials coincide with the unperturbed ones; do not silently invent a universal finite transition there.

**Actual comparison:** Diaz-Gonzalez–Pijeira-Cabrera–Quintero-Roba,2308.06304v1, Theorem5 PDFp18 and actual Gershgorin proof: for their Laguerre-Sobolev field, positivity of each external-field second derivative at all zeros makes the Hessian positive definite and hence gives a local minimum. It is a different weight, a sufficient condition, and a local conclusion. It cannot establish the Freud global-minimum transition or all-lambda threshold. The2005 source's own general convex-field proof PDFp9 supplies a separate sufficient criterion, not necessity.

**Mechanism:** exact Hessian continuation in lambda, with a global barrier argument excluding a competing minimum; computing a negative Hessian at one parameter only proves instability there. DEFER, endpoint qualification and actual closest Freud follow-up bodies still needed. No threshold theorem invented from the suggestion.

## 8. Alternating MZV polynomial recurrence (arithmetic/special-function analysis)

**Original posed body:** Zudilin in Cohl's1607.06196v2, Questions7.1, PDFpp10-11. Set A0(t)=1,A1(t)=0 and
(n^3-(-1)^n*t^3)A_n+(n+1)^2(2n+1)A_(n+1)+(n+2)^2(n+1)A_(n+2)=0.
For S_n=sum_(k=0)^n A_k, can one derive directly from its recurrence
(n^3-(-1)^n*t^3)S_(n-1)+(2n+1)n*S_n-(n+1)^2*n*S_(n+1)=0
the known limit product_(j>=1)(1+t^3/(8j^3)); and can A_n,S_n be given explicit hypergeometric forms? The sum starts at n=0; the S recurrence is for n>=1. This is a requested proof method/representation, not a still-unproved MZV identity.

**Actual comparison:** Zudilin,1504.07696v2 (revision31Mar2017), Sections3-5 PDFpp3-7. Lemma3 gives a hypergeometric B_n^alpha family and its nonalternating cubic recurrence, but Section5 explicitly distinguishes alternating A_n, eliminates parity to a new three-term subsequence recurrence, and says the related Frobenius–Stickelberger–Thiele closed form does not identify A_n. The actual elimination multiplies three neighbouring recurrences and cancels odd shifts; it does not give their asymptotics. The known MZV identity is not new work.

**Mechanism:** generating-function differential equations or a uniform discrete Volterra bound for the alternating recurrence. A proof that merely reuses the known MZV identity to restate the limit would fail the requested direct-recurrence condition and discovery standard. DEFER, likely special-function subsumption; current companion coverage is inadequate.

## Handback priorities

No breadth family is justified as a fully cleared new survivor. Diversity's finite dual cone is the most concrete genuinely different structural lead, followed by lattice-angle cyclic compatibility. Both require stronger current original/citing-proof work before sustained investment. Pinwheel, general field implications and Weil spectra are too large without a new invariant. The Freud suggestion needs precise scope before candidate status. The recurrent-MZV method question has a high routine-subsumption risk. Main Bernstein has a useful new leading-form obstruction (discovery.md), but no full result.
