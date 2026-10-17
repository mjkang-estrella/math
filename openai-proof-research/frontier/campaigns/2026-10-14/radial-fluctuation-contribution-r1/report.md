# Independent RF contribution review, round 1

**Verdict: TECHNICAL, conditional on the separate full-proof gate.** The full RF statement is stronger than the thermodynamic free-energy statements found in the primary sources. I do not identify an exact duplicate, a counterexample, or a previous developed project chain that by itself makes RF ineligible. However, the residual operations are a standard finite-graph Nash transfer, a stricter use of the existing CGS variational estimates in a deliberately small volume window, and an elementary relative normalization of the exact SU(2) character on the same low-energy sector. In combination they are a useful technical extension, not a substantial new mechanism under this campaign's stated gate. No campaign increment is warranted from this review. This is a contribution verdict, not an independent proof PASS.

## Exact object reviewed

Author directory: `../fresh-analytic-discovery-r19/`. The full 374-line candidate, full frozen scope, screening note, and rights/audit note were read. Bindings:

- `sealed-manifest.json`: `bde061c4eea5499343cfd07b623efe2079b858b19faa90f031e719702ec4902b`.
- `candidate.md`: `9ea51c98f9f50c7e614c754070b21ba8fc0e558df506363ccbbcaa453962ca80`.
- `original-scope.md`: `e40f0169ee9c301474c7f255ea129e311f001990786c338862e884dddf756e8f`.

RF concerns every fixed positive half-integer spin S, even periodic cubic side L, every sequence β→∞ satisfying β^.501≤L≤β^.51, and the exact zero-field quantum Gibbs distribution of total-spin deficit D=SL³−J. With a=β/L² and μ the exact nonzero free-mode mean, it asserts weak and all nonnegative-parameter Laplace convergence of a(D−μ) to Σ_{k≠0}(E_k−1)/(4π²S|k|²). These are full interacting finite-volume claims, including S=1/2 and zero-energy descendants. I have not replaced them by a selected-spin, ideal-gas, positive-field, or subsequence statement. No claim about centering by the interacting mean, all moments, fixed-temperature fluctuations, or optimal volume windows is part of this freeze.

## Primary comparison: what is already supplied

[Correggi–Giuliani–Seiringer, arXiv:1312.7873v2](https://arxiv.org/abs/1312.7873v2), supplies the Holstein–Primakoff comparison, projected Gaussian trial state and entropy calculation, Casimir gap, rough trace, energy cutoff, and two-particle subsolution. Its Section 5 already combines highest-weight reduction, interaction control, and a truncated zero mode. These operations, not merely its headline free-energy theorem, are the relevant antecedent. Its printed conclusions do not give RF's absolute, character-normalized Laplace comparison.

[Chatterjee–Diaconis, arXiv:1306.3625v2](https://arxiv.org/abs/1306.3625v2), supplies the centered geometric-to-exponential series mechanism and its square-summable domination in the non-Gaussian spectral regime. Its ideal canonical condensate result has different conventions and sign from a depletion variable. RF's changing periodic dispersion requires checking the common |k|⁻⁴ majorant, but introduces no new fluctuation mechanism at this final stage.

[Portelli–Holdsworth–Sellitto–Bramwell, cond-mat/0102283v1](https://arxiv.org/abs/cond-mat/0102283v1), is a harmonic/Hartree 2D XY fluctuation antecedent, not a rigorous exact quantum RF theorem. It should receive contextual credit, not be used to declare RF proved or duplicated.

The pinned Bloch, first-correction, ordering, and spherical-law companions were checked at their actual relevant statements. They concern thermodynamic magnetization/pressure or fixed-temperature macroscopic spherical behavior, not this shrinking-temperature radial fluctuation limit. They motivate RF but do not supply a load-bearing estimate in the submitted proof. Their stipulated truth is respected. The absence of a load-bearing pinned premise is disclosed; I do not invent an eligibility rule requiring one.

## The periodic pair estimate, including collision and zero energy

RF needs ||ρ||∞≤C_S(E+L⁻²)³ n(n−1). This is not literally the open-box positive-energy statement in CGS. The submitted work correctly identifies the two issues requiring an adaptation: periodic finite-volume equilibrium and, at S=1/2, the removed collision diagonal.

For S≥1, the pair-graph weights stay bounded above and below by positive spin-dependent constants. Comparison of norms and Dirichlet forms transfers the six-dimensional torus Nash inequality immediately. For S=1/2, the candidate extends a function at (x,x) by averaging the twelve adjacent off-diagonal configurations. The resulting L¹ and L² bounds are bounded-degree estimates. Each missing-edge difference is controlled by a path of bounded length in the off-diagonal graph. The displayed perpendicular-coordinate and particle-exchange detours stay within a uniformly bounded neighborhood; each retained edge receives bounded congestion. Thus Cauchy–Schwarz along these paths gives the extension energy bound with constants independent of L. This is a specific valid-looking geometric construction to be checked by the proof reviewer, but its operation is precisely bounded-detour Dirichlet-form extension. It does not create a new interacting estimate or overcome a growing obstruction.

The finite-volume Nash term L⁻²||f||²₂ yields a heat-kernel estimate C(t⁻³+L⁻⁶). Applying the CGS subsolution by the positive semigroup and choosing t=min(L²,S/(2E)) gives the asserted pair bound. At E=0, t=L² is available and the equilibrium term supplies L⁻⁶. There is no singular limiting argument or new treatment of degenerate spin multiplets at this step. The missing endpoint is paid by the standard finite-volume term, not by a new cancellation.

The general Nash-to-smoothing operation and comparison framework are classical; actual statements and proof passages of [Diaconis–Saloff-Coste, Nash inequalities for finite Markov chains](https://pi.math.cornell.edu/~lsc/papers/Nashfmc.pdf), Theorem 3.1 and Section 4.3, were consulted. I do not claim that paper states this exact deleted-diagonal graph lemma. The technical classification here follows the explicit bounded extension and semigroup derivation above, rather than an unsupported citation to an exact theorem.

## Absolute partition comparison

This is a real strengthening of an intensive free-energy estimate. Errors that vanish only after division by βL³ would not suffice. The author instead revisits CGS's proof estimates and retains their absolute size.

Write V=L³, M=Vβ⁻³ᐟ² and E₀≈Mβ⁻¹(logβ)⁵ᐟ². On the H+hN cutoff with h=λ/L², positivity gives n≤E₀/h. The pair estimate and the original quartic HP remainder then give

β〈K〉≤CβVE₀⁵h⁻² = C L²²β⁻²³ᐟ²λ⁻²(logβ)²⁵ᐟ².

For λ≥λ₀=β⁻¹ᐟ²⁰ and L≤β^.51 this is O(β⁻.18(logβ)²⁵ᐟ²). In particular, no improved interaction inequality is proved; the old n(n−1) bound is evaluated using a field cutoff rather than the highest-weight number bound used in the original zero-field argument. The finite-volume correction is absorbed because E₀L² grows in the frozen window. The projected Gaussian lower bound uses the same projection, Wick expectations, and entropy comparison already present in CGS. Its absolute errors shrink by the selected powers of L, β, and λ₀.

The choice L barely above √β simultaneously makes M diverge, producing a negligible cutoff tail, while keeping all absolute errors small. This requires careful bookkeeping and uniformity, but it is a compatible-scale specialization of existing estimates. It does not establish a new many-body stability principle or an estimate in a regime where those antecedent bounds fail. A thermodynamic theorem alone is insufficient; the primary proof operations suffice after the technical adaptation.

## Combined relative character normalization

The strongest potential contribution is the bridge from a field partition function to the zero-field radial observable. It must be assessed as a combined argument, since the elementary character identity alone would not pay it.

For a multiplet with highest weight J and deficit D, summing its descendants gives the exact geometric series. In the candidate's notation,

(1−e⁻ᵝʰ)Z(h)=Q(h)−R(h).

CGS already uses the highest-weight/multiplicity decomposition. The author retains the geometric sum, removes the bosonic zero mode, and then performs three relative comparisons using an H-only cutoff:

1. The Casimir gap gives D≤D₀=C L²E₀ and D₀/(SV)→0. Therefore all retained multiplets have J close to SV. The omitted endpoint in the character is exponentially small since βh₀SV has order βλ₀L→∞. The high-energy error is negligible, and Q(h)≥1 converts absolute tail errors to relative ones.
2. The small field h₀=λ₀/L² also satisfies βh₀D₀≤Cλ₀βE₀→0. Thus Q(h₀)/Q(0)→1. On the ideal side, λ₀aμ→0 gives the corresponding zero-field normalization of the nonzero-mode product.
3. On the same retained sector, (2J+1)/(2SV+1)→1 uniformly. Consequently the physical zero-field multiplet weighting and the highest-weight weighting agree relatively. The remaining tail is again controlled by the original rough trace and cutoff.

All these conditions fit simultaneously: λ₀βE₀=O(β⁻.02(logβ)⁵ᐟ²), λ₀aμ=O(β⁻.04), βλ₀L≥β^1.451, and D₀/V→0. The previous absolute partition comparison holds uniformly down to this same λ₀. Hence the relative normalization is preserved even after exponential centering; simply carrying an additive error through centering would have been inadequate.

This is a soundly targeted bridge, conditional on the proof gate, and should be preserved in the proof record. Nevertheless, the combined operation is still exact character summation plus uniform low-energy truncation and an auxiliary field chosen between two compatible scales. The existing Casimir and rough-trace bounds pay every error. There is no additional estimate on interacting radial fluctuations, nontrivial cancellation of interaction terms, or construction of a new effective radial measure. I therefore judge the combination technical as well as its constituent parts; this is not a verdict reached solely by labeling the character identity elementary.

## Strongest recent comparator actually checked

[Andreas Klippel, arXiv:2610.10736v1](https://arxiv.org/abs/2610.10736v1), dated October 7, 2026, has field-uniform thermodynamic spin-wave free-energy asymptotics for two-dimensional quantum Heisenberg ferromagnets at every fixed spin. Theorems 2.1–2.2 cover the specified long-range power laws and finite-second-moment rank-two interactions, with a supremum over all h≥0 after the stated temperature normalization. This includes fields tending to zero, not merely fixed strictly positive fields.

Its equations (3.68)–(3.82) explicitly retain the SU(2) descendant character, perform an energy/particle cutoff, and control the zero mode. The multiplicity and zero-mode losses are logarithmic and are discarded on the intensive scale. Its theorem does not supply RF's three-dimensional periodic absolute comparison or radial law. Its decorated exclusion/collision analysis is also not RF's torus Nash extension. It is evidence that exact character retention with weak-field cutoff control is already an explicit primary proof operation, not an exact duplicate of RF.

[Kwasnicki–Napiórkowski–Petrat–Pietruszka, arXiv:2610.17883v1](https://arxiv.org/abs/2610.17883v1), Theorem 1, is a one-dimensional S=1/2 two-magnon dynamical wave-packet approximation. Its particle number, dimension, observable and regime are different. It does not dispose of the equilibrium many-particle claim here. Only the stated scope was checked; no full proof reading is claimed.

## Eligibility and limits

The earlier-history screen used the mandatory briefs, NEW-TEN/TEN/TWENTY ledgers, and searches across proposals, reviews, findings and frontier iterations, followed by actual relevant scopes. The older Heisenberg F007/I39 chain is antiferromagnetic spin-one Haldane ground-state block tails/response, with different Hamiltonian, regime and method. I153's many-body spectral screens do not establish this ferromagnetic Gibbs radial result. Other Bloch/ferromagnetic keyword hits concerned qubit channels or Ising arguments. No old RF development was established by this bounded semantic screen. Family numbers alone were not used: an I271 identifier elsewhere is not source family 271.

The earlier unproved fixed-temperature heuristic was abandoned before RF's first freeze; the current proof is judged at its actual fixed scope. No count pressure, positive proof verdict, or publication preference changes this contribution assessment. No narrower or adjacent replacement is proposed.

This is not a worldwide priority certificate. The search did not exhaust every book, non-English paper, citation chain, or historical physics derivation; some search hits were inspected only at metadata level. The exact RF statement may be new to the literature. That possibility does not establish the substantial mechanism required here. The report's affirmative conclusion is the operation-level TECHNICAL verdict for the sealed candidate, conditional on full proof correctness.

## Reproducibility and rights

All 43 author payloads and exact file membership were authenticated against the parent-provided manifest hash. The 27 pinned sources match their Git blob IDs in the untruncated complete preprint tree; six classical primary PDF/text hashes match the sealed receipts. Additional comparator downloads have independent private receipts. These checks establish identity, not mathematical correctness. `reading-extent.md` distinguishes actual reading from mere hash verification. `verify_review.py` is read-only and requires the externally supplied review-manifest hash.

Original review prose: CC BY 4.0. Original verification code: MIT. Author attribution for the underlying proposed result: Myeongjin Kang, no affiliation. Third-party PDFs and extracts remain private; no publication or shared edits were performed.
