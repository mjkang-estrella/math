# Operation-level comparison and nomination boundary

Original prose, CC BY 4.0. Status: author comparison, not an independent contribution decision.

The full claim is T273NC108 in `frozen-target.md`; the proposed proof is `author-proof.md`. The author argument closes its own stated obligations. Whether it contains a substantial unpaid operation is **not established by this packet**. It must not be counted automatically. In particular the matrix calculation below can be assessed as technical without disputing the theorem's scope.

## Selected source: complete family contract

The selected pinned family is [source273, The entropy photon-number inequality](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-entropy-photon-number-inequality-September-24-2026/build/main.tex). All nine TeX files were read: main, references, and Sections 0–6. All paths were located in the complete 13,223-entry tree; a complete-tree path search for this entropy-photon-number family returned this manuscript, not another companion manuscript. This is a catalogue-family check, not a semantic assertion about all 372 catalogue families.

`thm:epni` covers independent finite-energy n-mode input ports, internal entanglement unrestricted, and a scalar transmissivity identical across modes. `cor:thermal-attenuator` fixes an isotropic thermal bath and the same scalar channel on every mode; its exact output minimum is the scalar entropy-photon-number expression. Section 6's `cor:broadcast-capacity` concerns the stated degraded two-receiver pure-loss classical coding model. It does not generalize the physical mode matrices. These exact statements and their operative proofs, rather than their catalogue summaries, set the comparison.

| Operation in T273NC108 | Already paid | Additional calculation supplied here |
|---|---|---|
| Finite-energy compactness and entropy continuity | Source Section 1 | None; applied with a fixed finite-dimensional covariance matrix |
| Positive-noise Gaussian reference and stationarity | Ordinary compactness, matrix trace differentiation, Lagrange multipliers | Interior minimizer proof and (K^*h(Q)K=\lambda h(R)\) at every positive entropy |
| Four-weight interpolation | Source `thm:interpolation`, including arbitrary maps, parameter-dependent coordinates, parallel sums and Stieltjes argument | **No new interpolation theorem.** Place the physical mode index in the coordinate space and verify its hypotheses |
| Scalar Hessian at a Gibbs minimizer | Source Section 3, exact difference and finite-block duality | Replace scalar thermal energy by (d\Gamma(h(R))\), still comparable to number; otherwise the same proof |
| Simultaneous arithmetic and constant comparisons | Source Section 4 for common scalar reference temperatures | Use (U=\lambda^{-1/2}h(Q)^{1/2}Kh(R)^{-1/2}\), which is unitary; covariance slack gives both matrix comparisons after congruence |
| Thermal defect and weak convolution | Source Section 4, scalar defect and discarded-commutator cutoff | Transport the column (h(R)^{1/2}D_R\) through (U\) and (K\); keep complex conjugates and matrix order |
| Replacement control | Source mixture variance and two-weight logarithmic mean | Finite direct sum and Cauchy–Schwarz; reference-dependent constants |
| Relaxation covariance and cancellation | Source Section 5 and standard Gaussian channel calculus | Common scalar decay rate, different reference covariances; (K^*h(Q)K=\lambda h(R)\) matches the centered-energy traces |
| Limit identified by ladder recurrences | Source Section 5 | Different geometric ratio in each fixed reference eigenmode; no new compactness method |

The source is essential because its interpolated defect contraction is what permits the final coercive cancellation. None of the finite tests supplies it. Conversely, virtually all difficult infinite-dimensional operations are credited to that source. The only plausible integrated contribution is making the four comparisons, weighted defect transport and cancellation work in incompatible physical eigenbases. The normalization is ordinary polar algebra after KKT; the interpolation theorem was already formulated broadly enough to accept it. This is a concrete reason for a possible TECHNICAL disposition, not a reason to demand a substantial rating.

## Closest primary comparisons actually read

The exact versions, private byte hashes and reading ranges are in `private/primary-retrieval.json` and `private/reading-ledger.json`. No external theorem is silently made a stipulated premise. The analytic proof uses the pinned operations and the explicit calculations it displays.

| Primary body | Operations inspected and comparison |
|---|---|
| [De Palma–Trevisan–Giovannetti, 1610.09970v2](https://arxiv.org/html/1610.09970v2) | Theorems 1–5, the p-to-q norm derivative and scalar attenuator/amplifier concatenation. It pays one-mode constrained minimum output entropy. Iterating a one-mode statement on reduced states does not give a fixed **joint** input entropy bound for arbitrary entangled inputs. |
| [De Palma–Trevisan–Giovannetti, 1705.00499v1](https://arxiv.org/html/1705.00499v1) | Theorem 2's classical-to-quantum tensorization proof and Theorems 10–11's product-basis-diagonal-input theorem. Its classical conditional decomposition requires the stated input restriction; this is not a proof for arbitrary coherent entangled inputs to incompatible noisy modes. |
| [Giovannetti–Holevo–García-Patrón, 1312.2251v2](https://arxiv.org/html/1312.2251v2) | Gauge-covariant channel matrices, Proposition 1's attenuator/amplifier factorization, and Proposition 4's unconstrained minimum reduction. These are important antecedents for matrix Gaussian channels and the pure endpoint. The factorization does not preserve a specified positive input entropy, so its unconstrained minimization cannot simply be substituted into (T). |
| [De Palma–Mari–Lloyd–Giovannetti, 1408.6410v2](https://arxiv.org/html/1408.6410v2) | Equation (9), Sections III.1–III.2: matrix mixing, tailored anisotropic heat covariance, Fisher-matrix data processing and congruence. Matrix matching of an entropy/Fisher estimate is already a primary operation. The resulting exponential entropy bound is a different bound, with high-temperature saturation; it is not the finite-entropy (\operatorname{tr}g\) optimum in (T). |
| [Beigi–Mehrabi, 2504.02206v3](https://arxiv.org/html/2504.02206v3) | Theorems 1–2 and Section 3.1's inverse-logmean integral, arithmetic inner products, and score norms. Integral transfer between arithmetic and logarithmic metrics and quantum convolution scores are credited antecedents. This inspected portion does not supply the finite-temperature four-weight matching for (T). The full later lifting/ANOVA proof was not read or used. |
| [Beigi–Rahimi-Keshari, 2311.09572v2](https://arxiv.org/html/2311.09572v2) | Lemma 2's passive invariance, Theorem 3's restricted multimode tensorization, and the full Theorems 11–12 scalar supporting-flow proof. Thermal reference differentiation, passive rotations, and entropy-production optimization are already present. Their relevant multimode theorem retains a product or Gaussian-transformed diagonal input hypothesis. This packet does not claim to re-prove their meta inequality. |
| [Berta–Sutter–Walter, 1909.02383v3](https://arxiv.org/html/1909.02383v3) | Complete Section III.2, Proposition III.4: compatible heat flow, matrix Fisher linearity, geometric projection matching, and the entropy inequality. It is a homogeneous generalized marginal inequality. Appending a fixed bath does not identify its global sharp constant with the constrained finite-temperature optimum in (T). |
| [De Palma–Trevisan, 2105.05627v2](https://arxiv.org/html/2105.05627v2) | Definition 2/Theorem 1, Theorem 4's KKT equation, Section VI.1's full optimizer-adapted projection proof, and the start of the generalized-EPI application. This is especially close at the operation level: **Gaussian stationarity determines matrix normalization before a Fisher comparison.** That idea is not new here. Its sharp constant obeys a dimension scaling condition and uses infinite-covariance heat asymptotics. It does not directly optimize with a fixed independent finite-covariance bath and prescribed finite input entropy. Generic-case continuity and all applications were not completely read. |

The last two papers materially reduce the plausible novelty of the normalization idea. Their title-level Gaussian-optimality claims are neither ignored nor used as an automatic exact duplicate. The missing direct reduction would have to retain the fixed bath, its finite temperature, and the exact (g\)-entropy constraint. No such complete reduction was found in the portions read. That limited finding is not priority clearance.

## Developed project work compared by operations

The body search recorded in `private/history-search.json` searched campaign, iteration and experiment Markdown for bosonic entropy/EPnI/thermal-attenuator terms, then screened the matching bodies for incompatible/noisy mode matrices. It found 34 files in the selected authored-file search (some are shared indexes or historical snapshots). This is not an assertion that every file was read semantically.

I114's actual B target, stable ladder-defect proof and metric conversion were read. I117's audit of those operations was read in its initial sections; I120/I123's scopes and relevant failure/disposition passages were inspected, with truncation limits recorded. They concern quantitative trace stability for an identical scalar attenuator with an isotropic fixed bath. They already pay stable recurrence and scalar defect conversions; none is claimed here. The present proof obtains defects only at hypothetical-negative-witness Gibbs minima, and gives **no** stability estimate for arbitrary small nonnegative deficits.

`fresh-operator-discovery-r1` Section 6 was read through its domain obstruction: equality states need not inherit Gibbs regularity or finite thermal score, and zero-penalty stationarity does not force vanishing defects. `epni-gaussianity-r2`'s full frozen target and inherited-obligation section were read. Their target classifies equality for two freely varying independent ports; the Gaussianity implication remains open in those records. T273NC108 instead has a fixed strictly noisy gauge-Gaussian environment and proves an inequality by contradiction with positive penalties. It neither classifies all equality states nor closes their score-domain passage. Their target is not renamed or narrowed into this one.

## Several analytic families screened before freezing

These were exclusion screens, not full new theorem claims. Retrieval of every file in a family does not imply semantic reading of every file.

* **262, matrix Lieb–Thirring:** the actual action/equality interface and I250/I259's developed rotating-channel Hessian/coercivity operations were checked. Rotating-soliton stability would reopen an existing chain, and a dimension-uniform assertion needs more than the already developed transverse calculation. No target was frozen there.
* **354, cubic-torus isoperimetry:** the actual standard competitor comparison and two-volume setup were checked against I249's developed nested ball/tube analysis. That topology transition and constrained-nesting route are spent screening ground. No renamed stability or rectangular-torus surrogate was used.
* **368, diffeomorphic approximation:** the low-p theorem, its uncontrolled-cell operation, and the high-p companion's actual contract were checked against I331's simultaneous map/inverse Sobolev attempt. Collapse repair pays map energy and does not pay inverse energy. No bi-Sobolev theorem was inferred from forward approximation.
* **276, amplitude damping:** complete thermal, output and arbitrary-partner sections were read, then compared to I273 and the I285 phase-coercivity history. Arbitrary-partner tensorization is source-paid, and the strong-converse chain is already identified as externally duplicated in that history. No fresh nomination was made.
* **273, bosonic entropy:** selected only after inspecting its general interpolation, penalized minima and scalar cancellation, plus the existing equality/stability chains. Full two-mode matrix scope was then frozen and preserved.

No avoided family listed in the assignment was reopened. No historical finding or previously paid source companion is proposed as a new campaign acceptance.

## Handoff decision

Return the full author deduction for parent inspection, with **nomination held / contribution unresolved**. The mathematical proof has no identified remaining author gap, but it has not passed an independent proof gate. There is a concrete, potentially decisive technical-reduction concern. No formalization, manuscript production or release has been started. Campaign credit remains zero from this packet; the reported campaign total remains 18/20.
