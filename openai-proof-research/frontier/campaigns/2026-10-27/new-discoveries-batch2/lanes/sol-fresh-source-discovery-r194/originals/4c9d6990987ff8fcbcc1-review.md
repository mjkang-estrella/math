# T096N126 — independent contribution review, round 1

**Recommendation: TECHNICAL** (conditional on correctness).

This is an independent contribution review of the full integrated theorem frozen in `fresh-analytic-discovery-r126/packet/public/FROZEN.md`. It assumes that the author proof is correct. It is not a correctness review. The separate proof review was not inspected, and neither was its brief. No count, acceptance, gate or worldwide-priority claim is made. Under the campaign rules, TECHNICAL does not count.

In short, the theorem is a genuine and, within the bounded search below, previously unstated strengthening. It extends small-positive-correlation propeller optimality from three labels to every finite label count, with one threshold that does not depend on dimension, label count or masses. However, the label-count and dimension uniformity is not produced by a new estimate. It is inherited from the accepted R012/I38 weighted calibration, or it follows automatically from expanding exactly around a fixed planar reference. The remaining compatibility work (tails, higher chaos, frame change and absorption) consists of short classical estimates. These follow a design already present in the primary literature: a bounded smoothed-score weight in the tails, and a first-moment stability estimate used as the leading-order penalty in a small-ρ perturbation. I examined each place where an unpaid uniform compatibility estimate could hide (Section 5) and found none. This reasoning is analogous to the T238B125 lesson, but it is decided here on its own merits.

## 1. Claim and artifacts reviewed

The claim reviewed is the one in the user brief and FROZEN.md (SHA256 `ec4ebab8…d382`). There is one absolute ρ₀ ∈ (0,1). For every d ≥ 2, every k ≥ 3, every measurable labeled partition A (arbitrary masses and empty cells allowed) and every 0 < ρ ≤ ρ₀,

  S_ρ(A) = Σ_i [⟨1_{A_i}, T_ρ 1_{A_i}⟩ − γ_d(A_i)²] ≤ S_ρ(P).

Equality holds only on the propeller orbit P_{d,k}. No effective threshold and no quantitative noise stability is claimed.

I verified the following anchors read-only: proof.md `c60417b4…ea59`, packet/MANIFEST.json `8419adc4…e28d` (equal to the detached FINAL), and outside REPORT.md `26aaf530…7587`. They match the handoff. These are artifact checks only.

The disclosed sequence is retained without backdating. noise-feasibility.md ends with an unpaid linear tail term. prefreeze-addendum.md later records, before the freeze, the v-weight, the cone lower bound, the polar alignment and the absorption outline. The full proof was written after the freeze. For contribution purposes this sequence is neutral. It does not show that the operations were unpaid, and it does not show that they were paid.

## 2. Exact operational scope of the inherited R012/I38 input

I read I38 Sections 3–9 (lines 90–388), which include (6.10), (7.1) and (7.2), together with the R012 finding. The contracts the proof uses are as follows.

* **(6.10)** For every finite norm-one score list v, in any dimension ≥ 2, with any number of labels ≥ 3 (zero padding allowed): e(v) ≥ c_V·dist(v, T)². Here T is the set of unit equilateral-triple arrays and c_V is universal.
* **(7.1)** For a partition with F > 0, set v = z/√F and choose t ∈ T that minimizes ‖v − t‖. This gives
  J_t(A) = B − ⟨t, Z_A⟩ ≤ (B⁻¹ + (2c_V)⁻¹)·Δ(A) = C₀·Δ(A).
  Because ‖v‖ = ‖t‖ = 1 for every t ∈ T, minimizing ‖v − t‖ is the same as maximizing ⟨t, Z_A⟩. The author's restatement "every maximizing t" is therefore exactly I38's contract and not a strengthening of it. The identity J = B − √F + (√F/2)‖v − t‖² holds for every t ∈ T, and only the minimizer is fed into (6.10).
* **(7.2)** For the propeller of that t, ε ≤ 6√J. Inactive labels are covered by the single zero-score event max_i⟨t_i, g⟩ ≥ R/(2√3). There is no union bound over labels.

All three are uniform in d, k and masses. They apply to every measurable partition, so they also apply to the truncated partition A^N used in proof Lemma 4.1. They do not mention ρ. R012 was counted as SUBSTANTIAL for the uniform extra-label activation estimate (6.4) and its compactification (R3 review, Sections 3–4). The present theorem neither reopens nor re-earns that mechanism. **The weighted linear calibration J ≤ C₀Δ is the decisive inherited input.** It is exactly the statement that the order-ρ part of the noise deficit is coercive in the weighted mismatch norm that also controls the order-ρ² errors in a bounded region.

## 3. The strongest compatible reduction (integrated)

The comparison below is a single route, not a list of components. Each step is matched to the strongest existing operation that already supplies it. The steps are composed with the constant order the frozen claim requires.

**R1. Exact quadratic structure (classical).** Write f_i = 1_{A_i} − 1_{P_i}. Since T_ρ − Π₀ is positive semidefinite for ρ > 0,

  S_ρ(A) − S_ρ(P) = 2Σ⟨f_i, (T_ρ − Π₀)1_{P_i}⟩ + ρ‖Σ-first-chaos‖² + Σ_{m≥2}ρ^m‖Π_m f_i‖².

This expansion is the same Hermite bookkeeping as Heilman SSC (12)–(14) and Theorem 7.1 (103)–(104). Expanding around a candidate is the standard first step for a quadratic functional on partitions.

**R2. Global entry (classical; SSC Theorem 7.1 Step 1).** The bound S_ρ(A) ≤ ρF(A) + ρ² gives Δ ≤ ρ. SSC's (104) is the same step, with a loss of 3kρ. Here the factor k disappears because Σ‖1_{A_i}‖² = 1. That improvement is trivial.

**R3. Leading-order coercivity with stability (inherited; SSC Theorem 7.1 Step 2 + I38).** SSC uses the three-label stability of Lemma 2.8 (d₂ ≤ 6Δ^{1/8}), followed by a small rotation (Step 2), to enter a neighborhood. SSC Section 8 is phrased for its equal-mass Conjecture 3 (k = 4, n = 3). There it names the missing ingredient for k ≥ 4 as an order-zero stability estimate resembling Lemma 2.8, and says that with such an estimate the main lemma would go through "in principle". This is a design statement, not a proof. I38 (6.10)/(7.1) provides a far stronger, weighted and all-label form of that estimate. Its "polar alignment" also supplies the frame selection that SSC Step 2 performs with rotations.

**R4. Bounded-region Taylor control (classical; compare SSC Lemmas 4.2, 5.3).** The proof's (12) is a Taylor expansion of the planar smoothed score on a compact parameter set. Its constant depends only on R.

**R5. Tails: use the exact bounded smoothed score, not its linearization (design paid by Eldan and Heilman).** Heilman 2108.04950v1 Section 1.1 (read) reports, citing [Eld15, Section 1.1], that the example (−∞, 0] ∪ [d, ∞) shows a linear centroid-type deficit cannot control the noise deficit without a logarithmic loss caused by far tails. I did not read Eldan's own Section 1.1. Eldan's Conjecture 1.5 (as stated in Heilman 2108 Section 1.1) and Heilman's Theorem 1.6 and Problems 1.10–1.11 replace it with the weight Φ(β⟨ν, x⟩/√(1−β²)) = T_β 1_H(x). This is the exact smoothed indicator of the comparison set. Heilman 2108 Section 1.3 explains that the penalty must be bounded at infinity for exactly this reason. The proof's q_i = T_ρ 1_{P_i} − 1/3 is the label-wise analogue. Its lower bound (11), q_i − q_j ≥ 2κρ·v, is an explicit two-dimensional reflected-sector integral. It plays the same role as SSC Lemma 4.2's (51) lower bound for ρ⁻¹ sign(x₁)·LT_ρ(1_{B_i} − 1_{B_j}), but is simpler, because T_ρ of a cylinder over planar sectors is itself planar.

**R6. Higher-chaos energy in the same weight, uniformly in d (classical tensorization + Mehler + margin principle).** The complete argument is three lines.
(a) Hermite tensorization in the fixed coordinates (u, y) ∈ ℝ² × ℝ^{d−2}, together with ρ^{|α|+|β|} ≤ (ρ/q)² q^{|α|} for |α|+|β| ≥ 2, gives
  Σ_{m≥2} ρ^m ‖Π_m f‖² ≤ (ρ/q)² ∫⟨f_y, T_q^{(2)} f_y⟩ dγ(y).
(b) The Mehler feature-map diagonal bound gives ⟨g, T_q^{(2)} g⟩ ≤ (1−q²)⁻¹(∫|g| e^{a|u|²})².
(c) The sublevel ("bathtub") bound then gives (∫|g| e^{a|u|²})² ≤ C∫v|g| for |g| ≤ 1.
Step (c) is I38's margin principle (7.2), "slab mass ≤ C·width, hence mismatch² ≤ C·weighted loss", applied to a Gaussian tilted by e^{a|u|²} with a < 1/4 and to slabs that widen linearly. Dimension never appears, because the weight and the smoothing live in the fixed plane and the y-chaos factors are bounded by 1. Heilman SSC Section 8 lists dimension-dependent L∞ Hermite and heat-kernel bounds as the loss in his method. Those losses come from bounding T_ρ of the unknown optimizer's error set pointwise (SSC Lemma 5.1, (120)). An expansion around a fixed planar reference never requires such bounds. The difference lies in which object is expanded, not in a new estimate.

**R7. Coupling tails to the first-chaos calibration (classical + inherited).** The truncated A^N is a legitimate partition, so I38 applies to it unchanged. The one-line identity Δ(A^N) = 2B·J_N − ‖G‖² follows from Z_P = Bt. The calibration cost of changing frame is quadratic in the tail centroid b = ‖z(h)‖. This is Lipschitz stability of the polar factor at a matrix whose smallest singular value is ≥ B/4 (Procrustes; I38 (6.9) already uses the same polar decomposition). The vanishing tail coefficient b² ≤ e(R)·V is Gaussian integrability under the same tilted weight as in R6.

**R8. Absorption (classical).** Fix R from absolute constants, then choose ρ small, using Young's inequality for the cross term 2ab. All constants are I38's C₀, one- and two-dimensional Gaussian integrals, or compact Taylor constants depending on R.

**Composition.** R1–R8 yield the frozen inequality, together with the strict bound S_ρ(P) − S_ρ(A) ≥ c·ρ(J_N + V). The equality case follows because the weights are strictly positive almost everywhere. Every uniformity the frozen claim requires is accounted for:

| Uniformity | Source in the composed route | New estimate needed? |
|---|---|---|
| In k (extra labels, arbitrarily many tiny cells) | I38 calibration on A and A^N; for inactive labels q_i = 0 and the zero-score gap ≥ \|u\|/(2√3) (I38 (7.2) device); "two units per mismatch" bookkeeping | No |
| In d | Fixed planar reference; tensorization in R6; q_i depends only on u | No |
| In masses | The centered functional has no mass constraint; I38 has none either | No |
| Far tails | Exact smoothed score (Eldan/Heilman design); planar lower bound; integrability | No (explicit 2D computation) |
| Frame change after truncation | Polar-factor Lipschitz bound; three-label support fixed by the gap 1/√3 | No |
| Equality | Positivity of the weights almost everywhere | No |

## 4. Primary-literature comparison (bounded, exact hypotheses)

* **Heilman, *Euclidean Partitions Optimizing Noise Stability* (author SSC.pdf, SHA256 `6fe8cd4f…cb44`; EJP 2014).**
  * *Theorem 7.1:* for k = 3 and n ≥ 2 there is ρ₀(n, k) such that the propeller uniquely maximizes ψ_ρ = d/dρ Σ∫ f_i T_ρ f_i over the full simplex Δ₃(γ_n), with unrestricted masses.
  * *Theorem 7.2:* the equal-mass corollary, obtained by the fundamental theorem of calculus. The same integration gives the centered inequality S_ρ(A) = ∫₀^ρ ψ_α(A) dα ≤ S_ρ(P) for unrestricted three-label partitions at ρ < ρ₀(n).
  * *Method:* existence of a maximizer (Lemma 3.1, by convexity and weak compactness), first-variation containment (28), entry via (104) and Lemma 2.8, a small rotation, and then the iterated bootstrap Lemma 6.1, which has n-dependent constants (Lemmas 5.1–5.3).
  * *Section 8:* the problem is open for k ≥ 4, and the obstacle named there is the missing stability estimate. The author also states that dimension-independent error estimates "seem to be a difficult task".
* **Heilman–Tarter 2011.05583v2, Theorem 1.9.** For any ρ ∈ (0, 1), maximizers of fixed-mass noise stability (masses a_i > 0, m ≤ n+2) are (m−1)-dimensional. Theorem 1.10 combines this with [Hei14] for equal masses and k = 3. **Reduction I derived (a sketch, not certified):** a maximizer of the centered functional exists for fixed d and k = 3 by SSC's Lemma 3.1 argument. It maximizes the fixed-mass problem for its own masses, so HT 1.9 puts it in dimension ≤ 2. SSC Theorem 7.1 at n = 2, integrated as above, then gives the frozen theorem **for k = 3 with an absolute ρ₀ = ρ₀(2, 3)** and with the equality case. The k = 3 restriction of T096N126 is therefore essentially primary-paid, and it is d-uniform, which is stronger than the author's "dimension-dependent" description. For fixed k ≥ 4 the same route reduces d to ≤ k−1, but it then needs a k-label analogue of SSC Theorem 7.1. That analogue is not in the primary literature, and its constants would depend on k.
* **Heilman 2306.03312v3**, Theorem 1.5 (k = 3, equal masses, 0 < ρ ≤ .1082; unrestricted masses only for ρ < 0) and Section 8 (46)–(47). Its mean-subtracted spherical decomposition is maximized without any mass constraint. Section 1.5 explains that its rearrangement fails for four sets because the first-order optimizer is the propeller. This is consistent with the frozen target, but it supplies no transfer for k ≥ 4.
* **Heilman 2108.04950v1**, Theorems 1.6 and 1.12, Problems 1.10–1.11, Sections 1.3 and 1.7. These cover one set with fixed mass a, a centroid lower bound z₀, and a bounded smoothed penalty. Section 1.7 only states a belief about partitions. The bounded-tail design is credited (R5); no partition theorem is imported.
* **Eldan 1307.2781v3**, Theorems 1–2. These give a one-set, two-sided comparison between noise deficit and centroid deficit, with a |log ε| loss and the hypothesis ε < e^{−1/ρ}. According to Heilman 2108 Section 1.1 (Eldan's Section 1.1 was not read by me), the log factor cannot be fully removed. This is the primary reason a naive "noise deficit ≥ c·ρΔ" transfer fails, and why the bounded tail weight is needed. It is not an all-label transfer.
* **Heilman 2209.11216v1** (abstract read; full text not read). It gives a conditional Propeller-Conjecture-type result for four sets under a hyperstability hypothesis. It is not an unconditional or all-k result, so it does not make the theorem REDISCOVERED.
* **Heilman 1901.03934** (taken from the accepted R3 record, not freshly read). It uses the three-cell first-moment stability Lemma 2.8 as a penalty in a fixed-mass surface-area theorem. This is a further instance of the design "order-zero stability as the leading penalty".

No primary source examined proves the full frozen theorem, or the theorem for any fixed k ≥ 4. **REDISCOVERED is therefore not supported.** This rests on the bounded reading above and is not a worldwide claim.

## 5. Where an unpaid uniform compatibility estimate could hide

Each candidate location was examined directly. None was dismissed merely because its ingredients are elementary.

1. **Linear term in the tails.** The original feasibility failure is real: the remainder relative to the score gap tends to ρ along rays. The fix (R5) is a design that already exists in the primary literature, and its only input is an explicit planar inequality. Its 1/(1+|u|) loss is absorbed by e^{a|u|²}-integrability in R6 and R7. No dimension or label parameter enters anywhere.
2. **Higher chaos in d dimensions.** Tensorization in a fixed frame (R6(a)) is the entire d-uniform content. The estimate does not depend on the partition's geometry in the y-directions, because only |f| ≤ 1 and the planar weight are used.
3. **Arbitrarily many extra labels.** The proof does not estimate their collective activation. That job (R012's substantial (6.4)) is done inside I38's calibration, which the proof applies as a black box to A and A^N. For inactive labels, the linear term involves only q_i = 0 and the gap |u|/(2√3), the same device as I38 (7.2).
4. **Reselecting the frame after truncation.** This is a real logical point: one may not reselect the frame silently. The cost, however, is a standard first-order perturbation bound for the polar factor, and the cross term is quadratic in b. The fixed three-label support follows from the elementary separation 1/√3 between different supports.
5. **Order of constants.** R is chosen from absolute constants before ρ, and C′_R ρ ≤ c_*/4 is a final choice of ρ. This is ordinary.

For contrast, R012's substantial step needed a genuinely non-classical bound: aggregate activation of order E^{3/2} for arbitrarily correlated extra scores, beaten by an order-E normalization loss. No step of T096N126 has a comparable feature. Every step is either a black-box call to that already counted mechanism or a one- or two-dimensional Gaussian calculation in a fixed frame.

## 6. Strongest arguments for SUBSTANTIAL, and why they do not prevail

* *"The statement is new, and Heilman calls k ≥ 4 open and dimension-free estimates difficult."* Novelty of the statement in a bounded search is not the criterion. SSC Section 8 attributes the k ≥ 4 obstacle to the missing order-zero stability estimate, which R012/I38 has supplied and which has been counted. It attributes dimension dependence to a pointwise optimizer bootstrap, which a fixed-reference contender expansion does not use. Once the weighted calibration exists, the contender expansion is the natural route, and it closes with classical estimates.
* *"Naive linear-tail, three-label and fixed-mass shortcuts fail."* They do. Section 3 shows that the strongest compatible route does not use them, and its tail design is already present in the primary literature. A failed weaker route does not establish substantiality.
* *"The author found a single weight v that serves the tail penalty, the higher chaos and the tail centroid at once."* All three bounds use the same principle: tilted-Gaussian integrability of a weight that vanishes linearly on fixed lines. That this weight works in all three places is an observation, not a new estimate.
* *"Avoiding optimizer existence and regularity is a methodological advance."* It does simplify the argument relative to SSC and HT, but it is the standard way to use an exact quadratic expansion once a linear-in-weight calibration is available. I credit it as clean technique.

## 7. Prior objections and findings, retained

* Global entry Δ ≤ ρ only places A in a neighborhood. *Retained. This is R2, which is not counted as contribution.*
* Uniform Taylor remainders fail in far planar tails because exact smoothed scores saturate. This is a method diagnostic, not a counterexample. *Retained. R5 is primary-designed.*
* A fixed reference frame cannot be reselected silently after replacing tails. *Retained. Lemma 4.1 pays for the change, classically.*
* Fixed-mass dimension reduction gives m−1 dimensions, not elimination of arbitrary labels. *Retained. HT pays k = 3 (Section 4), and k ≥ 4 is paid by I38, not HT.*
* Heilman's unrestricted three-label derivative theorem already implies a centered three-label comparison. *Retained and strengthened: with HT 1.9 the threshold is absolute for k = 3.*
* Separate scalar rearrangements need not form a partition (I295). *Retained; not used.*
* No numerical or integrity check proves the analytic statement. *Retained. This review contains no numerical evidence.*

## 8. What would change this verdict

* If the correctness review finds that Lemma 2.1, 3.1 or 4.1 is false as stated and needs a genuinely new uniform estimate to repair, contribution should be reassessed against that repair.
* If a primary source were found proving the full theorem, the verdict would become REDISCOVERED.
* If the inherited I38 contract were narrower than stated in Section 2 (for example, valid only for some maximizing t, or requiring masses), the reduction would need re-examination. I found it to be exactly as used.

## 9. Validation performed

All validation was reading and reasoning. I independently reconstructed the integrated route (Sections 3 and 5) and the k = 3 primary corollary (Section 4, labelled a sketch). I ran no numerical experiments. Artifact anchors and integrity controls are described in `reading-limits.md` and the outside REPORT. They are not mathematical gates.
