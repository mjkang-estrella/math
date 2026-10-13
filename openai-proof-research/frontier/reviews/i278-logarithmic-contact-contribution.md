# I278 — first independent contribution review of logarithmic ball–slab contact

2026-10-12. **Verdict: SUBSTANTIAL**, for the proposed sharp nonlinear minimum over all finite-perimeter nested pairs, as one prospective finding. This is a contribution judgment, not a complete proof-gate verdict, acceptance, or worldwide-priority certification. Eleven findings remain accepted toward twenty; the original ten and R017 are unchanged.

The entire 141-line I275 candidate and its authentication were read. Its SHA256 matches the supplied `ab1a54ce81fc0047d05edc343ab6c65ac00e2a62fcc4515725df748c7aaf693f`. I274, I276 and its literature record, the accepted R017 theorem, completed I269 proof review/analysis, and I270 contribution review/analysis/literature were read for same-source overlap. I277 and I273 were not read. No independent proof verdict for I275 is assumed.

## Exact nominated result

For the unit cubic flat torus, fixed 1/(2π)<R<1/3, and sufficiently small positive ε, put

    L_R(ε) = min { P(E)+P(F)-4πR²-2 :
                     E ⊂ F a.e., |E|=4πR³/3, |F|=2(R-ε) }.

The class includes every finite-perimeter pair; both interfaces are free. The proposed conclusion is

    |log ε| L_R(ε)/ε² → 2π.

Constants may depend on fixed R. No endpoint uniformity, prescribed contact shape, symmetry, topology restriction, regularity of arbitrary near-minimizers, or full functional Gamma-limit is included.

Pinned family 354, Theorem `intro:main`, is stipulated true, including its BV equality classification. Its actual statement was read. The ball branch applies to the inner volume. The outer limiting volume lies strictly between 1/π and 1-1/π; above one half its complement still gives a coordinate slab. The limiting ball touches the slab at two poles. These facts establish the reference geometry, not the sharp deficit.

## What is classical, including moving contacts

The logarithmic law is not new. Independently read [Lacasse–Grest–Levine, v1](https://arxiv.org/pdf/mtrl-th/9603005v1), Section III and the continuation through equation (33), and [Lv, v2](https://arxiv.org/pdf/1704.05830v2), Sections 4.2–4.3 and Appendix B.2. The first paper's normalizations and equations (27), (29), (31), (33) give the rigid two-plate leading area excess 4πδ²/|log δ|. Lv's constant-volume force law corroborates it. These are source calculations, not a novel coefficient extraction by this project. Their rotational/contact-model setup should not be silently identified with the unrestricted torus pair problem.

Nor is “two moving interfaces” alone a sufficient distinction. The [original Morse–Witten publisher abstract](https://doi.org/10.1209/0295-5075/22/7/012) expressly concerns droplet–droplet contacts and energy of order f² log(1/f). The accessible statements of [Höhler–Weaire 2019](https://doi.org/10.1016/j.cis.2018.11.002) concern deformable contacting bubbles and volume-mediated coupling. Their full original calculations were inaccessible in this run; no exclusion theorem is inferred from those abstracts.

A stronger comparison was available in actual primary calculations: [Ginot et al., 1910.10029v1](https://arxiv.org/pdf/1910.10029v1), introduction and Sections 2.1–2.3, equations (3), (5)–(6), (10)–(21). Its linearized contact law has a self term f_i log(f_i)/(4π) and finite Green-function couplings between separated contacts. Thus multiple moving contacts, global volume constraints, and leading logarithmic self response are established precedent. Its stated weak-deformation, radial-force and contact assumptions, followed by simulation/experiment comparisons, do not supply the nominated BV minimum theorem. This comparison is stronger than the parent's rigid-wall distinction.

Equal sharing is also elementary: ½(a²+b²) ≥ ¼(b-a)². Combining that with local annular capacity predicts the half coefficient. The universal leading constant, logarithmic cutoff, radial-average inequality and harmonic-mean interpretation merit no separate finding.

## Honest overlap with accepted R017

R017 already pays for exact minimizing replacement, common two-volume correction before regularity, lattice comparison, uniform scalar quasiminimality, classical AFM improved convergence, reference-center normalization, and energy-controlled area remainders. Its argument adapts to a ball/slab pair because both limiting surfaces have free patches and the same equal-weight perimeter cancellations. The disconnected outer boundary and complementary volume branch are adaptations of that framework. I275 Section 3 is therefore predominantly inherited work; it cannot independently justify another substantial count.

R017 also already couples two moving interfaces by constrained Jacobi energy. Its complete contribution cannot be counted again under “free boundaries” or “all BV.” The relevant incremental question begins after the inherited graph reduction.

There is no parameter substitution in R017 that gives I275. R017 constrains a fixed equatorial circle, where compact H¹-to-L² trace convergence is available. Its coefficient uses a spherical trace capacity and the period-one cylinder resolvent. A point on a two-dimensional interface has zero H¹ capacity. Replacing the circle by two point values makes that limiting quadratic obstacle meaningless and would give no positive sharp cost. The slab is also a different scalar equality class, not a limiting radius in the tube theorem's interval.

## The real incremental burden

At I275's energy scale, centered graph H¹ norms are O(ε/√|log ε|). Dividing heights by ε therefore makes their global H¹ norms tend to zero, although actual inclusion still requires an order-ε relative displacement near a pole. A fixed point-trace passage or ordinary coercivity estimate cannot see this energy. Concentration on shrinking neighborhoods must be measured sharply, without postulating the actual contact radius or an axial profile.

I275 Sections 4–5 propose a substantive solution to that singular lower passage:

1. Actual inclusion is written at the same horizontal coordinate for the sphere and flat face. The exact identity W=Aψ∘F carries the full nonlinear radial graph into a vertical chart. Mere unscaled C1 convergence does not imply an additive o(ε) coordinate error, so this identity has a real purpose.
2. A fixed finite spherical-mode block is uniformly o(ε) by the global energy bound. Its nonnegative Jacobi energy can be retained or discarded. The complementary high block has a curvature-potential loss tending to zero as the cutoff increases, and its exact transformed gradients can be compared with the global spherical energy. This earns an arbitrarily sharp Dirichlet coefficient rather than a fixed coercivity constant.
3. Inclusion forces circle averages at radius c√ε, irrespective of the unknown true contact set. A separate outer radius has average o(ε) by the paid global L2 norm. Weighted Cauchy–Schwarz across the annulus sees the missing logarithmic cost. It does not evaluate an H1 function at a point.
4. The two polar constraints retain the relative axial shift h. The positive-part inequality (a+h)_+²+(a-h)_+²≥2a² prevents center drift from lowering the result without assuming h/ε bounded. Matching logarithmic recovery and exact free-patch volume corrections address attainment in the original nonlinear class.

Each tool is classical; neither the chart algebra nor spectral cutoff is claimed as a new general theorem. Their joint role is to connect an unrestricted nonlinear minimum to a concentrating obstacle cost with no prior contact-set ansatz. That step is absent from the paid R017 trace limit and from the actual primary droplet calculations read here. Its significance lies in the sharp lower bound for all original competitors through exact minimizing replacement, not in a surprising physical prediction or a long calculation.

## Duplicate and standard-corollary routes

No exact duplicate was identified in the read primary statements. This is a bounded finding, not evidence from search silence.

The strongest plausible standard route is: reuse the R017 reduction, invoke a general sharp small-contact theorem for stable constrained interfaces, and insert the two contacts/equal tensions. A theorem that handles C1-small nonlinear charts, sphere Jacobi potentials, translation/volume modes, arbitrary shrinking contact geometry and a sharp universal lower bound would make I275 an application. No such ready-to-apply theorem was established by this reading. Planar annular capacity by itself assumes the relevant inner/outer averages and controls only a positive Dirichlet form; it does not establish those hypotheses for the nonlinear minimizers. I275's exact chart and spectral steps are the unpaid bridge in that route.

The actual [ABLW Section 4.4, Theorem 4.5](https://arxiv.org/html/2212.06381v4#S4.SS4), independently read from its retained complete primary section, is a genuine logarithmic next-order Gamma-limit and tangent-shell selection result. Its nonlocal interaction selects positions of already perimeter-optimal round shells. Setting that interaction to zero preserves perimeter degeneracy; it does not force positive deformation of a ball by a narrowed slab. The same word “logarithmic” and tangent geometry do not yield this theorem as a corollary.

The pinned manuscript's complete retained slice-nesting section was also read. It improves ordered sections of one reflected CMC region at the cylinder/slab transition; its actual `nest:shape-gain` and `nest:area-bound` hypotheses are not those of this independently volume-constrained pair. It is credited upstream work, not a concealed version of the nominated limit.

## Objection, repair, and boundary of the verdict

The serious contribution objection is **double counting inherited all-BV machinery plus a classical logarithmic response**. The repair is to nominate precisely one theorem: the sharp nonlinear two-point ball–slab minimum over all BV pairs, and identify Sections 4–5's concentrating lower passage as the increment over R017. Credit R017's paired reduction and the original droplet literature explicitly. Remove any suggestion that logarithmic deformation, moving-contact sharing, classical capacity, or disconnected-slab regularity is independently new.

No further substantive contribution limitation was identified in the proposed mechanism at this gate. A smooth axial calculation alone would be TECHNICAL; it is not the full nominated theorem. This judgment does not certify the proposed chart estimates, parameter order, upper containment or regularity adaptation. Those remain for the independent proof gate. If the all-BV sharp lower passage is not validated, the local calculation/recovery cannot retain this SUBSTANTIAL classification by itself.

Full original Morse–Witten/Höhler–Weaire proofs, general shape-sensitivity and contact-capacity literature beyond the bounded screen remain access/read limits. They constrain priority claims and are disclosed rather than replaced by the parent's interpretations. Detailed extents, retrieval failures and provenance are in the [reading log](../experiments/i278_logarithmic_contact_contribution/reading-and-failures.md), [analysis](../experiments/i278_logarithmic_contact_contribution/analysis.md), [literature](../sources/i278_logarithmic_contact_contribution/literature.md), and [authentication](../experiments/i278_logarithmic_contact_contribution/input-authentication.json).
