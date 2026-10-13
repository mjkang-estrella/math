# I278 contribution analysis

2026-10-12. **SUBSTANTIAL for the full proposed theorem; no proof-gate verdict.** The candidate is authenticated. This analysis tests incremental mathematical burden against the completed R017 chain and independently read primary contact calculations. It does not assume that I275 has passed correctness review.

## 1. Geometry and exact scope

The target is a limit of minima for all BV nested pairs on the unit cubic T3, with inner volume 4πR³/3 and outer volume 2(R-ε), fixed 1/(2π)<R<1/3. Pinned Theorem `intro:main` supplies the two separate minima 4πR² and 2 and their equality classes. Its truth is stipulated.

The inner ball radius is below the ball/tube transition radius 1/3. For fixed R the outer volume remains strictly on the slab branch, since 1/π<2R<2/3<1-1/π. A complement of a coordinate slab is again a coordinate slab on the periodic circle, with the appropriate width and shifted center. Thus crossing volume one half changes neither the two-face reference boundary nor its local contact geometry. No endpoint-uniform constant is needed.

Inclusion at limiting equality forces the ball's axial center midway between slab faces. Transverse translation can be fixed by a common translation, since the reference slab is transversely invariant. At positive ε separate scalar optimizers do not fit. Qualitative positivity of the minimum does not compute its scale.

For comparison, the undeformed ball loses two caps of height ε outside the centered thin slab. A spherical cap of height d has volume πd²(R-d/3), so the lost volume is 2πε²(R-ε/3). This is an elementary hand calculation, not a numerical scan. Squared volumetric-asymmetry information at that obstruction scale would be of order ε⁴, far below ε²/|log ε|. A quantitative contact-energy passage is necessary.

## 2. Classical prediction and normalization

Lacasse–Grest–Levine's relative area variable is e=A/(4πR²)-1 and plate compression is x=δ/R. With X their small facet parameter, e∼-4X²log X and x∼-2Xlog X; hence e∼x²/|log x|. At fixed R this yields A-4πR²∼4πδ²/|log δ|. Their force and displacement relations give the same result. The inference is asymptotic elimination of the source parameter, not a new theorem.

Lv's constant-volume equation (4.15) relates half-height loss to F times a logarithm with coefficient 1/(4πγ). Work against two approaching plates gives the same rigid leading area response. The full elliptic remainder proof was not independently verified; these sources are used as prior calculations, not as a correctness premise for I275.

In a planar annulus, cutoff capacity is 2π/log(b/a). Taking a∼√ε gives 4π/|log ε| at leading order. Four moving patches, each with half-area energy and amplitude ε/2, give 2πε²/|log ε|. This is precisely the elementary sharing of a prescribed relative gap; it cannot earn the contribution verdict.

Primary moving-contact theory is closer than rigid compression alone. Ginot et al. derive a finite-contact displacement law whose self compliance diverges logarithmically, whereas interaction between contacts at fixed angular separation has finite Green coefficients. The dominance of the local logarithm and lower-order global coupling is established physical/mathematical-model precedent. The distinction that survives is rigorous optimization over the entire nonlinear BV class, not the existence of two deformable surfaces.

## 3. What R017 already buys

The inherited exact-minimizer argument avoids needing to regularize arbitrary input competitors. A global paired minimum lower-bounds every original pair. Smooth limit free patches give an invertible two-volume flow Jacobian for measurable nearby pairs, before they are graphs. A common flow preserves inclusion. Intersections and unions make arbitrary scalar competitors into nested pairs, and perimeter submodularity gives scalar comparisons after correction. Classical AFM then provides global small normal graphs. The equal perimeter weights are essential to this cancellation.

These steps were independently paid in I269 and credited as part of the accepted R017 contribution by I270. I275's slab version has different free patches and centering details but is an adaptation, not another discovery of the paired lemma. AFM's statement has no connected-boundary requirement. Its underlying regularity proof was not newly read here.

Sphere exact-volume expansion, removal of translation modes, Poincare control of zero-mean flat faces and small-C1 energy remainders likewise use the same framework. The recovery's free-patch volume bumps are standard exact corrections. None should be nominated independently.

## 4. Why the remaining lower passage is not R017's corollary

R017's relevant trace is on a fixed equatorial circle. Its rescaled displacements have bounded H1 norm and compact L2 traces, so a fixed obstacle survives weak convergence. The sphere/cylinder Jacobi resolvents determine its coefficient, including global periodic geometry.

For I275, an upper bound of order ε²/ℓ and spectral coercivity give H1 heights of order ε/√ℓ, with ℓ=|log ε|. Rescaling heights by ε makes the global H1 norm vanish. Nevertheless the actual geometry demands order-ε separation near a pole. This is consistent because a point has zero H1 capacity in two dimensions. Enforcing a point value in the weak limit would be invalid; simply inserting poles in the R017 trace functional gives no lower cost.

The candidate must therefore bound concentrating gradients while allowing low smooth modes to disappear. Its decomposition at a fixed spectral cutoff N gives a finite low block with C1 norm O_N(ε/√ℓ)=o(ε). The constant mode is smaller by the exact volume equation. The high block retains the contact constraint at leading order while the negative sphere potential costs a relative O(N^-2) fraction of its Dirichlet energy. Taking N large before the sequence limit, after fixing chart/Young-inequality parameters, can recover an arbitrarily sharp energy coefficient. A fixed coercivity estimate loses that coefficient.

The exact multiplicative chart identity is also substantive in this passage. From the actual radial boundary, z²+|x|²=(R+ψ)², subtracting the reference square root gives W=Aψ∘F exactly. A and F depend on the full graph, including low modes. Carrying the high part through that actual map retains a uniform o(ε) low-part error without demanding that arbitrary chart remainders be o(ε). The proposed derivative bound includes the product term k∇A; the high-mode L2-to-gradient inequality is what pays it. One cannot drop it merely because the original graph is C1-small.

This scrutiny identifies why Sections 4–5 are real mathematical work. It is not a complete certification of every chart domain, metric inequality or constant.

## 5. Shrinking circles rather than presumed contact patches

Actual inclusion yields V-W ≥ ε±h-[R-√(R²-|x|²)] at the same x. On a circle of radius c√ε the last term is (c²/(2R)+o(1))ε. After removing the finite low modes, the mean of Z=V-W_high is bounded below by (1-c²/(2R)+o(1))ε±h. No assertion about the actual contact-set radius is used.

The local L2 bound gives an outer circle between δ and 2δ with mean o(ε). The radial average inequality then gives a sharp annular cost for the positive part of the inner-minus-outer mean. Since log(b/(c√ε))=ℓ/2+O_(c,δ)(1), the leading coefficient for each relative Dirichlet energy is 4π/ℓ. Combining ½(|∇V|²+|∇W_high|²)≥¼|∇Z|² with both polar inequalities gives the candidate 2π coefficient.

The axial center is a zero-energy reference freedom but affects actual inclusion. Retaining ±h and using positive parts avoids assuming h=O(ε) before paying for it. The inequality for the two positive parts is valid even when one contact constraint is negative. This handles a route by which a one-pole calculation alone could misstate the minimum.

The four-patch logarithmic upper construction makes this lower coefficient attainable in actual shapes if its proposed containment and correction estimates pass the proof gate. Its core radius √εℓ is a buffered recovery choice, not a predicted exact contact radius. Changing that radius by a subpower logarithm changes only lower-order terms.

## 6. Strongest technical-application objection

After inheriting R017's reduction, only standard chart identities, spectral estimates and capacity remain. That makes I275 a concise specialization of a general singular-contact strategy. It does not make the nominated theorem a proved standard corollary: the strategy still needs a sharp nonlinear energy lower bound and a geometrically supplied shrinking-circle constraint. Classical planar capacity alone supplies neither. The zero-capacity contact transition breaks the existing trace proof rather than merely changing its coefficient.

A read general theorem giving this bridge for two stable interfaces would change the assessment to TECHNICAL or KNOWN depending on its scope. None was established. Conversely, the existence of unread general shape-sensitivity literature cannot itself establish either novelty or duplication. The bounded verdict is supported by identified unpaid steps, not by proof length or search absence.

ABLW's actual second Gamma-limit is another caution: logarithmic next-order contact selection is not new in rigorous variational analysis. But its local perimeter is already minimized by nested round shells; its second functional is nonlocal. Here the reference slab is forcibly narrowed, so the local perimeter itself must rise. The exact primary section does not permit direct substitution of this problem.

## 7. Disposition

The full proposed theorem is **SUBSTANTIAL** beyond accepted R017 and the actual primary comparisons. The repair is attribution and precise nomination: one all-BV two-point nonlinear minimum asymptotic, with the concentrating chart/spectral/capacity lower passage identified as the increment. The physical scale, sharing constant, regularity machinery, recovery alone and any alleged general capacity theorem are not separate findings.

The contribution judgment does not assume a proof PASS. No complete correctness decision, endpoint result, unequal-tension extension, dynamic implication, contact-set classification or full functional Gamma-limit is issued. Original Morse–Witten/Höhler–Weaire full-text access remains limited; their full arguments are not represented as independently read or excluded. No worldwide-priority claim is warranted.
