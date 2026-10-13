# I220 — literature and contribution boundary

## Accepted source

OpenAI, *A counterexample to the Monge ansatz for the three-marginal Coulomb cost*, September 25, 2026, at the stipulated revision `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.

Pinned URL: https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-counterexample-to-the-Monge-ansatz-for-the-three-marginal-Coulomb-cost-September-25-2026/paper.pdf

Read all 749 lines of the existing I79 extracted copy in place, including Theorem 1.1; Lemmas 2.1, 3.1, 4.2; Proposition 4.1; all of Section 5; Proposition 6.1 and Lemma 6.2; Theorem 7.1 and its proof; references. A fresh retrieval of the pinned PDF, passed through `pdftotext -layout`, has exactly the same SHA256 as that existing complete text: `0c82801c83218d368b0edf839a3f4c32f3c3998a53e4e0d1dba3c96465ca5efe`. No duplicate manuscript copy was retained.

The source supplies nonattainment, the calibrated local branches and smooth marginal, and a separated-cell approximation with a linear cost-oscillation estimate. It does not state the BV/fractional tradeoff or quantitative regularity of an exact cyclic sequence. Its Riesz extension is Section 7 of the same paper, read completely; the family catalogue lists this same manuscript for family 373. No source theorem was challenged.

## Closest quantitative overlap — serious, not dismissed

Carioni, Del Grande, Iglesias and Schönberger, *From plans to maps: Nonlocal regularization of optimal transport*, https://arxiv.org/abs/2609.05062v1. Read the complete 859-line existing excerpt in place, covering introduction, the included portions of Section 2, and Section 4 including Example 4.6 and its proof. This is an excerpt, not the entire 36-page paper; omitted Section 3, later sections, and omitted portions of Section 2 were not read.

Example 4.6 proves the penalized excess scaling epsilon^{2/(2+q alpha)} for quadratic transport from one line segment to two separated segments. Its striped maps, jump condition q alpha<1, and interpolation lower bound are close prior art. Thus neither that exponent, the fractional jump threshold, nor oscillatory resolution of deterministic mass splitting is new here. Their model has two unequal marginal measures supported on segments. The I220 claim has smooth full-dimensional identical marginals, four competing branch images, a singular three-particle interaction, and exact order-three preserving maps with both powers controlled. Its lower proof uses branch measure domination by nu/2, not their one-dimensional primitive identity. No priority claim beyond this checked distinction is made.

## Exact images and vanishing gradient

De Pascale, Louet and Santambrogio, *The Monge problem with vanishing gradient penalization: vortices and asymptotic profile*, https://arxiv.org/abs/1407.7022v3, DOI 10.1016/j.matpur.2016.02.009. Read all 142 lines of the existing excerpt, including Theorem 1.1. Its Lipschitz-density theorem assumes two Lipschitz polar domains and Hölder densities bounded above and below by positive constants. Our disconnected target support and flat boundary densities do not satisfy these hypotheses. The abstract records an epsilon|log epsilon| regime in a different two-dimensional example. This paper establishes that exact-image regular approximation is prior work; it does not permit disregarding the support obstruction in I220. Full later proofs were not read.

Colombo and Di Marino, *Equality between Monge and Kantorovich multimarginal problems with Coulomb cost*, DOI 10.1007/s10231-013-0376-0, author version https://cvgmt.sns.it/media/doc/paper/2127/MultiColDim.pdf. Read all 210 lines of the existing excerpt: Theorems 1.1, 1.4 and 2.1; Lemmas 2.2 and 2.3 and their included proofs. Exact cyclic approximation for nonatomic identical marginals is already established. I220 does not nominate existence of such approximation; it nominates the sharp regularity/cost bound and concrete cycle with controlled jump costs. The rest of their paper was not read.

## Mixing and interpolation

Cinti and Otto, *Interpolation inequalities in pattern formation*, https://arxiv.org/abs/1509.01189, primary PDF https://cvgmt.sns.it/media/doc/paper/2778/interpola-paper-11.pdf. New retained excerpt: PDF pages 1–4, read completely, including Propositions 1.1–1.3 and their surrounding hypotheses. It establishes the established role of BV, negative norms and Wasserstein interpolation in energy scaling. Its proofs are outside the excerpt. I220 gives its elementary mollifier estimate directly and does not claim a new interpolation principle.

Seis, *Maximal mixing by incompressible fluid flows*, https://arxiv.org/abs/1309.0556, PDF https://arxiv.org/pdf/1309.0556. New retained excerpt: PDF pages 1–3, read completely (the extracted header says v1, September 2, 2013, with document date September 17, 2018). The introduction treats transport-distance and negative-Sobolev mixing measures under velocity-gradient budgets; no main theorem or proof beyond the start of Section 2 is included. It is background context only, not an invoked theorem or an exhaustive novelty exclusion.

## Coulomb smoothing is a different object

Bindini and De Pascale, *Optimal transport with Coulomb cost and the semiclassical limit of density functional theory*, https://jep.centre-mersenne.org/articles/10.5802/jep.59/. New excerpt: physical PDF pages 1–3 (cover, journal page 909 and 910), read completely. This only supports the subject and semiclassical context; no detailed smoothing theorem is claimed from that short excerpt.

Cotar, Friesecke and Klüppelberg, *Smoothing of transport plans with fixed marginals and rigorous semiclassical limit of the Hohenberg-Kohn functional*, https://arxiv.org/abs/1706.05676, PDF https://arxiv.org/pdf/1706.05676. New excerpt: physical PDF pages 1–4, read completely, including Theorems A and B. Their announced limiting objects are wavefunction densities and transport plans. That is not a construction of smooth deterministic maps with exact images. Later smoothing arguments were not read or invoked.

## Prior project overlap and nomination boundary

The I217 saved record already identifies I33–I35 as quadratic Brenier/entropic questions and I189 as a graph-theoretic patch problem. I220 read bounded leading sections of I33 (lines 1–45), I34 (1–35), I35 (1–30), and explicit keyword-matching lines in those reports and I189 dispositions. These support a bounded scope comparison only. No old experiment, validation script, review gate, or historical computation was replayed. No active I214 or other live task output was read.

The proposed contribution is the conjunction of: (1) quadratic control from the actual Coulomb/Riesz certificate in all four branch orientations; (2) a quantitative lower bound for arbitrary preserving pairs using exact branch domination, valid despite flat boundary density; (3) matching, explicitly defined three-cycle maps for one concrete smooth product-bump marginal, with global variation and fractional estimates for both powers; (4) a fixed positive obstruction for continuous, W^{1,1}_{loc}, and critical-or-higher fractional maps. General interpolation, equality of Monge/Kantorovich values, fractional thresholds, and the bare penalization exponent are excluded from the novelty claim.

The literature search is bounded, not a proof of first discovery. The parent contribution gate must decide whether this extension beyond the close two-marginal precedent is substantial enough. The proof gate must independently check the new deductions. No acceptance or new-to-literature verdict is preempted.
