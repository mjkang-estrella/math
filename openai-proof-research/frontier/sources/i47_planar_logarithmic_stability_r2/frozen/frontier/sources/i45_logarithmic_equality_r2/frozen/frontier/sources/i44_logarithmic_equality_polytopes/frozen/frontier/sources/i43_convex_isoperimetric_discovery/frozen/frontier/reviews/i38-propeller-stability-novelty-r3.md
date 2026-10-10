# I38 propeller stability: independent significance and novelty review, round 3

**Recommendation: SUBSTANTIAL, as one candidate finding. Retain R2 PASS ORIGINAL WITHOUT REPAIRS.** The substantive contribution is uniform stability across the boundary where arbitrarily many labels disappear, obtained by combining a compactification of normalized Gaussian scores with a uniform cubic bound for activation of the extra scores. This is a bounded operation-level judgment against the sources examined here, not a worldwide-priority certificate or an acceptance decision. No accepted count, shared index, author file, or R2 file was changed.

I read the full author report and R2 review, the entire selected pinned Gaussian propeller manuscript, its relevant companion interface, the prior I30/I36 significance reviews and R011's final significance review. The comparison below does **not** award significance to equality classification, the endpoint extension of the source elimination, a fixed-three-cell exponent improvement, or the partition calibration by themselves. Those portions are technical. The reason for the recommendation is the remaining, quantitatively material transition from an exact finite optimizer theorem to stability with no lower bound on cell mass and no bound on the number of cells or ambient dimension.

## 1. Exact contract and proof status

Write (B=3/(2\sqrt{2\pi})\). For every finite (d\ge2\), (k\ge3\), and measurable partition (A=(A_1,\ldots,A_k)\) of standard Gaussian space, set

\[
 z_i=\int_{A_i}x\,d\gamma_d(x),\qquad
 \Delta=B^2-\sum_i\|z_i\|^2.
\]

Empty cells are allowed. Let (d_P(A)\) be half the sum of Gaussian symmetric-difference measures from a partition consisting of an origin-centered, planar, (120^\circ\) three-sector propeller, extended cylindrically in its orthogonal complement and padded with empty cells, minimized over orthogonal transformations and label permutations. There are no prescribed masses, translations, minimum positive masses, fixed ranks, or hidden upper bounds on (d,k\). Theorem P asserts

\[
 \Delta\ge c_Pd_P(A)^2
\]

with a single positive (c_P\). Its global constant is implicit through a strictly positive uniform gap; neither its value nor its optimality is claimed. The distance exponent (1/2\) is sharp already among three planar sectors. Consequences for mass outside three labels belong to this same finding. The Mahler screen and scalar Lieb–Thirring splitting example are not additional nominations.

R2 independently reconstructed the full analytic argument, including countable first-chaos moments, equality, residual determinants, endpoint elimination, Gram compactness, correlated activation, exact triangle/polar remainder, and calibration. I found no new mathematical gap while testing the significance interfaces. The alternative local estimate below is a comparison and simplification, **not a repair**. The original all-(d,k\) statement and original proof PASS stand.

## 2. What the pinned proof already pays

G denotes *The Gaussian propeller bound in every dimension*, September 24, 2026, at `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. The [selected manifest](../sources/i38_propeller_stability_novelty_r3/selected-pinned.json) records exact raw pinned URLs, Git blobs, SHA-256 and sizes. All eleven readable G artifacts were read, including `main.tex`, `extremizers`, `scalars`, `geometry`, `elimination`, `certificates`, the full kernel application, figures and references. The Unique Games companion's kernel-clustering interface was also read. Its discrete hardness reduction uses G's constant and supplies no Gaussian stability estimate; its unrelated PCP proof is not a dependency of P.

| Existing operation | Exact usable output | Consequence for this audit |
|---|---|---|
| G `extremizers`, Khot–Naor score duality | Normalized finite score inequality; optimal cells are winning-score cones; centroid pairing; merging gain (2\langle z_i,z_j\rangle\) | Already paid. Neither duality nor merging is a new I38 mechanism. |
| G `scalars` | At an exact extremizer: deletion/recentering, translation first variation, Ehrhard concavity, radius/mass lower constraints | These depend on optimality identities. They do not apply unchanged to arbitrary near-optimal partitions. |
| G `geometry` | For a smallest radius (t\) and three large competitors, a two-residual density bound and a three-by-three PSD inequality | The source already uses three large radii against one small radius. I38 must not claim that choice as new. |
| G `elimination` and exact certificates | Scalar contradiction after the radius/mass constraints and residual determinant estimate | R2 verifies that the endpoint (C=B^2\) retains the contradiction. Extending strict-superlevel elimination to equality is technical. |
| HJN strict four-cell analysis | Excludes the genuine four-cell optimizer; author Remark 1.4 specifies uniqueness | Supplies the finite equality endpoint. It is not itself an all-label near-optimizer remainder. |
| Classical triangle support/perimeter formula and Gaussian boundary margin | Three-cell shape coercivity and conversion of score regret into squared disagreement | Technical local geometry/calibration, not separately substantial. |

The explicit countable reduction is important to credit correctly. At a countable optimizing limit, I38 proves the strong centroid sum and equality identities, so that the source's residual calculation is available. Fix any three positive radii with minimum squared radius (c>0\), and send another positive radius (t\) to zero. The same determinant/PSD calculation gives

\[
 \tfrac32(c-t^2)^2\le10(3/\pi)^2t^2,
\]

which is impossible as (t\to0\). Thus the determinant obstruction, once its countable hypotheses are justified, already excludes infinite support. This is a concrete reduction of that substep to G, not merely the label “standard compactness.” I do **not** count this endpoint argument alone as substantial.

The subsequent compactification uses a familiar concentration-compactness pattern, but its actual uniformity must be paid. Sorting squared norms gives (\|v_i\|^2\le1/i\). A Gaussian union bound integrated above a threshold yields a tail maximum tending uniformly to zero; finite covariance blocks converge continuously. The limiting trace is at most one. Sharpness and homogeneity give (M(v)\le B\sqrt{\operatorname{tr}G}\), so a limit with maximum expectation (B\) must retain trace one. The countable equality classification then forces three equilateral scores. This establishes a uniform neighborhood-entry gap across growing (d,k\), rather than taking an unjustified infimum of fixed-(k\) gaps. Tail Chernoff integration and finite covariance continuity are ordinary tools; the contribution is their correctly matched changing-support interface. Equality classification alone would not supply a rate.

## 3. Why exact support elimination does not already solve stability

A literal uniform bound on the number of active cells of near optimizers is false. Here is an analytic test of that proposed reduction, not a counterexample to P.

Take normalized equilateral scores (t_1,t_2,t_3\) in a plane, with (\sum\|t_i\|^2=1\). For any (N\ge1\) and (0<E<1\), in dimension (N+2\) put

\[
 v_i=\sqrt{1-E}\,t_i\quad(i\le3),\qquad
 v_{3+j}=\sqrt{E/N}\,e_{2+j}\quad(1\le j\le N).
\]

Their total squared norm is one. Every score has an open winning cone of positive Gaussian measure: for a tail score take its orthogonal coordinate sufficiently large, the other tail coordinates small, and the planar coordinates near zero; for a head score take a sufficiently large vector in its sector and small tail coordinates. Each winning cell has a nonzero first moment, since its winning score is strictly positive almost everywhere. The maximum expectation satisfies

\[
 B\sqrt{1-E}\le M(v)\le B.
\]

For its winning partition, score/partition Cauchy–Schwarz gives (F\ge M(v)^2\), hence (0\le\Delta\le B^2E\), uniformly in (N\). Thus an arbitrarily near-optimal partition can have arbitrarily many genuine nonempty, nonzero-moment cells. The source's minimum-radius bounds apply to exact extremizers and cannot be imposed on these partitions.

Merging does not remove this problem for free. It can improve the objective, but changing many labels can destroy the desired distance comparison unless their combined mass or score effect has first been controlled. Nor can fixed-(k\) compactness, HJN's finite mesh, or the (k-1\) dimension reduction supply a uniform constant by themselves. A proposed finite truncation must control the tail and its distance cost without assuming the very stability estimate being proved. I38 does this through the trace compactification and the local activation estimate, rather than through a false active-support bound.

## 4. The remaining bridge: a uniform boundary remainder

The local part is where the qualitative support reduction becomes a quantitative theorem. Center the leading three scores by their common mean (\mu\). Let

\[
 E=\sum_{i\ge4}\|v_i\|^2+3\|\mu\|^2.
\]

Inside the fixed neighborhood supplied above, the centered head support dominates (hR\) on its two-dimensional span, with the author's (h=1/(4\sqrt3)\). Here (R\) is the norm of a standard planar Gaussian. Each planar tail perturbation, including the head mean, is bounded by (2\sqrt E\,R\), absorbable into (hR/2\). What remains consists of arbitrarily correlated orthogonal Gaussian scores, independent of this planar Gaussian. Their **combined covariance trace**, not their count, is (O(E)\).

The author bounds their activation by (400E^{3/2}\). Since normalizing the head costs order (E\), the activation is of strictly smaller order and can be absorbed uniformly. This is the missing estimate: the new cells live near the codimension-two junction, where available planar Gaussian area is quadratic in the perturbation amplitude, and the score gain has another amplitude factor. It proves that an unbounded number of almost-empty cells cannot cancel the normalization penalty. A generic first-order Gaussian maximum bound would be (O(\sqrt E)\), which is insufficient.

The estimate is elementary once its geometry is identified. To avoid overstating novelty of the particular covariance-trace packaging, here is an independent equivalent bound. Put (A=\max_{i\ge4}|W_i|\), (b=|W_0|\), where (W_i\) are the orthogonal tail scores and (W_0\) is the orthogonal common head mean. Condition on all these variables. Using the Rayleigh density (r e^{-r^2/2}\le r\),

\[
 \mathbb E_R(A+b-aR)_+
 \le\int_0^{(A+b)/a}(A+b-ar)r\,dr
 =\frac{(A+b)^3}{6a^2},\qquad a=h/2.
\]

No independence among the (W_i\) is used. If (c_3=\mathbb E|G|^3=2\sqrt{2/\pi}\), then

\[
 \mathbb EA^3\le\sum_{i\ge4}\mathbb E|W_i|^3
 =c_3\sum_{i\ge4}\operatorname{Var}(W_i)^{3/2}
 \le c_3\left(\sum_{i\ge4}\operatorname{Var}(W_i)\right)^{3/2}.
\]

Together with ((A+b)^3\le4(A^3+b^3)\), this yields the bound (128c_3E^{3/2}<400E^{3/2}\) under the same local hypotheses. It treats the common mean once, rather than once per label. Thus a carefully organized sum of single-label third moments **can** be uniform; any suggestion that per-label estimates are inherently incapable of doing so is too strong. This does not invalidate the author's proof or remove the need for the cubic activation argument.

G's residual triangle integral is the closest antecedent: it also exploits a two-dimensional density bound and a cubic positive-part integral. Its operational input, however, is an exact centroid identity and negatively correlated residual competitors at an extremizer; its output is a determinant constraint excluding that extremizer. In the local estimate above, the tail correlations are unrestricted, there is no centroid stationarity, and the output is an upper bound for the **aggregate change of the objective** in terms of total tail energy, small compared with the head's normalization loss. Neither substituting a smaller radius into G's determinant conclusion nor applying its elimination inequalities pays this estimate. The new step is this boundary-energy comparison, not the formula for a Gaussian third moment or the power-counting integral in isolation.

Once that estimate is supplied, the rest is a short technical chain: the exact triangle formula pays the singular-value imbalance ((\alpha-\beta)^2\); polar alignment turns (E+(\alpha-\beta)^2\) into squared score distance; the squared pairing identity pays partition regret; three active boundary margins, with the zero-score competitor accounting for all inactive labels at once, give squared label disagreement. The sharp sector perturbation establishes the distance exponent but creates no second mechanism. This operation-level separation is why I recommend the complete result as substantial while declining to count its routine components separately.

## 5. Strongest primary comparisons

Primary payloads, HTTP responses, version histories, failed requests, and opened passages are retained in the review's [sources](../sources/i38_propeller_stability_novelty_r3/). The following are proof comparisons, not abstract-only exclusions.

**Khot–Naor, *Approximate kernel clustering*.** The author PDF and current arXiv history (0807.4626, latest v2) were checked. Lemmas 3.1–3.3 give finite existence, projection to the span of centroids, and merging/minimal support; Corollary 3.4 computes the planar constant; Lemma 3.7 proves Gaussian-score duality by centroid pairing and Cauchy–Schwarz. Projection reduces dimension to at most (k-1\), and merging reduces an exact optimization problem. These operations do not bound the label disagreement caused by merging a near optimizer. The source supplies the duality contract used in the active-support example above, but no changing-support remainder. [Primary author PDF](https://web.math.princeton.edu/~naor/homepage%20files/kernel.pdf).

**Heilman–Jagannath–Naor, *Solution of the Propeller Conjecture in (\mathbb R^3\)*.** I compared arXiv 1112.2993v2 with the Princeton author PDF, including author Remark 1.4, the geometric stationarity identities, degeneration exclusions, Lemma 4.1, and the strict finite-cover computation with error controls. The uniqueness interface is explicit in the author version and omitted in the corresponding v2 introduction; R2 checked the proof interface rather than inferring uniqueness from a non-strict inequality. Its quantitative strict margins concern exact stationary four-cell configurations after geometric exclusions. They do not provide a uniform neighborhood for arbitrary growing lists. The finite computation was not rerun here; the paper and its accepted interface are not re-proved by I38's diagnostics. [Author PDF](https://web.math.princeton.edu/~naor/homepage%20files/PropR3.pdf), [v2](https://arxiv.org/abs/1112.2993v2).

**Heilman 2014, *Euclidean Partitions Optimizing Noise Stability*.** Lemmas 2.5–2.8 and the full proof of 2.8 are the direct quantitative predecessor. For three cells, with the same first-moment deficit and small deficit assumption, the bound is (d_2\le6\Delta^{1/8}\). Since squared (L^2\) distance of partition indicators is total symmetric difference, (d_2^2=2d_P\), so it gives (d_P\le18\Delta^{1/4}\). The proof moves a partition to its centroid-score partition, then controls angular near-stationarity; its successive norm estimates lose powers. Direct triangle coercivity and squared pairing improve this three-label rate without the new all-label issue. I would classify that restricted improvement alone as technical. The later feedback argument concerns exact small-positive-correlation optimizers; it does not estimate the cost of arbitrarily many extra labels. [SSC.pdf](https://www.stevenheilman.org/~heilman/papers/SSC.pdf).

**Heilman 2306.03312v3 and author `corthreev3.pdf`.** Theorem 1.5, the complete angular proofs of Lemmas 3.3/4.1, circular rearrangement Lemma 6.1, and the proofs ending at (53)/(65) were compared. Positive correlation uses three equal-mass cells; the negative branch has a different, unrestricted-mass statement. The angular/radial penalties are genuine quantitative antecedents, but remain three-label estimates. The paper itself explains the failure of its spherical rearrangement extension at four labels. Displayed radial-mass penalties also vanish for radius-dependent rotations of three equal arcs, so that display alone is not a full orientation-distance estimate. Full rearrangement information, rather than just the penalty, must be retained. These operations could pay portions of the local three-label analysis after a justified uniform reduction; they do not supply that reduction or the extra-score activation bound. [v3](https://arxiv.org/abs/2306.03312v3), [author version](https://www.stevenheilman.org/~heilman/papers/corthreev3.pdf).

Version hygiene matters here. I used the actual v3 and author-version payloads, keeping them separately. In the inspected texts the introductory positive coefficient is (-.3+3(\rho+\rho^2)\), while the analytic proof reaches (2.5(\rho+\rho^2)-.109\) before the subsequent numerical improvement. The negative branch has its own coefficient and sign convention. No coefficient from another version, introductory claim, or sign branch is substituted into P; none is needed as a premise of P.

**Stable bubbles, dimension reduction, hyperstability, robust Borell.** These are serious stability methods, but their actual interfaces differ:

- In [1901.03934v1](https://arxiv.org/abs/1901.03934v1), Theorem 1.6 bounds perimeter deficit below by a multiple of a centroid deficit for fixed prescribed masses. Example 1.7 uses the older three-cell rate. The full Lemma 13.1 calculation cancels the two second-variation centroid terms for the cylindrical shear; it is not an extra-label coercivity estimate. The perimeter-to-centroid inequality cannot be reversed to obtain P.
- In [Heilman–Tarter 2011.05583v2](https://arxiv.org/abs/2011.05583v2), Theorem 1.9 and its translation-variation proof reduce an exact fixed-(m\) maximizer to dimension (m-1\). Rank-nullity and vanishing normal components use exact stationarity. They supply neither a uniform reduction to three labels nor a distance bound for near maximizers.
- In [2209.11216v1](https://arxiv.org/abs/2209.11216v1), the conditional propeller result is for (3\le m\le4\) under hyperstability. Lemmas 8.1–8.3 derive dilation invariance through second variations and then classify low-dimensional cones. Arbitrary near-optimal partitions do not satisfy the additional variational hypothesis.
- In [2108.04950v1](https://arxiv.org/abs/2108.04950v1), Theorem 1.6 and the dimension-reduction/penalization proof concern one set compared with a halfspace of fixed measure, with a positive centroid lower parameter. Its variational estimates are not a multicell, vanishing-label version of P.

**Gaussian width and current vector-max results.** Kabluchko–Litvak–Zaporozhets [1511.08479v3](https://arxiv.org/abs/1511.08479v3), including Proposition 1.1 and its support-function proof, treats unit variances. Böröczky–Fodor–Hug [2001.10706v1](https://arxiv.org/abs/2001.10706v1), Theorems 1.3–1.6, the isotropic finite-support reduction, and the reverse-Brascamp–Lieb proof interface of Proposition 7.1, treat John/Löwner or centered isotropic normalization. Their symmetric successor [2410.11460v1](https://arxiv.org/abs/2410.11460v1) similarly uses even isotropic measures and dimension-dependent constants. I38's scalar trace constraint is not isotropy; whitening can be arbitrarily ill-conditioned at rank two and changes the objective.

Two current 2026 comparisons were also checked. Mulgund [2607.14087v4](https://arxiv.org/abs/2607.14087v4), Theorem 2.1 and its proof, compares common-threshold orthants for unit-diagonal covariance with a PSD constraint; its equality result supplies no trace-normalized vanishing-label remainder. The full quantitative interpolation argument in [2609.38904v1](https://arxiv.org/abs/2609.38904v1), Theorems 1.1–1.3 and Section 2, gives stability for Gaussian partition-function moments with unit variances. Its quantitative (q>1\) bounds concern a different extremal direction from the free-energy maximum problem, and their coefficients depend on the moment/temperature/label parameters. Coordinatewise variance normalization changes I38's maximum and its trace budget. These papers do not already imply P. Their results are compared as prior-art interfaces, not imported as new premises.

**Generic stability and clustering.** Carlen [1609.00936v1](https://arxiv.org/abs/1609.00936v1), Theorems 3.2/3.3 and proofs, transfers an already established stability estimate through quantitative duality; its hypotheses include primal stability. Its discussion of the Bianchi–Egnell method explicitly separates local remainder control from compactness. Applying that architecture here still leaves I38's two central obligations. It cannot create uniform coercivity from equality classification.

Le Gouic–Paris [1801.09419v2](https://arxiv.org/abs/1801.09419v2), Definition 2.1 and full main proof through the separation step, obtains a quadratic quantizer-distance remainder under an absolute margin condition: a neighborhood of Voronoi boundaries has zero probability, together with uniqueness under perturbation. Standard Gaussian measure has positive mass in every such nonempty neighborhood. Levrard [1801.03742v2](https://arxiv.org/abs/1801.03742v2), Proposition 5, uses bounded support and a margin/minimum-cell-mass contract; its constants expose that dependence. More basically, optimal (k\)-means uses normalized conditional centroids and a mass-weighted center norm, whereas P uses unnormalized first moments. No exact identification of the objectives is available. These generic clustering estimates therefore do not bypass the support boundary.

## 6. Gate decision and its limits

The comparison with I30 and I36 is specific. I30's allegedly missing all-subset square-root volume principle was exactly Clarke's existing lemma, followed by the already available packing operation. I36's allegedly missing common physical windows and multivariable signatures were already operational in the prior physical-clipping and parameter-partition proofs, and the pinned routing amplifier paid the remaining cost. Those reviews could give explicit reductions with no unpaid analytic input.

Here a sizeable portion admits the same kind of reduction: G already pays the determinant obstruction; standard Gaussian tail integration pays continuity; triangle geometry and squared pairing pay the three-cell/calibration portions. After crediting all of those, a real uniform boundary estimate remains. The relevant exact-extremizer identities do not hold for arbitrary near optimizers, and near optimizers can have unbounded active support. The cubic activation argument resolves this obstruction and makes a uniform quadratic remainder possible. Its proof uses elementary ingredients, but the output is stronger than the separate inputs' available operational contracts. This is comparable in kind to R011's new compensation/induction connection, rather than a claim that every newly assembled inequality is substantial.

I therefore recommend **SUBSTANTIAL for the complete uniform theorem**, not DUPLICATE, TECHNICAL ONLY, or GAP. A primary result already establishing trace-normalized Gaussian-score stability across disappearing labels, or an explicit reduction that supplies the aggregate activation/normalization comparison without a new boundary estimate, would change this recommendation. I have not found such a result in the bounded search below. That absence is supporting context; the affirmative justification is the identified and validated missing operation, including the active-support obstruction to the tempting simpler reduction.

Supported novelty wording is:

> Relative to the pinned Gaussian propeller proof and the primary quantitative predecessors compared in this review, I38 establishes a dimension- and label-uniform quadratic deficit bound without mass constraints. Its additional mechanism controls changing support: compactness prevents trace escape, and a cubic aggregate activation estimate makes vanishing extra labels subordinate to the quadratic normalization cost. The precise worldwide priority of this theorem or mechanism is not certified.

Do not describe P as the first quantitative propeller theorem, the first Gaussian partition stability result, a new determinant inequality, a sharp-constant theorem, or an effective computation of the global gap. No stronger variant is substituted for the theorem reviewed, and no future variant is counted.

## 7. Evidence, search scope, and reproduction

The original discovery/R2 briefs and objections, the superseding full R3 brief, reports, gate reviews, source pin, complete inventory, ledgers and parent verification records are frozen in [input-manifest.json](../sources/i38_propeller_stability_novelty_r3/input-manifest.json) and `full-brief.txt`. The prior-byte checkpoint covers 161 author/R2 files. The original and R2 verifiers were rerun with their output writes intercepted, preserving all 161 bytesets; no seal was refreshed. Their exact diagnostics and noncertified numerical rows retain their original status. In particular, floating quadrature is not analytic proof, and none of these runs reruns HJN's many-hour proof computation.

The new corpus audit verifies all **9,340 files / 141,349,121 bytes**, including SHA-256 and Git blob identities, against the reused read-only corpus manifest. It searches the complete **13,223-entry / 749-manuscript** pinned inventory and all cached texts. It does not use the stale 719-entry contents list as its coverage denominator. Exact patterns and all matches are in `corpus-search.json`: propeller matches occur in seven files, centroid/stability proximity in four, Gaussian-max/width proximity in 55, and the intentionally broad support/compactness pattern in 1,101. These counts are mechanical coverage, not semantic review of every match. I inspected all direct propeller matches, the Gaussian-max/centroid match lists, the complete selected G proof, and the relevant companion interface. Broad unrelated matches were not all read as proofs. The separate project screen covers 111 Markdown files in iterations/reviews/findings; only I02, I38/R2 and the iteration ledger match the specific propeller/first-moment screen. I02's hit is an unrelated Gaussian-integral upper bound in its cross-field screen, not a propeller theorem.

Six web-search request/response snapshots, 39 full fresh primary HTTP responses (including one retained 404), sixteen current-version pages, and the extracted texts are retained. Current pages establish the exact version numbers used; initial older KLZ/Mulgund PDFs were superseded by v3/v4 and remain identifiable. The guessed `corthree.pdf` request returned HTML/404, was excluded, and was replaced by the correct author `corthreev3.pdf`. Search engines returned substantial irrelevant mechanical-propeller material; those responses are preserved rather than silently treated as exhaustive mathematical coverage. Search time was October 9–10, 2026 UTC. Cached dates do not prove priority. No subscription-only comprehensive citation search or semantic reading of all 749 papers is claimed.

`read-log.json` records actual opened byte-line spans and hashes; `manual-read-scope.json` supplements earlier direct full-text reads. Primary comparisons are contracted in `comparison-contracts.json`; primary identities and complete requests retain version distinctions. The small independent diagnostic checks 859 exact rational identities/inequalities for the active-support family and the radial-integral comparison. Its finite checks validate bookkeeping, not the infinite analytic argument or significance judgment.

Run from `/home/mj-kang/Documents/Dev/math/openai-proof-research`:

```bash
python -B frontier/experiments/i38_propeller_stability_novelty_r3/check.py
python -B frontier/experiments/i38_propeller_stability_novelty_r3/reproduce_prior.py
python -B frontier/experiments/i38_propeller_stability_novelty_r3/verify.py
```

The combined verifier checks the review seal, frozen inputs, selected pinned identities, full corpus identities/search reproducibility, retained primary response bodies, read passages, new exact diagnostics, and both prior verifiers with intercepted writes. Live shared-ledger drift is reported separately from immutable dependency drift; it cannot be hidden by refreshing frozen inputs. Downloaded primary PDFs/text/HTML remain ignored caches under the review-local ignore policy. The seal excludes itself and explicitly regenerated outputs. Do not run the one-time bootstrap/packaging scripts to refresh evidence after sealing.

**Final disposition: SUBSTANTIAL recommendation for one uniform stability finding; original R2 proof PASS preserved; no repairs, no count change, no priority certification.**
