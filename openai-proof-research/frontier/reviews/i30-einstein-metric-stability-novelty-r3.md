# I30 original-metric almost-Einstein stability — final significance review R3

**Recommendation: TECHNICAL ONLY. Preserve R2's full-theorem proof PASS, without mathematical repairs.** I30 proves the stated universal original-metric power estimate relative to the stipulated corpus. I found neither an exact full-scope duplicate nor a new gap. The decisive additional prior art is **Clarke's Lemma 12**, which already proves the all-measurable-subset square-root volume estimate, with exactly the Cauchy–Schwarz and path-integration mechanism proposed as I30's refinement. Applied to EG's small-defect flow, that lemma supplies the revised error budget directly. Tian–Wang's actual proof supplies the remaining missing-ball, packing, and subdivision operations. The final local Einstein inversion uses established rigidity and spectral inputs.

This is a significance judgment under this project's substantial/nonroutine standard, not a judgment that the theorem is uninteresting or false. It is not a DUPLICATE verdict. No worldwide-priority certification, R012 designation, count increment, publication, or shared-index change is made. Five accepted findings, including R011, remain the supplied status.

Review date: 2026-10-09. All proofs at `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true. The immutable candidate has SHA-256 `a8bdb8937745dc57d89d5ee1562299a8a7d888f1e6816c833f28776a14ebe8a9`. This is a fresh significance review after independent proof PASS, not a replacement proof review. No agents were spawned.

## Exact theorem and strongest positive contribution case

For every smooth closed connected simply connected Riemannian four-manifold with

\[
 \sec_g\ge0,\qquad \frac1{\operatorname{Vol}_g M}\int_M R_g\,d\mu_g=12,
 \qquad D=\int_M|\operatorname{Ric}_g-R_gg/4|^2\,d\mu_g<\epsilon,
\]

there are universal positive constants \(C,\epsilon\) such that

\[
 \min_{h\in\mathscr H}d_{GH}((M,g),(M_h,h))\le C D^{1/16},
\]

where \(\mathscr H\) consists of the sectional-curvature-one round \(S^4\), Fubini–Study \(\mathbb{CP}^2\) with \(\operatorname{Ric}=3h\) (twice the unit-Hopf normalization), and the product of two curvature-three round two-spheres. The estimate concerns the **original** metric. There is no initial injectivity-radius, pointwise Einstein-error, upper-curvature, Kähler, or almost-Euclidean-ball assumption. Neither an optimal exponent nor an explicit smallness threshold is claimed.

The strongest case for substantiality is real. EG's advertised conclusion is diffeomorphism classification; even its stronger compactness proposition identifies positive-time slices. I30 obtains a uniform quantitative metric conclusion at time zero despite critical-norm concentration. Its constants are fixed before taking a sequence, its two-metric argument deals with possible short-distance distortion, and the equal product is treated by invertible elliptic linearization despite an unstable Ricci-flow direction. These are materially stronger conclusions than topology or qualitative compactness. The earlier I27 time-zero objection is actually resolved: the divergent tensor integral is stopped at a positive time, while a different integrable distance estimate reaches zero.

It would therefore be wrong to reject I30 merely because the ingredients are known, because its proof is long, or because a different theorem has a similar title. The significance decision below rests on a concrete reduction of each new operation, including the proposed improved volume budget, to already available proof interfaces.

## Stipulated corpus: remaining problem after strongest interfaces

I read the candidate and R2 in full, AGENTS.md, the ledger, the operative full review brief, and the relevant original I27 task/report and prior objections. EG's complete 863-line proof, E0's exact classification and equality/splitting proof, and E+'s complete classification section were read directly. Their local paths, Git identities and exact opened spans are recorded in the [selected source manifest](../sources/i30_einstein_metric_stability_novelty_r3/source-manifest.json) and [passage record](../sources/i30_einstein_metric_stability_novelty_r3/read-passages.json).

**EG** already supplies, with \(\eta=\sqrt D\), initial \(\|R-12\|_2\le4\eta\), \(\|\operatorname{Ric}-3g\|_2^2\le5\eta^2\), uniform volume/diameter/Sobolev bounds, noncollapse, high-curvature-tail absorption, common lifespan, and \(|\operatorname{Rm}(t)|\le A/t\). Its evolving Einstein-error energy inequality retains \(\|L(t)\|_2\le C\eta\); this is not merely qualitative convergence. Its negative-sectional-integral control identifies nonnegative Einstein limits without assuming preservation of \(\sec\ge0\). Proposition `prop:limit` gives smooth convergence on positive slabs after diffeomorphisms. The proof does not contain an original-distance defect power.

**E0/E+** identify the three normalized smooth models. E0 includes the zero-plane/product boundary; E+ alone does not. Their Weyl identities, equality cases, parallel tensors and global continuation are exact-Einstein arguments. No approximate original-metric estimate is concealed in those passages. Direct perturbation would introduce derivatives of the Ricci defect not controlled by its initial critical norm. I30's successful flow route bypasses that issue rather than solving a new approximate Weyl classification.

I reused the complete 749-manuscript/9,340-text-file inventory read-only. A fresh normalized full-text and title screen is retained in [normalized-corpus-screen.json](../sources/i30_einstein_metric_stability_novelty_r3/normalized-corpus-screen.json). This is mechanical screening, **not** semantic reading of the whole inventory. The strongest additional plausible companions were checked in actual text:

- **Bounded scalar curvature and smooth extension of four-dimensional Ricci flow:** its curvature-radius/geodesic lemma and good-material-points proof do control distances, so it cannot be dismissed on its title. They concern late-time concentration under a uniform scalar bound, with Ricci-improvement envelopes and selected good labels. The displayed control is relative to degenerating cluster scales and integrated envelopes. These hypotheses and rates are not EG's initial \(L^2\) Einstein defect.
- **Path selection and an elliptic inequality on degenerating Ricci-flat trees:** the actual tree inequality requires a fixed finite tree, order-20 end-metric bounds, order-10 weighted Ricci errors and compact vertex convergence. Its conclusion is \(E(g_j)=o(M_j)\), explicitly without a uniform power over trees. It retains deformation kernels. It supplies no stronger original-metric power in I30's class.
- **Universal-cover splitting for compact Kähler manifolds** uses specified compatible holomorphic splitting data; **Gigli's distributional curvature characterization** identifies an Alexandrov curvature condition. Neither is an almost-Einstein metric estimate.
- The October 7 **hypersymplectic deformation** theorem starts with a definite closed two-form triple and deforms it to a hyperkähler endpoint, preserving cohomology. It does not bound the original metric's distance to a positive Einstein model. The **bounded-scalar finite-time blowup** companion has a sufficiently high-dimensional sphere-product conclusion, not a four-dimensional almost-Einstein theorem. Other normalized search hits concern Lorentzian Penrose/Kerr geometry, incompressible transport, or rectifiability; the matched passages were screened as such.

Thus the relevant residual task is quantitative recovery of the initial metric from EG's existing global flow estimates, followed by quantitative local identification at a fixed smooth slice. This conclusion uses actual companion interfaces, not an inference from absence of an exact title.

## Primary literature and exact overlap

Fresh bounded searches and primary retrievals were performed on the review date. Current arXiv metadata confirms versions TW v1, CCL v3, HKRX v1, HW v2, Ma–Wang v1, Martens v2, Gursky–Viaclovsky v2 and Kröncke v2. The published TW 2015, HKRX 2020 and Ma–Wang 2023 PDFs were successfully retrieved and their decisive proofs read in this round. Earlier publisher 403s remain historical failures; they are not this round's access status. New primary responses, version histories, URLs, byte lengths and hashes are in [new-primary-manifest.json](../sources/i30_einstein_metric_stability_novelty_r3/new-primary-manifest.json). Previously pinned primary PDFs/texts are reused through the dependency manifest.

| Primary source and actual interface | Scope, strength and I30 comparison |
|---|---|
| [Tian–Wang, 1202.2912v1](https://arxiv.org/abs/1202.2912v1), and [published §4](https://www.ams.org/journals/jams/2015-28-04/S0894-0347-2015-00834-7/S0894-0347-2015-00834-7.pdf), Lemmas 4.3–4.4/Theorem 4.1 | Normalized flow \(-\operatorname{Ric}+\lambda_0g\), \(|\lambda_0|\le1\), initial almost-nonnegative Ricci and almost-Euclidean unit-ball volume. Error is spacetime scalar \(L^1\). Lemma 4.3 stops a singular integration using shrinking-distance control. Lemma 4.4 subtracts an inner later ball, excludes a missing initial ball, locates a later-ball point near an initial endpoint, and packs disjoint later balls along an initial geodesic. Theorem 4.1 uses fixed-time bounded geometry and subdivision. These are precisely the relevant operations, although its stated theorem cannot simply be cited for I30. |
| [Chan–Chen–Lee, 2102.12840v3](https://arxiv.org/abs/2102.12840v3), Theorems 1.2/1.4 and §5 | Initial Ricci lower bound, local entropy lower bound and small local full \(L^{n/2}\) curvature produce common-time smoothing with small curvature coefficient and initial-distance/Hölder comparisons. This is stronger than only positive-time compactness. In I30, \(\int_{B_g(x,r)}|\operatorname{Rm}|^2\le C(r^4+\eta^2)\) permits small concentration at a fixed sufficiently small scale. The resulting fixed-parameter Hölder equivalence does not itself give a model-distance power tending to zero with \(\eta\). |
| [HKRX published Lemma 2.4](https://www.ams.org/journals/tran/2020-373-11/S0002-9947-2020-08177-X/S0002-9947-2020-08177-X.pdf), arXiv:1808.03774v1 Lemma 1.11 | Initial Ricci lower bound and uniform almost-Euclidean/Reifenberg control yield smoothing and bi-Hölder comparison to time zero. The proof uses the small \(\alpha/t\) regime. Its multiplicative constants and exponents are not an additive defect-to-model modulus. The published numbering and hypotheses were verified, not inferred from a citation. |
| [Huang–Wang, 2008.09956v2](https://arxiv.org/abs/2008.09956v2), Appendix A | Initial scalar lower bound and doubling/Poincaré control, with a sufficiently small \(\alpha/t\) Ricci bound, give local time-zero distance comparison, including initially collapsing data. The proof's volume/ball containment and packing are additional antecedents, not an Einstein classification. A universal \(A/t\) with large \(A\) cannot silently be substituted for small \(\alpha/t\). |
| [Ma–Wang, published §5](https://www.ams.org/journals/btran/2023-10-27/S2330-0000-2023-00155-8/S2330-0000-2023-00155-8.pdf), Lemma 5.1/Theorems 5.2–5.4; arXiv:2109.02449v1 | The proof explicitly transfers TW's packing once curvature, noncollapse and injectivity estimates are supplied. The new analytic work establishes appropriate inputs from small negative-Ricci \(L^p\), \(p>m/2\), and almost maximal initial ball volume. I30's negative part is zero, but its almost-maximal ball input is not automatic. Their flow continuity theorem starts with GH closeness; it does not derive I30's closeness from \(D\). This is direct evidence of modular transfer of the distance argument. |
| [Martens, 2408.11115v2](https://arxiv.org/abs/2408.11115v2), Theorems 1.1–1.2/Remark 1.3 | Critical-curvature smoothing and metric-measure compactness do not there ensure recovery of the initial limit distance. I30 has extra uniform initial Ricci/noncollapse structure. It does not resolve the general initial-trace issue in that remark. |
| [Koiso, 1982](https://ir.library.osaka-u.ac.jp/repo/ouka/all/8420/ojm19_03_09.pdf), Lemma 2.4/Proposition 2.5; [Gursky–Viaclovsky, 1105.4648v2](https://arxiv.org/abs/1105.4648v2), slice discussion, Propositions 7.7/7.9 | These supply infinitesimal Einstein rigidity, slice machinery and the CP²/product spectral inputs. At Ricci 3, the CP² TT \(-\Delta_L\) bottom is 16. For the equal product it is 0 followed by at least 12; subtracting 6 leaves a negative invertible mode and a gap above zero. Thus elliptic invertibility is available without dynamical stability. |
| [Kröncke, 1312.2224v2](https://arxiv.org/abs/1312.2224v2), §8 | The dynamical stability theorem requires a local variational maximum and a strict scalar spectral condition. Its Łojasiewicz–Simon inequality controls an entropy gradient near a smooth model, not the original metric from a critical defect. It cannot justify attracting flow for the product. |

Further genuinely relevant primary checks were made. [Bamler–Zhang II, 1506.03154v1, Theorem 1.1 and its proof](https://arxiv.org/abs/1506.03154v1) gives strong time-distance estimates under a uniform spacetime scalar bound and an entropy lower bound. EG does not supply the former down to zero: \(R(t)\le C(1+\eta/t)\) is insufficient. [Bing Wang, 2010.09981v1, Lemma 5.2/Proposition 5.3](https://arxiv.org/abs/2010.09981v1) again uses the TW bridge, obtaining small spacetime scalar error from near-Euclidean entropy/volume assumptions. This gives a qualitative small distortion function under those inputs, not the needed uniform \(D\)-power by itself.

[Datar–Seshadri–Song's Kähler metric-rigidity result, 2010.10925v1, Theorems 1–2 and proof](https://arxiv.org/abs/2010.10925v1) concerns Kähler metrics with pointwise Ricci lower bounds and volume/cohomology conditions, and obtains qualitative GH conclusions using Kähler-flow structure. It is not an all-three-model critical-defect theorem. [Gioffrè, 1703.01846v2](https://arxiv.org/abs/1703.01846v2) has a quantitative almost-Einstein conclusion for convex Euclidean hypersurfaces; its constants depend on extrinsic curvature and diameter, and it uses the embedding. Those additional data cannot be supplied for I30's arbitrary manifolds. These comparisons do not establish that every possible stronger method is unavailable; they rule out the specific shortcuts checked here.

### The newly identified exact volume antecedent

[Brian Clarke, *The metric geometry of the manifold of Riemannian metrics over a closed manifold*, 0904.0174v2, Lemma 12](https://arxiv.org/abs/0904.0174v2), proves for **every measurable** \(U\)

\[
 \left|\sqrt{\operatorname{Vol}(U,q_1)}-\sqrt{\operatorname{Vol}(U,q_0)}\right|
 \le {\sqrt n\over4}\,d_{\mathrm{Ebin}}(q_0,q_1)
 \le {\sqrt n\over4}\int\|\dot q(t)\|_{L^2(q(t))}\,dt. \tag{C}
\]

Its proof differentiates material-set volume, applies the trace bound and Cauchy–Schwarz, divides by the square root of volume and integrates. This is the same operation as candidate (9)–(10), with no curvature assumption. The current metadata gives v2; the PDF's arXiv banner dates that version to 5 November 2010. A later generated date on its first page is not a new arXiv version. The retained page-8 render verifies the absolute value, measurable-set quantifier and constant; the following page completes integration. The older official MPI preprint was also retrieved, but the assertion here is pinned to v2 Lemma 12.

Here is the exact application, rather than an analogy. Put \(c(t)=1-6t\), \(q(t)=c(t)^{-1}g(t)\), and \(L=\operatorname{Ric}_{g(t)}-3g(t)/c(t)\). Then

\[
 \dot q=-2c^{-1}L,\qquad
 \|L\|_{L^2(q)}=\|L\|_{L^2(g)}\quad(n=4),\qquad
 \|\dot q\|_{L^2(q)}\le C\eta.
\]

The middle identity follows from the inverse-metric factor \(c^2\) in squared tensor norm cancelling the volume factor \(c^{-2}\). Choose EG's universal \(\tau\) with \(c\) uniformly positive. Formula (C) gives

\[
 \left|\sqrt{\mu_{q(\tau)}(U)}-\sqrt{\mu_g(U)}\right|\le C\eta\tau
 \quad\text{for every measurable }U.
\]

The path is smooth for each initial metric and has uniformly bounded L² length. Simply connected closed manifolds are orientable, so Clarke's background convention creates no obstruction. No initial pointwise estimate, control of the support, or fixed lower bound for \(\mu(U)\) is needed. **This identifies an exact prior lemma for the proposed structural refinement.** Ebin distance is a distance on the space of metrics, not GH distance: (C) alone does not prove I30. The packing step is still necessary.

## Minimal deduction graph and what remains new

The following is an input-to-output graph, not a chronology of the author's discovery. Constants are universal after fixing EG's threshold, time and geometry bounds. For \(\eta>0\) small, set \(k=q(\tau)\).

| Edge | Inputs → output | Source or remaining operation |
|---|---|---|
| A | Initial hypotheses → common flow, noncollapse, Sobolev, \(|\mathrm{Rm}|\le A/t\), \(\|L\|_2\le C\eta\), fixed-slice bounded geometry | EG's existing proof, including quantitative energy propagation. |
| B | A + positive-slab parabolic iteration → \(\|L(t)\|_\infty\le C\eta/t\) | Standard Moser iteration with the already uniform Sobolev and slab potential bounds; no estimate at zero asserted. |
| C | A's index-form shrinking estimate + B integrated only from \(s=\eta^2\) → \(d_k\ge d_g-a\), \(a=C\eta(1+|\log\eta|)\) | Classical integrable shrinking estimate plus a stopping-time substitution of the kind already used in TW Lemma 4.3. |
| D | A + normalized-path identity → all-set square-root volume error \(C\eta\) | Exactly Clarke (C), not a new material-set principle. |
| E | Initial Bishop upper bound + later sharp small-ball lower bound + C/D → two-sided original/later distance error \(C\eta^{1/8}\) | TW's hole/packing/subdivision proof with the revised volume budget; elementary scale balancing below. |
| F | EG's positive-time compactness + E0/E+ → membership of \(k\) in a fixed smooth neighborhood of one of the three models | Compactness contradiction gives a uniform sufficiently small threshold. No rate for neighborhood entry is needed. |
| G | F + \(\|\operatorname{Ric}_k-3k\|_2\le C\eta\) + known slice/spectral inverse → model GH error \(C\eta^{1/3}\) | Local elliptic inverse estimate, absorption, and interpolation with uniform spare regularity. |
| H | E + G + triangle inequality → original-metric \(CD^{1/16}\) theorem | Dominant exponent and \(\eta=\sqrt D\). |

The concrete transfer at E is worth spelling out. Initial Ricci nonnegativity yields \(\mu_g B_g(x,r)\le\omega_4r^4\); later bounded geometry yields \(\mu_k B_k(x,r)\ge\omega_4r^4(1-Cr^2)\). C gives the inclusion \(B_k(x,r-a)\subset B_g(x,r)\). D changes the outer ball budget to

\[
 \mu_k B_g(x,r)\le\omega_4r^4+C\eta r^2+C\eta^2.
\]

Subtract the inner later ball. The remaining volume is bounded by

\[
 H_r=C(r^6+ar^3+\eta r^2+\eta^2). \tag{H}
\]

A missing initial endpoint ball would consume more than this budget once its radius exceeds a constant times \(H_r^{1/4}\), with the additive distance allowance included. Coarse packing first gives \(d_k\le C(d_g+a+\sqrt\eta)\); it then converts the nearby endpoint supplied by the missing-ball step into a later-distance error. Subdivide an initial geodesic into steps of order \(r\). Its accumulated error is controlled by \(H_r^{1/4}/r+a/r\). Taking \(r=\eta^{1/4}\) gives \(H_r=O(\eta^{3/2})\), because the logarithmic term is strictly smaller, hence \(H_r^{1/4}/r=O(\eta^{1/8})\).

These are the candidate's actual operations; they do not require initial almost-Euclidean lower volume. The initial upper bound and later lower bound take the roles required by the proof. This explains why TW's stronger **proof interface** transfers even though its packaged local theorem has a missing hypothesis. Ma–Wang's explicit reuse confirms that the packing portion is already treated in the literature as independent of the particular route supplying smoothing estimates. I30 supplies those inputs through stipulated EG, so it does not reproduce Ma–Wang's hard work establishing smoothing from different integral hypotheses.

At G, a finite set of rigid smooth models and smooth neighborhood entry make all inverse constants uniform. On transverse-traceless tensors the fixed-constant Einstein linearization satisfies \(2P=-\Delta_L-6\). The product's eigenvalue \(-6\) is invertible; positivity is unnecessary. Gauge, scalar/trace control and elliptic absorption are the usual local rigidity argument. R2 checks the spare regularity needed for the slice. The \(H^2\) estimate is combined with a uniform \(C^1\) bound to obtain \(C^0\) control; no false critical \(H^2\hookrightarrow C^0\) embedding is used.

**Which operation is absent from the prior source proofs?** The exact assembly of EG's particular normalization, the two-metric hypotheses and the displayed \(D^{1/16}\) conclusion is absent from the strongest statements read. The arithmetic budget (H) with the term \(\eta r^2+\eta^2\) is not TW's printed error budget. But its source is the direct application of the already general Clarke lemma; inserting it in the unchanged volume-subtraction/packing argument is a local estimate substitution. The stopping-time and radius choices, fixed-neighborhood entry and elliptic inversion introduce no new invariant, obstruction-removal mechanism or analytic input beyond those contracts. This is the affirmative reason for TECHNICAL ONLY, rather than just a list of familiar ingredients.

## Exponent, correctness and significance kept separate

With only an all-subset absolute volume budget \(C\eta\), the same argument gives \(H_r=C(r^6+ar^3+\eta)\). Balance at \(r=\eta^{1/6}\): the subdivision error is \(\eta^{1/12}=D^{1/24}\). Clarke's localized square-root budget improves this to \(D^{1/16}\). The improvement is mathematically real and worth stating, but there is no matching lower obstruction, endpoint theorem, optimality proof, or qualitative change of scope. It results from using a known stronger estimate in the same argument. It is insufficient here as a separate substantial mechanism.

I did **not** find a stronger currently applicable distance theorem that makes \(1/16\) obsolete under exactly I30's hypotheses. Bounded-scalar results need extra spacetime control; fixed-parameter Hölder estimates do not tend to the identity; near-Euclidean theorems require quantified inputs not automatically furnished at a defect-dependent scale. A cleverer use of those methods could improve the exponent, but that is not established by this review. Nor do I claim \(1/16\) is the best exponent obtainable by variations of the packing argument.

The correctness status remains R2 PASS. No failure of uniformity, normalization, gauge or original-distance control was discovered. I checked the new prior-art substitution and the exact exponent bookkeeping; these are not a second complete proof audit or a replacement for R2. The parent's reproduced 20,698 author and 4,759 independent checks remain historical verified records, not checks newly rerun here. Finite checks and hashes cannot establish a universal theorem or significance.

The unequal-product warning is preserved. Volume-normalized Ricci flow increases the factor imbalance and can collapse an unequal product in finite time. That disproves a universal attracting-flow proposal, not I30's finite-time smoothing plus elliptic comparison. Initial \(\sec\ge0\) is not presumed preserved. R2's smooth conformal concentration examples preclude casually replacing a critical norm by a small pointwise defect; this review does not claim they prove unbounded curvature or a sharp GH lower bound.

Under the project benchmark, I14/I15/I17 were demoted only after explicit proof-level reductions, while R011's rooted allowance and positive-global-maximum induction repaired a separator obstruction not paid by the old contraction/rank interface. I30 deserves the same strongest-case analysis. Here the missing volume principle is already exactly known, and the residual distance construction has the same working invariant—later-ball volume inside a controlled initial set—as its antecedent. There is no analogous unpaid step after substituting EG and Clarke. This comparison supports the recommendation; it does not mechanically inherit earlier verdicts.

## Evidence and reproducibility

The full original author task, fresh review task (including the supplied prior reviews and precise significance objection), original I27 task/report, candidate, R2, parent notes/check records, instructions, ledger and upstream identity are frozen in [input-manifest.json](../sources/i30_einstein_metric_stability_novelty_r3/input-manifest.json). [dependency-manifest.json](../sources/i30_einstein_metric_stability_novelty_r3/dependency-manifest.json) hashes reused evidence without duplicating the large cache. [search-record.json](../sources/i30_einstein_metric_stability_novelty_r3/search-record.json) distinguishes retained raw search responses from the exactly retained final request and records retrieval limitations. Search results are discovery aids, not theorem authorities. Exact primary HTTP URLs, UTC retrieval dates, versions and bytes are retained separately.

The opened passage record identifies actual inspected source spans and hashes. Long tool outputs were occasionally truncated; decisive omitted formulas were reopened in smaller spans, and Clarke's critical statement was also visually verified. The record is not a claim to have semantically read every page of every retained PDF or every source file in the selected manifest. The complete corpus screen is similarly not a whole-corpus proof review. No exact duplicate found in this bounded review is a claim about worldwide priority.

Run from the project root:

```bash
python3 frontier/experiments/i30_einstein_metric_stability_novelty_r3/check.py
python3 frontier/experiments/i30_einstein_metric_stability_novelty_r3/verify.py
```

The first command checks the dimension-four rescaling/trace constants and the two rational exponent balances. The second verifies frozen controls, selected Git blobs against the complete pinned tree, all reused dependency hashes, new primary bytes, exact passage hashes and the artifact seal. Shared ledger drift is separately reported; it is not a mutation of frozen evidence or a theorem failure. Reproduction writes only the allowed review experiment directory. The seal covers this report, scripts, primary evidence, contracts and diagnostics; the self-referential seal and regenerated verification output are excluded by explicit policy. Initial reproduction passes eight exact reduction checks, 13 frozen inputs, 163 read-only dependencies, 43 selected pinned files, 22 fresh primary responses, 59 opened passage ranges and 70 sealed artifacts. There are no verification errors or live shared-input drifts at packaging time; the parent's earlier shared-ledger drift remains historical evidence.

**Final recommendation: TECHNICAL ONLY; exact original-metric theorem and full proof PASS preserved; neither DUPLICATE nor GAP; worldwide priority unverified.** The next mathematically viable target is a sharp or obstruction-backed original-metric modulus in the same class: produce a smooth nonnegatively curved small-defect family with a proved GH lower bound and match it by an upper mechanism, or establish a genuinely stronger concentration-to-distance principle with a demonstrated limitation of the current packing method. Merely adjusting stopping times, rebalancing (H), or repackaging the now-proved theorem would not by itself address the significance objection. No such new discovery task was undertaken here.
