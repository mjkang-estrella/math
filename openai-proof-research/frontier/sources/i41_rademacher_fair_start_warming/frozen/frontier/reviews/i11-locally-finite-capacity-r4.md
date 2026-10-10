# Independent proof audit: locally finite weighted-capacity strengthening

**Verdict: PASS, conditional on the pinned corpus.** The entire proposed locally finite theorem, both universal information bounds, the zero-edge corollary, and the nonlocally-finite counterexample are valid. No substantive repair is required. The binary renormalization really removes the degree dependence; the converse's constants do not conceal a common child bound. This is a strengthening of the **same prospective capacity finding**, not a separately countable result. No result number or acceptance action is assigned here.

I read the full strengthening, full original proof, prior proof review, actual source statements and companion scope. The favorable on-disk novelty review was consulted only as a **live finalization draft**, not as a completed record or proof premise. Its status is not certified by this review. The parent retains responsibility for integration and the separate significance decision. No agents, staging, commits, shared-index changes, candidate changes, or work outside the assigned paths were performed.

**Inputs and source contract.** The pin is `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. [input-manifest.json](../sources/i11_capacity_r4/input-manifest.json) records fresh SHA-256 hashes, byte lengths, snapshots, source URLs and verified Git blob identities. The strengthening's audited hash is `f68c3accfc5478058b9a74d8fd29afed56b2f61909a9385a5bd8b26f6fc7c660`; the original full proof's is `4220b53ff1d80ba82795c56cc075944f9ed011ae13cb7be976e1dd4e8c037f6b`. The complete `sources/preprints-tree.json` was parsed: 13,223 entries, 749 first-level manuscript directories, `truncated: false`. [inventory-screen.json](../sources/i11_capacity_r4/inventory-screen.json) retains the directory inventory and relevant-title screen; catalogue excerpts are retained separately. The truncated root-tree cache was not used.

The actual dependency is [A Capacity Criterion for Four-State Potts Reconstruction on Trees, build/main.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-Capacity-Criterion-for-Four-State-Potts-Reconstruction-on-Trees-October-5-2026/build/main.tex), `prop:companion` / `eq:moment-saving`. It states closure under **all** channel parameters in `[0,1]` and conditionally independent products, includes revealing and uninformative experiments, and gives the saving with `c=1/1000`. Its cited threshold companion, [03-cone.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Reconstruction-Threshold-for-the-Ferromagnetic-Four-State-Potts-Model-October-5-2026/build/sections/03-cone.tex), `prop:cone-closure` / `eq:moment-saving`, has precisely that scope. The threshold introduction, posterior-experiment section and tree-decay section were also read. Its tree theorem addresses homogeneous regular/Poisson models; it is not a stronger arbitrary-edge converse. The capacity source's `thm:main` assumes bounded children and one fixed `0<lambda<1`; its `lem:local-moments` uses smoothing and its `eq:uniform-loss-bound` uses geometric decay. These source hypotheses were not silently widened. Source truths were accepted, without checking upstream polynomial certificates.

**Exact scope.** Fix a deterministic rooted locally finite tree, known to the observer, a uniform four-state root, and independent edge transmissions conditional on parent spins through `P_e=lambda_e I+(1-lambda_e)U`, with every `0<lambda_e<=1`. No common degree bound, minimum positive edge parameter, or separation from one is imposed. Put `r_e=lambda_e^2`, `R_root=1`, `R_w=product_[root,w] r_e`. Capacity is the supremum of the finite masses of nonnegative conserved flows whose worst infinite-ray potential

\[
 \sum_{e=(v,w)}(1-r_e^2)(\theta(e)/R_w)^2
\]

is at most one. Conservation includes leaves, so their incoming flow is zero. Set `m_infty=lim_n E|Lp_root^(n)|^2`. The proved conclusion is

\[
 \frac1{20000}\frac{C}{\sqrt{1+C^2}}
 \le m_\infty\le\min\{3,C/\sqrt\kappa\},
 \qquad K=1/3000,\quad\kappa=2K/(1+9K)^3.
\]

At `C=infinity` the left fraction means one. Finite trees, including a finite root component after pruning, have zero limiting information and no positive flow. Expected TV lies between `m/8` and `sqrt(m)/2`, so positive limiting information is equivalent to reconstruction. This is an expected quadratic-information statement, not a pathwise bound on individual posterior vectors.

**Binary inequality and finite product closure: PASS.** Write `a=m(mu)`, `b=m(nu)`, `d=m(mu star nu)` for laws in the accepted class. Jensen gives `E A^2>=m^2`, hence

\[
 d\le a+b-cab(a+b),\qquad 0\le d\le a+b.
\]

Use the first bound only in the linear term of `g(d)=d+Kd^3`, and the second in the cubic term. The resulting difference from `g(a)+g(b)` is at most `(3K-c)ab(a+b)=0`. The argument never asserts `a+b<=3`. Actual branch and partial-product moments lie in `[0,3]`, but their sum need not. After each binary combination the law stays in the class, so induction gives the same bound for every finite number of branches, however large. Empty and singleton products are covered by zero information and exact channel scaling. This induction uses conditional independence of branch experiments given the common input, not independence under their actual joint marginal law.

At any fixed depth, local finiteness makes the entire subtree truncation finite, by induction on levels. Thus finite closure is sufficient. There is no infinite product of posterior laws to justify, and no claim that a limiting posterior law lies in the preserved class.

**Numerical limits and the necessity flow: PASS.** For each vertex, use its descendants at relative distance `n`. The next level is a Markov degradation of the present one, including disappearing dead branches. Convexity of the quadratic posterior statistic makes `m_v^(n)` decrease to a number in `[0,3]`; nested observation sigma-fields are unnecessary. For each fixed vertex its child set is finite. Continuity of `g` and passage through this finite sum give

\[
 y_v=g(m_v)\le\sum_w g(r_e m_w)
 =\sum_w r_e y_w-K\sum_w r_e(1-r_e^2)m_w^3.
\]

Set `L=1+9K`. Since `y_w<=L m_w`, the subtracted term is at least `(K/L^3)r_e(1-r_e^2)y_w^3`. The tangent inequality `(1+2t)^(-1/2)>=1-t` gives the stated upper recursion with `kappa=2K/L^3`. Its direction is correct. All coefficients and sums are finite.

Let `S_v` be the last nonlinear right side. If `S_v>0`, multiply every coefficient by `y_v/S_v`; otherwise choose all coefficients zero. Then `0<=d_e<=r_e/sqrt(1+kappa(1-r_e^2)y_w^2)` and `y_v=sum d_e y_w`, including when `y_v=0`. With the note's `ell`, `theta`, and `h=ell/R`,

\[
 h_w^2\{1+\kappa(1-r_e^2)y_w^2\}\le h_v^2,
 \qquad \theta(e)/R_w=h_wy_w.
\]

Conservation holds everywhere and the root mass is `y_root<=g(3)`, hence finite. Along every finite ray prefix the potential of `sqrt(kappa) theta` is at most one. Increasing nonnegative partial sums prove this on every infinite ray; no exchange of a supremum with a limit is required. A leaf has label zero. Perfect edges simply have zero potential cost. Zero labels and zero scaling coefficients never require division by those quantities. Division by `R` is valid because each finite product of positive edge parameters is positive. This proves the stronger bound `C>=sqrt(kappa) g(m_infty)` and thus the asserted upper bound.

**Uniform local estimates and arbitrary finite branch counts: PASS.** I rechecked the original proof's unsmoothed lemma, rather than importing the smoothed source lemma outside its scope. Feasibility gives `0<=Z<=4`, `|N_i|<=Z`, and `N=0` at `Z=0`. The weighted quadratic and third-moment integrands extend by zero there. The third-moment remainder is bounded by `36s^2`, with expectation `12ab`; the polynomial coefficient bound is `4^3(1+6)=448`. Mixed monomials linear in either vector vanish; each remaining mixed expectation is bounded by `ab`. This gives 460 uniformly, including simplex-boundary observations and perfect channels. The exact quadratic cancellation and `h<=m` give seven. These estimates use symmetry, with subadditivity supplied separately by the accepted class.

For `d` branches at a positive-flow vertex, let `b_i<=t_i X`, `h_i'=lambda_i^3 h_i`, `S=sum b_i`, and `P_2=sum_(i<j)b_i b_j`. Iterating the two-input estimates gives

\[
 h_v\le\sum_i h_i'+460P_2,
 \qquad
 D_v\le7\sum_i h_i'(S-b_i)
       +3220\sum_{i<j<k}b_i b_j b_k.
\]

The second expression follows by summing each sequential deficit, so no factor counting the number of additions has been dropped. For every finite `d`,

\[
 S-b_i=\sum_{j\ne i}b_j\le X(1-t_i),\qquad
 P_2\le X^2\beta/2,\qquad
 \sum_{i<j<k}b_i b_j b_k\le XP_2.
\]

The first inequality is a sum over the other branches, not subtraction of upper bounds. Using `h_i'=t_i X lambda_i U_i`, the constants needed in (H) and (D) are at most 230, seven, and 1610. The common choice 2000 is therefore valid for any finite child count. A unary positive-flow vertex has `t=1`, `beta=0`, and exactly zero deficit.

**Profile, terminal noise, and finite probability spaces: PASS.** For any admissible finite mass `A>0`, scale the flow by `epsilon` and use `X_v=Theta(v)/R_v`. Every positive-flow vertex has a positive-flow child, giving an infinite positive-flow continuation. Along a prefix ending at such a vertex,

\[
 X_w^2-X_v^2\le(1-r_e^2)X_w^2.
\]

Extend that prefix to a ray and use nonnegativity of the remaining energy. This proves `X_v^2<=epsilon^2(1+A^2)` uniformly over all positive-flow vertices. It does not try to control `X_v` by a single edge cost when that edge is perfect.

The terminal channel `sqrt(X_v/3)` is valid when `epsilon sqrt(1+A^2)<=1`. A revealing spin has `m=3` and signed third moment one, giving terminal values `mhat_v=X_v`, `hhat_v=(X_v/3)^(3/2)`. Finite channel/product closure applies separately at every observation depth. At zero-flow terminals the zero channel outputs independent fresh uniform labels. Conservation implies every descendant flow below a zero-flow vertex is zero, so these branches really are uninformative jointly. No quotient `U=hhat/X` is used there.

For a fixed `n`, choose a level-`n` vertex with probability `Theta(v)/M` and take its ancestors. All levels are finite, their flow sums equal `M`, and dead ends carry zero. This gives all the ray-prefix expectations needed for the proof; an infinite boundary probability measure is optional. Every sampled prefix extends to an admissible infinite ray. Unbounded degrees at increasing depths therefore cause no integrability or normalization problem.

**Energy, kernels, conditioning, and terminal index: PASS.** Write `F_i` for the selected prefix through depth `i`, `alpha_i=1-t_(i+1)`, and `beta_v=1-sum t_vw^2`. Then `E[alpha_i|F_i]=beta_(V_i)`. The conditional energy identity is

\[
 X_i^2-E[r_{i+1}^2X_{i+1}^2\mid F_i]
 =X_i^2(1-\sum_wt_w^3)\ge X_i^2\beta_{V_i}.
\]

After splitting the edge term and telescoping, the expected weighted edge energy is at most `epsilon^2`, and the terminal `-E X_n^2` can be discarded. This gives (E). It never sums unweighted `X_i^2` over an infinite ray.

For `K_ij=product_(k=i+1)^j sqrt(t_k)`, the row bound follows from `alpha_j K_ij<=2(K_ij-K_i,j+1)`. The column and terminal bounds follow from `alpha_i K_ij<=2(K_i+1,j-K_ij)`. The first telescope ends at `j=n-1`, and the separate terminal column uses `j=n`; there is no `alpha_n`. All bounds are at most two, even with `t=1`, arbitrarily small positive splits, and arbitrary finite numbers of siblings. Zero transitions are never sampled. The profile identity gives

\[
 X_iX_j\prod_{k=i+1}^j\lambda_k
 =X_i^{3/2}X_j^{1/2}K_{ij}
 \le(3X_i^2/4+X_j^2/4)K_{ij}.
\]

The row and column bounds give the coefficient two in (B).

When unfolding (H) inside (D), a term at internal descendant `j>i` has multiplier `alpha_i X_i X_j product_(k=i+1)^j lambda_k`, which is `F_j`-measurable. The tower property therefore replaces `beta_(V_j)` by `alpha_j` **inside expectation**. All subtree moments here are deterministic numbers after averaging over spins. No independence of successive splits, and no replacement under a future-dependent multiplier, is asserted. The diagonal term is `E X_i^2 beta_(V_i)=E X_i^2 alpha_i`. These facts verify the previous review's conditioning clarification in the locally finite scope.

At the terminal, `U_n=sqrt(X_n)/(3sqrt(3))`, so the full `X_n` dependence cancels:

\[
 X_i\left(\prod_{k=i+1}^n\lambda_k\right)U_n
 =X_i^{3/2}K_{in}/(3\sqrt3).
\]

The profile bound and terminal column estimate give exactly the last term of (F). Thus every constant in the converse remains independent of degree, depth and edge parameters.

**Loss constant, infinite conclusion, and capacity supremum: PASS.** Take `Q=1+A^2` and `epsilon=10^-4/sqrt(Q)`. Then (F) is bounded by

\[
 0.08002+\frac{4000}{3\sqrt3}10^{-6}
 <0.08002+1/750=12203/150000<1/2.
\]

The noise restriction is also satisfied. The exact finite-tree deficit telescope gives

\[
 \widehat m_\rho=M-M E\sum_{i<n}D_{V_i}/X_i\ge M/2.
\]

Only positive-flow vertices occur in the quotient; all omitted terms are zero. Data processing gives `m_root^(n)>=A/(20000 sqrt(1+A^2))` for every `n`. The original sequence has a decreasing limit, so the same bound holds for `m_infty`. The degraded experiments may vary with `n` and need not converge. At `0<C<infinity`, choose admissible masses tending to the supremum and use continuity of `A/sqrt(1+A^2)`; attainment is unnecessary. At `C=infinity`, unbounded finite admissible masses suffice. At `C=0` the lower bound is trivial and necessity gives `m_infty=0`. No compactness or uniform finite-degree truncation theorem is being assumed.

**Zero-edge pruning: PASS, with joint Markov justification.** Individual independence of each removed observation from the root would not be enough in general. The broadcast factorization proves the stronger statement needed here. Realize each edge channel using independent copy/refresh randomness; a zero edge refreshes to a new uniform label with probability one, independent of every primitive variable above that edge. Cut at the first zero edge on each path from the root. The resulting removed subtrees are disjoint. Each whole subtree spin vector is a function only of its own fresh uniform top spin and independent internal edge randomness. These primitive-variable sets are mutually independent and independent of the root and all primitives in its positive-edge component.

Equivalently, for any finite observed level, if `Y_0` denotes observations in the root component and `Y_b` those below its first-zero boundary edges, the Markov factorization is

\[
 \Pr(\sigma_\rho=i,Y_0=y_0,(Y_b=y_b)_b)
 =\Pr(\sigma_\rho=i,Y_0=y_0)\prod_b\Pr(Y_b=y_b).
\]

Only finitely many such subtrees meet a fixed level. Further zero edges inside them do not affect this conclusion; one can also factor all positive-edge components by their independent uniform roots. Thus the **joint** collection removed from the observation is independent of the pair `(root,Y_0)`. It cannot encode synergistic root information. The root posterior at every level is unchanged. Component depths are the original depths on the root component. If this component is finite, sufficiently distant observations in it are empty and all conserved flows vanish. The positive-edge formula is used only there; no `0/0` is assigned to a deleted edge.

**Failure without local finiteness: PASS.** In the countable star of chains of lengths `k=1,2,...`, all perfect, every edge on each chain has zero flow by backward induction from its leaf. Countably additive conservation at the root then forces root mass zero. There are no infinite rays, and under the usual nonnegative-potential convention the zero flow is the sole candidate, so capacity is zero. At every depth `n>=1`, the length-`n` chain alone supplies an observed vertex equal to the root (as do all longer chains). Its posterior is a point mass, giving `m_n=3` and expected TV `3/4`. Countably many observations are well-defined here and one coordinate already reveals the root. No finitely additive mass “at chain length infinity” is permitted. This directly falsifies the equivalence without the local-finiteness hypothesis under the stated flow definition.

**Contribution boundary: one additional reduction to record.** The extension does not weaken the need for the original uniform four-state sufficiency bridge. However, once the bounded-child theorem with **arbitrary edge parameters including perfect edges** is established, its qualitative locally finite extension also follows by a routine exact encoding: replace each finite child set by a finite binary routing tree of perfect-copy edges, retaining each original noisy edge at an exit. The resulting tree has at most two children per vertex. Every original flow extends uniquely by summing downstream exit flows on gadget edges; every gadget flow restricts to an original flow. Perfect-copy edges cost zero and do not change `R`, so capacities agree exactly. Each gadget is finite, so an infinite ray cannot remain forever inside one gadget.

The original spin experiment is preserved at the embedded original vertices. For every finite original truncation, the finitely many corresponding gadgets have bounded depth in the encoded tree. Conversely every original edge takes at least one encoded step. Consequently the embedded original levels and encoded levels are cofinal separating observations. Markov screening in both directions shows their limiting root quadratic information agrees; early dead ends cause no issue once depth exceeds the relevant finite gadgets. This argument establishes equivalence, not merely one information inequality.

This reduction makes removal of the child bound a natural corollary of the **new bounded theorem**, rather than an independent substantial discovery. It does not reduce the original new theorem to the pinned fixed-channel predecessor: the gadgets require parameter one, which that predecessor excludes, and leave the arbitrary original channel parameters untouched. Likewise, allowing unbounded finite gadget sizes in a fixed `c<1` simulation removes the simple uniform first-generation error floor, but does not by itself construct an exact channel simulation or control errors through infinitely many levels. Thus the draft's bounded-degree gadget obstruction must not be quoted verbatim as an obstruction for all locally finite gadgets. No completed standard reduction to the older four-state theorem follows from it. The sharper binary `K=c/3` estimate and direct degree-free proof are sound improvements within the same finding. This is a precise contribution limit, not a new literature-priority verdict.

**Validation and disposition.** The verdict rests on the universal proofs above; no finite numerical sample or tautological implementation test was substituted for them. [verify.py](../experiments/i11_capacity_r4/verify.py) checks artifact/input identities, pinned source blob identities and exact rational constant bookkeeping only. Source copies were freshly verified against the complete pinned inventory, not newly downloaded. The candidate, original proof and previous PASS were checked for changes at completion. The live novelty draft's observed status is recorded separately. [artifact-manifest.json](../sources/i11_capacity_r4/artifact-manifest.json) hashes the delivered report and supporting artifacts, excluding itself. There is no requested proof repair. Parent integration should retain the same prospective finding and state the locally finite hypotheses and joint zero-edge independence explicitly.
