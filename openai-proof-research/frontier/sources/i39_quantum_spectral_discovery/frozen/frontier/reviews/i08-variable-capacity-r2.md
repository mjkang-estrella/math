# Independent proof audit: i08 variable-channel capacity, round 2

**Verdict: PASS (conditional on the pinned corpus, as instructed).** The stated equivalence follows from the stated source premise and the new argument. I found no failed estimate, actual counterexample, hidden uniform channel restriction, or substantive gap requiring repair. Several compressed steps deserve the explicit justifications supplied below; these do not change the theorem or constants. This is a proof verdict with preliminary significance observations, **not finding acceptance or a final novelty verdict**. The accepted count remains two; this review assigns no result number.

Audit date: 2026-10-08, America/Los_Angeles (artifact timestamp is 2026-10-09 UTC). Work was confined to this repository. No agents were started, and no staging, commits, shared indexes, candidate edits, or parent experiment edits were made.

**1. Audited inputs and source identity.** The complete candidate was read and snapshotted at `frontier/sources/i08_variable_capacity_r2/candidate-input.md`. Its SHA-256 is `4220b53ff1d80ba82795c56cc075944f9ed011ae13cb7be976e1dd4e8c037f6b`; it still had this hash when the audit was completed. `AGENTS.md`, `sources/upstream.json`, the relevant catalogue entries, and the complete `sources/preprints-tree.json` were consulted. The latter explicitly has `truncated: false`; `sources/tree.json` was not used. The immutable revision is `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` of `https://github.com/openai/math`.

The actual source statements read were:

- [A Capacity Criterion for Four-State Potts Reconstruction on Trees, build/main.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-Capacity-Criterion-for-Four-State-Potts-Reconstruction-on-Trees-October-5-2026/build/main.tex): the entire manuscript, especially `thm:main`, `prop:companion`, `eq:moment-saving`, `eq:symmetric-moments`, `eq:exact-m-product`, `lem:local-moments`, and the sufficiency proof. SHA-256 `0e73632ec22fb64a26e0d0cda579d7b670bf3a75379b1b2747e0a919a6ad2ffd`, Git blob `90c4681d47201bea1ecc09340035003f20a50378`. These bytes were copied from the parent-screen source cache and verified against both its retrieval manifest and the complete pinned tree.
- [The Reconstruction Threshold for the Ferromagnetic Four-State Potts Model, build/sections/03-cone.tex](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Reconstruction-Threshold-for-the-Ferromagnetic-Four-State-Potts-Model-October-5-2026/build/sections/03-cone.tex): `prop:cone-closure` (the cited Proposition 3.2), its `eq:moment-saving`, and the preceding definition and initialization of the class. SHA-256 `c5a7a96a2c337de4ca67b9c6d40ac8b6051367220881ff7f3e786a51bce87250`, Git blob `defa4181aee88aebcb85a0c95f55d57a7925ba9d`.
- The threshold companion's `01-introduction.tex`, `02-experiments.tex`, and `04-tree-decay.tex`, including its main theorem, Bayes product, channel scaling, and tree scope. These were retrieved directly from pinned raw URLs and each Git blob checked against `preprints-tree.json`. All URLs, lengths, SHA-256 hashes, and Git blob identities are in the input manifest.

The source contract is exactly adequate: the class contains revealing and uninformative laws and admits **every** channel parameter in `[0,1]`, finite independent products conditional on the input, and the specified saving with `c=1/1000`. The capacity paper explicitly discusses independently chosen terminal noise and explicitly avoids any limiting-law membership assertion. The candidate uses class membership only for finite experiments and partial products. I accepted these source theorems as true and did not check their polynomial certificates or re-audit upstream truth.

**2. Scope and quantifiers.** The audited theorem concerns an infinite deterministic rooted tree with a fixed finite bound `B` on the number of children, a uniform four-state root, independent edge transmissions conditional on the parent spins, observed tree/parameters, and `0<lambda_e<=1`. For `r_e=lambda_e^2` and positive finite products `R_v`, reconstruction is equivalent to existence of a conserved nonnegative flow with finite positive mass and bounded potential

\[
 \sup_\xi\sum_{e=(v,w)\in\xi}(1-r_e^2)
                  (\theta(e)/R_w)^2.
\]

Homogeneity converts any finite positive potential bound to the normalization `V<=1`; a zero-potential positive flow can be scaled arbitrarily. No maximizer of the capacity supremum is needed. Infinite capacity is allowed. The proof does not divide by `1-r_e^2`, so perfect edges cause no singularity. Strict positivity of each `lambda_e` is used when dividing by `R_v` and in the profile/kernel identities; zero broadcast parameters are outside the theorem. Zero terminal-noise parameters are inside the source class and are used on zero-flow terminals.

**3. Uniform local lemma: PASS, including singular posterior pairs.** Under independent marginal posterior vectors, Bayes multiplication gives `Z=4 sum p_i q_i=1+x.y` and `N=L(4p_iq_i)`. The entries `4p_iq_i` are nonnegative, so `|N_i|<=Z`, `0<=Z<=4`, and `N=0` when `Z=0`. These are feasible-simplex statements, not bounds for unrestricted six-dimensional `x,y`.

The symmetry used is invariance under all spin permutations. Its coordinate action consists of coordinate permutations and even sign changes. Consequently `E x_i=0`, `E x_ix_j=(a/3)1_{i=j}`, and among degree-three coordinate monomials only `x_1x_2x_3` can survive. Independence here is under the two marginal posterior laws before the Bayes tilt, exactly as required. The audit's independent sparse-polynomial expansion gives

\[
 E[|N|^2(1-s)]=a+b-4(\tau_x b+a\tau_y)-6\tau_x\tau_y.
\]

The remainder `E[|N|^2s^2/Z]` is nonnegative. Since `h_x<=a` and `h_y<=b`, `2 h_x h_y<=h_x b+a h_y`, proving the lower bound with seven, regardless of the signs of the signed third moments.

For the new unsmoothed third-moment estimate, on `Z>0`,

\[
 \left|\frac{N_1N_2N_3s^2(3+2s)}{Z^2}\right|
 \le Zs^2|3+2s|\le36s^2.
\]

Here `s` lies in `[-1,3]`, so `|3+2s|<=9`, and `E s^2=ab/3`. The error expectation is at most `12ab`; it does not contain an inverse minimum normalizer or inverse `1-lambda`. In fact its magnitude tends to zero as `Z` tends to zero, using the stronger first bound `9 Z s^2`. The weighted third-moment integrand itself is bounded by `Z`, and the weighted quadratic integrand by `3Z`. Thus assigning these contributions zero at `Z=0` is valid and continuous **for the weighted integrands**. No continuous extension of the posterior vector `N/Z` itself is asserted or needed.

For the polynomial `N_1N_2N_3(1-2s)`, the raw coefficient absolute-sum bound is `4^3(1+2*3)=448`. The only pure terms are the two signed third-moment monomials with coefficient one. Every mixed monomial linear in either vector has zero expectation. Every other mixed monomial has degree at least two in each vector; retaining any two factors bounds its absolute value in each vector by its squared norm. Independence then bounds its absolute expectation by `ab`. This proves `h_product<=h_x+h_y+460ab`. Independently combining like terms yielded 189 monomials and coefficient absolute sum 396, with 364 on the mixed terms that are not already removed by the degree-one rule. The candidate's larger bound is sound; no optimization is necessary.

**4. Necessity: PASS.** Define `m_v^(k)` using descendants at distance `k` from `v`. Each sequence decreases by data processing, with values in `[0,3]`, so its numerical limit exists. This does not require nested observation sigma-fields or a limiting posterior in the class. The finite-depth moment-saving inequality and Jensen imply, for any pair of branches, a saving at least `c b_i b_j(b_i+b_j)`. Combine that pair first, then use subadditivity for the other finitely many branches. Taking limits and maximizing over finitely many pairs gives the stated bound `m_v<=S-cD` with variable edge parameters.

For the cubic bound, order the child values as `b_1>=b_2>=...`. Every mixed ordered triple in `S^3` is at most `b_1^2 b_2<=D`, and there are at most `B^3` ordered triples. The pure terms contribute `sum b_w^3`. With `K=c/B^3`,

\[
 y_v\le S-cD+KS^3\le S+K\sum b_w^3
 =\sum r_e y_w-K\sum r_e(1-r_e^2)m_w^3.
\]

Writing `L=1+9K`, the inequality `y_w<=L m_w` and the tangent inequality `(1+2t)^(-1/2)>=1-t` give the candidate's nonlinear recursion with `a=2K/L^3`. Its direction is correct: the nonlinear right side is an upper bound on the right side after subtracting the cubic saving.

For completeness, choose `d_e` explicitly by multiplying all upper coefficients at a vertex by `y_v/S_v`, where `S_v` is their weighted sum with `y_w`, and set all coefficients zero if `S_v=0`. Then

\[
 g_w^2[1+a(1-r_e^2)y_w^2]\le g_v^2,
 \qquad \theta(e)/R_w=g_w y_w.
\]

The potential of `sqrt(a) theta` along every finite ray segment is at most `g_root^2=1`. Taking increasing limits of nonnegative partial sums works on each ray separately. This constructs a finite positive root mass whenever reconstruction implies `m_root>0`. At a leaf the label must be zero; with one child or a perfect edge the same formulas work. No lower bound on channel parameters enters the construction.

**5. Sufficiency setup and local recursions: PASS.** A positive conserved flow on a locally finite tree supplies an infinite positive-flow continuation from every positive-flow vertex. For each positive-flow edge, `r_e X_w<=X_v`, so

\[
 X_w^2-X_v^2\le(1-r_e^2)X_w^2.
\]

Summing on the finite path to any positive-flow vertex and extending that path to a ray gives `X_v^2<=M^2+epsilon^2=epsilon^2 Q`. This is a uniform bound over all vertices, not a depth-dependent assertion. It applies even when many weights vanish and cannot be obtained merely by bounding each weighted edge term separately.

A revealing posterior has `m=3` and signed third moment one. Terminal channel `sqrt(X_v/3)` therefore gives exactly `m=X_v` and `h=(X_v/3)^(3/2)`. These are valid parameters under `epsilon sqrt(Q)<=1`. Channel closure and independent-product closure inductively place all finite subtree laws and partial products in the preserved class. Zero-flow branches produce independent uniform terminal observations and hence uninformative subtree experiments.

Here is the detailed constant calculation in the sequential branch combination. Put `P_2=sum_{i<j} b_i b_j` and `S=sum b_i`. Subadditivity bounds a partial quadratic moment by its partial sum. Repeated use of the local lemma bounds its third moment by the sum of its `h_i'` plus 460 times its partial pair sum. Summing quadratic deficits then gives

\[
 D_v\le7\sum_i h_i'(S-b_i)+7\cdot460\sum_{i<j<k}b_i b_j b_k
 \le7\sum_i h_i'(S-b_i)+7\cdot460 X_v P_2.
\]

Crucially, `S-b_i=sum_{j!=i}b_j<=X_v sum_{j!=i}t_j=X_v(1-t_i)` holds even when `b_i<t_i X_v`. It is not inferred by subtracting upper bounds. Also `P_2<=X_v^2 beta_v/2` and `h_i'=lambda_i^3 X_i U_i=t_i X_v lambda_i U_i`. Hence the coefficient in the third-moment error is 230, the propagated loss coefficient is seven, and the remaining cubic loss coefficient is 1610. All are at most `C_0=2000`, proving (H) and (D) as written. Nonnegativity of `D_v` uses the source class; the new lower bound alone would not give it. Unary vertices have `beta_v=0`, exact channel scaling, and exactly zero deficit. No fictitious loss accumulates on a unary chain.

**6. Energy and kernel estimates: PASS.** The finite-dimensional flow probabilities are `Pr(V_i=v)=Theta(v)/M`, and the transition probabilities are `t_vw`. They are consistent because of conservation; zero-flow vertices have zero probability. One can work entirely with these finite ray prefixes, avoiding any separate boundary-measure existence issue. If using the infinite ray measure, consistency on this finitely branching tree supplies it.

Let `F_i` be the sigma-field generated by the ray prefix through depth `i`. Then `E[alpha_i|F_i]=beta_(V_i)`. The conditional energy identity is exactly

\[
 X_v^2-E[r_e^2 X_{i+1}^2\mid F_i]
 =X_v^2(1-\sum_wt_w^3)\ge X_v^2\beta_v.
\]

Splitting the left side into a difference of consecutive `X^2` values and the weighted edge energy, summing, and discarding `-E X_n^2` proves (E), since the expected partial weighted energy is at most `epsilon^2`. This uses the admissible pathwise capacity bound, not any summability of unweighted `X_i^2`.

For fixed `i`, the row telescope uses `alpha_j=1-t_(j+1)` and
`alpha_j K_ij<=2(K_ij-K_i,j+1)`. For fixed `j`, the column telescope uses
`alpha_i K_ij<=2(K_i+1,j-K_ij)`. The latter follows by putting `u=sqrt(t_(i+1))` and using `(1-u^2)u<=2(1-u)`. The column endpoint `j=n` gives the separate terminal bound. These formulas cover `t=1`; a zero transition is never sampled. The sum limits in (K) are correct, including exclusion of `alpha_n`.

The profile relation gives

\[
 \prod_{k=i+1}^j\lambda_k=\sqrt{X_i/X_j}\,K_{ij},
 \quad X_iX_j\prod\lambda_k=X_i^{3/2}X_j^{1/2}K_{ij}.
\]

Weighted Young with exponents `3/4,1/4` bounds this by `(3X_i^2/4+X_j^2/4)K_ij`. Multiplying by `alpha_i alpha_j` and using the row bound for the first part and the column bound for the second proves (B), with coefficient `3/2+1/2=2`. Neither geometric channel decay nor a positive lower bound on splitting is used.

**7. Conditioning and terminal indices: PASS.** All `U_v`, `X_v`, and subtree information values are deterministic numbers once the tree, parameters, flow, and observation depth `n` are fixed. They are already averaged over the spin observations. Only the selected ray is random in this part of the proof.

More explicitly, iterating (H) from the child of depth `i` gives

\[
 E[\alpha_i\lambda_{i+1}U_{V_{i+1}}]
 \le E\left[\alpha_i\left(
  \sum_{i<j<n} C_0 X_j\beta_{V_j}
                  \prod_{k=i+1}^j\lambda_k
  +U_{V_n}\prod_{k=i+1}^n\lambda_k\right)\right].
\]

The same identity holds with the factor `X_i` present. For each summand, the factor multiplying `beta_(V_j)` is `F_j`-measurable: in particular `alpha_i` depends on a branch choice already made because `i<j`. Thus the tower property replaces `beta_(V_j)` by `alpha_j` **inside expectation only**. The diagonal contribution from (D) is handled by `E X_i^2 beta_(V_i)=E X_i^2 alpha_i`. No replacement is made under future-dependent weights; no independence between the `alpha` variables is assumed. This yields exactly the displayed sum in section 6 of the candidate, with `i<j<n` and a separate depth-`n` term.

The terminal moment is `U_n=sqrt(X_n)/(3 sqrt(3))`, so

\[
 X_i\left(\prod_{k=i+1}^n\lambda_k\right)U_n
 =X_i^{3/2}K_{in}/(3\sqrt3).
\]

The power of `X_n` cancels completely. The profile bound and terminal column telescope then give `2 epsilon^(3/2) Q^(3/4)/(3 sqrt(3))`. Together with (B) and (E), this verifies all powers and constants in (F).

An explicit depth-independent choice is `epsilon=10^(-4)/sqrt(Q)`: the first term of (F) is `0.08002`, and the second is less than `0.001334`, so their sum is less than `1/2`. This also verifies the terminal-parameter restriction. The dependence on the chosen finite flow mass through `Q=1+A^2` is harmless. There is no dependence on the minimum edge parameter, on `sup lambda_e<1`, or on the observation depth.

**8. Infinite conclusion and boundary cases: PASS.** Finite-tree telescoping gives `mhat_root=sum_|v|=n R_v X_v-sum_|v|<n R_v D_v`. Every level has total flow `M`; early dead ends have no flow and no noisy information. For positive-flow vertices, `R_v X_v=Theta(v)` converts the second sum to `M E sum D_(V_i)/X_i`. Zero-flow vertices contribute zero and need not be assigned a quotient. Therefore `mhat_root>=M/2` at every finite depth. Data processing from the original level observation to its independently degraded version and the bound `E TV>=m/8` imply `a_n>=M/16`. The original advantages decrease by data processing, so their limit exists and is positive. The degraded experiments need not converge or be mutually ordered as `n` varies.

A perfectly transmitting ray has zero weighted potential at every finite flow mass and advantage `3/4`; the proof still applies although capacity is infinite. For the proposed nonperfect ray, indexed from `j=1`,

\[
 P_n=\prod_{j=1}^n\left(1-\frac1{(j+1)^2}\right)
     =\frac{n+2}{2(n+1)},\quad R_n=P_n^2.
\]

The composed channel is `P_(P_n)` and its posterior TV is `3P_n/4`, tending to `3/8`. The unit-flow weighted sum through depth `n` is

\[
 \sum_{j=1}^n(1-\lambda_j^4)/P_j^4=P_n^{-4}-1\longrightarrow15.
\]

Every nonzero flow on a ray is constant. Its unweighted substituted potential diverges, since `P_n^{-4}` tends to 16. This is an actual counterexample to the naive unweighted variable-edge criterion, and it is consistent with the weighted theorem. Arbitrarily small positive edges, perfect stretches, highly uneven splits, and slack branch profiles do not invalidate the estimates above. I found no counterexample to the candidate itself.

**9. Independent finite checks and their limits.** The reproducible script is [check.py](../experiments/i08_variable_capacity_r2/check.py); run from the repository root with `python frontier/experiments/i08_variable_capacity_r2/check.py`. It uses only the Python standard library, sparse integer polynomials, and exact `Fraction` arithmetic. It does not import or run the parent's checks. [results.json](../experiments/i08_variable_capacity_r2/results.json) records a successful run of:

- An independent symbolic expansion and symmetry reduction of the quadratic cancellation; exact pure-term and coefficient-norm checks of the new third-moment polynomial.
- All 144 ordered pairs of 12 explicitly constructed symmetric posterior laws, including simplex-boundary laws, two negative-third-moment laws, and an observed mixture. The checks include exact product normalization, the two moment identities, Lemma (L), and 370 `Z=0` marginal atom pairs. The upstream saving theorem is deliberately not being tested.
- Four depth-five asymmetric rational flow trees, with 205 vertices and 101 terminal rays in total, using unary, binary, and ternary vertices, channel parameters `1`, `999/1000`, `1/1000`, and `2/3`. Each terminal ray can be continued by perfect unary edges. These verify the profile bound, conditional energy identity, row/column/terminal kernel bounds, weighted product identity, Young sum bound, and exact equality between recursively computed H/D upper expressions and their fully unfolded expectation. This last equality independently tests the conditioning and index manipulations. The profiles need not be normalized to small noisy-experiment profiles for these purely algebraic checks.
- Five actual exact finite channel-product examples for (H)/(D), including unary zero loss, perfect edges, very weak edges, and a three-branch example with an internal child product and strictly slack child profiles. The latter has 256 posterior atoms and explicitly tests `S-b_i<=X(1-t_i)`.
- The first 100 exact ray product/potential identities. Their limiting values are established algebraically above, not inferred from those 100 terms.

These are independent finite sanity checks. They do **not** establish the infinite theorem; that verdict rests on the preceding universal inequalities, class-preserving finite-depth construction, and uniform-in-depth argument.

**10. Preliminary significance and final-review boundary.** The actual capacity source fixes one `0<lambda<1`, uses channel smoothing in its third-moment bound, and sums the geometric kernel with a factor depending on `1/(1-lambda)`. The threshold companion's main theorem concerns regular and Poisson families with one common parameter. Neither of these read source statements already states the candidate's full variable-edge equivalence with vanishing edge weights and perfect channels.

The candidate is consequently more than a literal substitution in the source theorem: the ray example disproves that substitution, and the splitting-weighted energy/kernel calculation repairs a genuine obstruction to the fixed-channel sufficiency proof. The uniform local estimate is a short strengthening of the source's own algebra; the necessity change of variables and nonlinear flow construction are direct adaptations of source machinery. The strongest apparent new proof component is therefore the flow-splitting control of cumulative sufficiency loss when geometric channel decay is unavailable.

This is a limited comparison against the actual two relevant pinned companion manuscripts, identified using the complete path listing. It does not certify absence of an equivalent result elsewhere in the corpus or literature. No new external-literature search was performed in this proof-only round. The later novelty/significance audit should assess equivalence to standard variable-resistance nonlinear-capacity formulations, including the Pemantle–Peres framework cited by the source, and whether the extension reaches the user's substantial-finding threshold. Proof correctness alone does not settle that question.

**11. Artifacts and integration guidance.** [input-manifest.json](../sources/i08_variable_capacity_r2/input-manifest.json) records all audited input hashes and pinned source provenance. [artifact-manifest.json](../sources/i08_variable_capacity_r2/artifact-manifest.json) records the review, snapshot, source copies, independent check script, and results; it excludes its own self-hash. All new files are under the assigned review path and the two assigned `_r2` directories.

No substantive repair is requested. If expanding the candidate for publication, the useful small additions are the explicit `F_j` conditioning argument in paragraph 7, the numerical-limit construction and coefficient choice in paragraph 4, and the weighted-integrand distinction at `Z=0` in paragraph 3. They make already-valid steps easier to verify. **The proof passes; the separate final novelty/significance review remains pending, and the parent alone decides acceptance and counting.**
