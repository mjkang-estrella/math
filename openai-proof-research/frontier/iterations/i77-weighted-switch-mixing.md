# I77 — Fixed-strength weighted switch mixing: paid slice comparison, two local obstructions, and a complete matching flow

**Disposition: GAP for W; no substantial finding nominated.** This round develops two distinct constructions. Construction A proves the full weighted pair-fiber comparison to the prescribed switch chain, derives the actual weighted three-row and disjoint-pair laws, and identifies two sharp source inequalities that fail for arbitrarily small positive activities. One part of the disjoint-pair argument does survive exactly. Construction B gives a complete weight-cancelling flow, including reconstruction and congestion, for all degree vectors with entries in `{0,1}`. Its extension to arbitrary degrees still needs a uniform repair/encoding estimate. The matching theorem is a technical consequence of classical alternating-cycle encodings, not a proposed ninth finding. **W is neither proved nor refuted.**

The eight accepted findings and the parent's acceptance gates are unchanged. All corpus statements **and lower proof operations** at `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are accepted premises. This report audits applicability and new deductions. Its local counterexamples concern *new weighted analogues*, not the stipulated uniform results. No child agent, stage, commit, shared edit, publication, MathDB assessment, or worldwide-priority claim is involved.

## 1. Frozen problem, evidence, and source comparison

The complete supplied I77 brief, original I72 assignment, and returned I72 report are frozen verbatim from this T3 task's paginated user message in [full-brief.txt](../sources/i77_weighted_switch_mixing/full-brief.txt). The historical I72 output destinations confer no I77 write permission. [references.json](../sources/i77_weighted_switch_mixing/references.json) hash-references old immutable evidence rather than copying it recursively. Precisely `README.md`, `frontier/README.md`, `frontier/TEN-FINDINGS.md`, and `frontier/iterations/README.md` may drift informationally; their initial bytes are retained. The finalized [I72 parent replay](../experiments/i72-parent-verification.json) is a frozen reference: its PASS covers evidence and diagnostics, not W. No unused spectral/percolation proof was re-audited.

Write `M=binom(n,2)`, `m=sum_i d_i/2`, `Omega=Omega_d`, `W(G)=prod_{e in G}w_e`, `Z=sum_G W(G)`, and `pi(G)=W(G)/Z`. **Target W** asks for absolute `beta_0>0,C,K<infinity` such that, for every `n>=4`, every graphical labelled simple degree vector, every positive rational complete-host activity array with `|log w_e|<=beta_0`, every start, and every `0<epsilon<1/4`,

`t_mix(epsilon)<=C n^K(log n+log(1/epsilon))`.

The chain first stays with probability one half, otherwise chooses a uniform four-set and one of its six ordered pairs of distinct perfect matchings, performs the proposed valid switch with Metropolis probability `min(1,W(G')/W(G))`, and holds on rejection. A singleton state space has mixing time zero. The logarithmic restriction is a mathematical hypothesis. There is no exact-real logarithm oracle or extra computational promise. Neither a restricted host, degree regularity, changed dynamics, nor prescribed-marginal maximum-entropy sampling is built into W.

The complete tree contains 13,223 entries, 749 manuscripts and 10,373 blobs. The fixed text domain has 9,340 files; the remaining 1,033 blobs are covered by the hash-referenced I72 inventory. Focused mechanism searches in [searches.json](../sources/i77_weighted_switch_mixing/searches.json) retain full **line multisets**, with 100 and 95 hits, over the complete `rg --files --no-ignore` domain. These counts do not assert that unrelated hits were read. Thirty-seven relevant corpus files are hash-referenced with Git blob identities and pinned raw URLs; three fresh raw requests agree with `rows.tex`, `disjoint.tex`, and `mixing.tex`. Exact read ranges and passage hashes appear in [passages.json](../sources/i77_weighted_switch_mixing/passages.json).

### Strongest operations actually compared

* **Uniform switch source:** the complete `setup`, `rows`, `triples`, `disjoint`, `slice`, and `mixing` proofs, plus the introduction's proposal convention. The crucial inputs are `row:fixed-blocks`, `row:counts`, `row:variance`, `tri:conditional-row`, `dis:conditional`, `dis:interaction`, `sl:comparison`, `dis:nonnegative`, `mix:expansion`, and `mix:normalization`. The factorial weights in `row:counts` count *uniform labelled partitions*; they are not arbitrary edge activities. The proof uses a sharp constant at both the triple and disjoint summations.
* **Fu–Qin–Wang, [2606.22636v2](https://arxiv.org/abs/2606.22636v2):** §5.1–5.2 was read directly. Lemma 5.2 covers general positive log-concave one-dimensional weights, but Lemma 5.4 identifies the count sector using exchangeability of labels. That identification, and not just log-concavity, matters here. Theorem 5.1 concerns uniform fixed-margin matrices. The source's own self-contained uniform operations are the stipulated inputs; an arbitrary external-field version is not imported.
* **Erdős–Greenhill–Mezei–Miklós–Soltész–Soukup, [1903.06600v5](https://arxiv.org/abs/1903.06600v5):** Definition 5.23, Lemma 5.24, §§7–8.1 give the encoding `A_X+A_Y-A_Z`, endpoint reconstruction, bounded exceptional entries, and the subsequent use of P-stability to count encodings. These are distinct obligations. The stable-family conclusion does not become an all-degree weighted theorem just because the new corpus removes stability from the *uniform spectral* proof.
* **Anari–Oveis Gharan–Rezaei, [1602.05242v3](https://arxiv.org/abs/1602.05242v3):** the chain and Theorem 1.1 apply to homogeneous strongly Rayleigh measures and single-element exchanges on matroid bases. A weighted subset slice fits that support; general degree-constrained graph edges do not. For example, among the three perfect matchings of K4, deleting one edge and inserting one edge from another matching never preserves all degrees. The required basis-exchange property fails. We give a direct slice proof below rather than invoking a global spectral-independence theorem.
* **Quastel, [math/0303132v3](https://arxiv.org/abs/math/0303132v3):** the current version is *Comparison inequality and two block estimate for inhomogeneous Bernoulli measures*, by Quastel alone. Its Theorem 1 attributes the complete-graph Bernoulli–Laplace bound, uniform in occupancy and bounded field, to Caputo. Its moving-particle comparison is a separate operation. The initially located v2 has a different title and author line; both versions are preserved, and only v3 is used for the current comparison. No proof step from the superseded version is needed below.
* **Chen–Guo–Vigoda–Yang, [2609.20717v1](https://arxiv.org/abs/2609.20717v1):** the current permanent algorithm's §6.3 weighted routing bound and §7.1 complement encodings were inspected, not just its headline. They preserve edge multiplicities when switching ownership, and still pay endpoint reconstruction and routing energy. Their chains use bipartite perfect **and near-perfect** matchings with hole weights. These are not the state space and transitions of W.
* **Yi, [2609.04079v1](https://arxiv.org/abs/2609.04079v1):** Theorem 1.1 and Corollary 1.3 already give deterministic weighted matching approximation on dense/full-support inputs with bounded positive weights. This makes an alternative bounded-weight matching counter a poor novelty target. A partition-function approximation is not a mixing theorem for this fixed chain. No asymptotic estimate from Yi is used as a premise here.

All six current version pages and seven PDFs (including historical Quastel–Yau v2 and current Quastel v3) are captured with HTTP response metadata, exact bytes, hashes and text extractions. Current pages display FQW v2, unified v5, Rayleigh v3, Quastel v3, permanent v1, and hafnian v1. The source perfect-matching companion's actual arbitrary-activity overlay/four-hole operation and its constant-fiber Tutte construction were also inspected. Its sampler works on enlarged colored/product matching spaces; its prescribed-degree corollary explicitly uses an unweighted host. The contingency-table companions likewise use enlarged defect/completion spaces with their own repair moves. None supplies a projection/intertwining or congestion comparison to W. The hash-referenced Dyer–Müller accepted-version introduction distinguishes host-restricted ergodicity, mixing, and counting; no fixed-small-beta conclusion is attributed to it.

## 2. Audit of the original I72 §7 and I19 §7

**PASS ORIGINAL — I72's global comparison, with its stated scope.** For distinct switch neighbors let `D_n=12 binom(n,4)`; the uniform proposal has off-diagonal probability `1/D_n`, not the probability for choosing a uniform pair of present edges. Thus

`pi(G)P_w(G,G')=min(W(G),W(G'))/(D_n Z)`.

For `N=|Omega|`, comparison of Dirichlet forms and `Var(f)=min_c E(f-c)^2` gives

`D_w(f)>=N W_min D_0(f)/Z`, `Var_w(f)<=N W_max Var_0(f)/Z`.

Consequently `gap(P_w)>=(W_min/W_max)gap(P_0)>=e^(-2 beta m)/[24 n^2 binom(n,4)]`. There is exactly one weight-range ratio in this calculation. Also `pi_min>=e^(-2 beta m)/N` and `log N<=M log 2`. The half-laziness remains valid after Metropolis rejection, so the ordinary nonnegative-spectrum L2-to-TV estimate applies. This proves the original technical bound and polynomial mixing for `beta m=O(log n)`, but leaves fixed positive beta and unrestricted m unpaid. Nothing is repaired or promoted.

**PASS ORIGINAL — I19's unbounded-activity obstruction.** On complete K6 with all degrees one, give the six cycle edges weight one and the other edges `delta=2^(-L)`. The two alternating cycle matchings have weight one and cannot switch directly to each other. Every departure from one introduces a noncycle edge, giving exit probability at most `delta/2` and stationary mass at most `1/2`. The no-departure event yields TV distance at least `1/2-t delta/2`, and hence `t_mix(1/4)>=2^(L-1)`. The exact convention gives `Z=2+3delta+6delta^2+4delta^3` and exit `(delta+delta^2)/60`; these are independently recomputed. The barrier grows through beta, not n at fixed beta. Isolated-vertex padding changes only the proposal denominator; Construction B below moreover rules out a fixed-beta counterexample anywhere in the complete-host `{0,1}` degree class.

**REPAIR: none to the original I72/I19 arguments. GAP:** a claim of fixed-strength mixing from either calculation would be a new unsupported inference. The PASS ORIGINAL labels here are this focused author's applicability audit, not the parent's still-required independent review of any new candidate.

## 3. Construction A: weighted pair heat baths and the exact slice comparison

Use exactly the source's pair-fiber partition. For `a={i,j}`, keep all edges away from a, edge ij, and each outside vertex's number of neighbors in a. Let B be the N singleton vertices, and let q be the number assigned to i, fixed by its degree. Every q-subset `S subset B` is feasible: all outside degrees, both inside degrees, and simplicity are preserved. Its conditional probability is

`mu_a(S)=prod_{v in S} theta_v / e_q(theta)`, `theta_v=w_iv/w_jv`,

where `e_q(theta)=sum_{|S|=q}prod_{v in S}theta_v`. All other factors cancel. Here `e^(-2beta)<=theta_v<=e^(2beta)` and `theta_max/theta_min<=e^(4beta)`. Define the actual weighted conditional expectation `E_a^w`, `h_a^w=I-E_a^w`, and `H_w=sum_a h_a^w`. These are orthogonal projections/sums in `L2(pi_w)` because they are conditional expectations, without any permutation-isometry assumption.

### 3.1 A uniform weighted slice Poincaré inequality, proved directly

**Lemma A1.** For every integer `N>=2`, `1<=q<=N-1`, and every positive real vector theta, let `J_theta` be the positive Metropolis exchange Laplacian on q-subsets, with rate `min(1,theta_j/theta_i)` for `S -> S-i+j`. Then

`Var_mu(f) <= theta_max/(N theta_min) <f,J_theta f>_mu`.  (A1)

For q=0,N the variance is zero. There is no hidden dependence on q or a lower bound on its distance from the endpoints.

**Proof.** First use the continuous-time generator with rate `theta_j` for `S -> S-i+j`, and positive Laplacian B. It is reversible, since `mu(S)theta_j=mu(S-i+j)theta_i`. Couple adjacent states `S=C+i` and `T=C+j`; their distance is `|S\T|=1`. Put `V=[N]\(S union T)`.

1. For `k in C,l in V`, move `k -> l` in both states at rate theta_l; distance stays one.
2. For `l in V`, move `i -> l` in S and `j -> l` in T together at rate theta_l; the chains coalesce.
3. Move `i -> j` only in S at rate theta_j, and `j -> i` only in T at rate theta_i; either coalesces.
4. For each `k in C`, move `k -> j` in S and `k -> i` in T together at rate `min(theta_i,theta_j)`; the chains coalesce. The excess of either rate is used only in its own chain, and leaves distance one.

These disjoint categories reproduce every allowed move and its exact marginal rate. There is no distance-increasing event. The total coalescence rate is

`sum_{l in V}theta_l + theta_i+theta_j +(q-1)min(theta_i,theta_j) >= N theta_min`,

because `|V|=N-q-1`. For a fully explicit discrete argument, uniformize at any `Lambda>=2q(N-q)theta_max`. Adding a simultaneous holding event gives adjacent Wasserstein distance at most `1-N theta_min/Lambda`. Join arbitrary states by a shortest exchange path and glue the adjacent couplings to obtain the same Lipschitz contraction. Applied to a nonconstant eigenfunction of `I-B/Lambda`, it implies every positive eigenvalue of B is at least `N theta_min`. Connectivity of the entire subset slice identifies the kernel. Finally

`min(1,theta_j/theta_i)>=theta_j/theta_max`,

so the reversible Dirichlet form of `J_theta` dominates that of `B/theta_max`. This proves (A1). ∎

This is a standard weighted exclusion coupling, included to pay all slice parameters. It is consistent with the classical inhomogeneous Bernoulli–Laplace result; it is not a new substantial theorem or a claim about all graph-edge supports.

### 3.2 Comparison to the exact chain is now completely paid

Let `L_w f(G)=sum_{G' switch-neighbor}min(1,W(G')/W(G))(f(G)-f(G'))`, counting each neighbor once. Let `J_a^w` be the preceding slice exchange Laplacian on each a-fiber. A singleton transposition changes exactly the four switch edges, so its ratio `theta_l/theta_k` is exactly `W(G')/W(G)`. Every switch has the source's two and only two pair-trade realizations. Therefore

`sum_a J_a^w=2L_w`, `I-P_w=L_w/D_n`.

A nonconstant slice has N>=2. Lemma A1 gives `h_a^w <=(e^(4beta)/2)J_a^w`, including constant fibers by zero variance. Hence

`H_w <= e^(4beta)L_w`.  (A2)

All comparisons are operator inequalities in the same `L2(pi_w)`. Weighted connectivity is unchanged because every permitted switch has positive rate. Thus `ker H_w` consists of constants. If the proposed global estimate

`H_w^2 >= c H_w`, `c>0` independent of n,d,  (AG)

were proved, then `Var_pi(f)<=c^(-1)<f,H_w f>` and

`gap(P_w)>=c e^(-4beta)/D_n`.

In that case a sufficient integer time from every state would be

`ceil[D_n e^(4beta)/c * { (M log 2+2beta m)/2 + log(1/(2epsilon)) }]`.

This would prove W, even with a generously chosen exponent K=6. A bound `c>=n^(-s)` for fixed s would also suffice with a larger exponent: dimension-free (AG) is a useful sufficient target, not a necessary condition for W. We do **not** claim (AG).

## 4. Actual weighted three-row law and its unpaid estimate

Fix a source triple cell: graph away from `T={1,2,3}`, and each outside vertex's number of neighbors in T. Its internal edge count e is fixed. The source's augmented binary matrix bijection remains a bijection. For an external column v its entry factors are `a_iv=w_iv`. For the extra internal column one can take:

* e=1, a column of sum two: `a_i*=1/w_jk`, with `{i,j,k}=T`. Its product on the occupied rows is the internal edge weight times a cellwise constant.
* e=2, a column of sum one: `a_i*=w_ij w_ik`; selecting its one marks the path center and gives exactly its two edge weights.
* e=0,3: internal edges are deterministic and need no extra column.

The external column factors have logs bounded by beta; the extra factors have logs bounded by 2beta. This supplies the complete weighted law on *all* feasible matrices, including the internal edges. Fixing augmented row i remains exactly conditioning on the `{j,k}`-fiber, because that was equality of partition data, independent of the measure. Thus `E_{jk}^w=E_pi[.|S_i]` within the cell.

Remove the deterministic sum-zero and sum-three columns. Let U be the sum-one labels and V the sum-two labels, partitioned as `(U_i)` according to the unique one and `(V_i)` according to the unique zero. Set `b_iv=1/a_iv` for v in V, extracting the constant product over its three rows. If `k_i=|V_i|`, the row constraints give `|U_i|=k_i+delta_i`. Define

`A(t_1,t_2,t_3)=prod_{u in U}(a_1u t_1+a_2u t_2+a_3u t_3)`,

`B(t_1,t_2,t_3)=prod_{v in V}(b_1v t_1+b_2v t_2+b_3v t_3)`.

**The exact count law is**

`P(k) proportional [t^(k+delta)]A(t) * [t^k]B(t)`,  (A3)

on the same feasible nonnegative counts as the source. Conditional on k, the two partitions are independent, but each has its product label weights. This follows simply by summing the product weights over the two separate partition sets; it accounts for every state exactly once. For unit activities the coefficients are `|U|!/prod_i(k_i+delta_i)!` and `|V|!/prod_i k_i!`, recovering the source's factorial law and its shifts `l_i=max(0,-delta_i)`, `x_i=k_i-l_i`, `alpha_i=|delta_i|`. The word “weighted” in that factorial law cannot be substituted for (A3).

### A concrete loss of the source conditional-mean property

Take two U columns, two V columns, delta=(0,0,0), all b=1, and all a=1 except `a_1,u1=a_2,u1=t>1`. This is a 3-by-4 matrix law with row sums two and column sums `(1,1,2,2)`; it is also a valid graph triple cell on seven vertices with e=0, internal degrees two, and external degrees `(1,1,2,2)`. For `f_1=1_{u1 in U_1}`,

`E[f_1 | k=(1,1,0)]=1/2`, whereas `E[f_1 | k=(1,0,1)]=t/(t+1)`.

Both conditioning events have positive mass and the same k_1. Indeed, in the first case the two U assignments have weights t,t; in the second they have weights t,1. The V factors multiply each possibility by the same count. Thus the source's reduction of `E[f_i|k]` to a function of k_i is false for arbitrary small edge fields. Fixed-size label transpositions also cease to have the invariant row-function generator used by `row:fixed-blocks`: their Metropolis rates depend on the other block's identity. Neither this example nor that observation disproves a weighted three-row Poincaré inequality.

A sharp weighted three-row estimate sufficient for the source's triple step would be

`sum_i Var(E[f|S_i])<=2 Var(f)`.

It is **GAP**, neither assumed nor disproved here. Even if a new proof gave `H_T^2 >= (1-delta_beta)H_T`, summation over triples loses `(n-2)delta_beta H_w`. A fixed `O(beta)` error is therefore insufficient for that unchanged argument. The coefficient law (A3) has not been shown here to possess a dimension-uniform row-correlation estimate that pays this sum.

### Gauge cancellation, precisely scoped

The transformation `w_ij -> w_ij a_i a_j` multiplies every graph weight by `prod_i a_i^(d_i)`, so it preserves pi, every conditional law, and every Metropolis ratio. Row and column factors on a fixed-margin binary matrix likewise cancel. However, the contrast

`log w_ik+log w_jl-log w_il-log w_jk`

is invariant under this gauge and can be nonzero even for arbitrarily small activities. The examples in this report have a nonzero contrast. No vertex scaling makes all edge activities constant in general. Lemma A1 uses the given bounded representative directly; no cost-free gauge reduction is assumed.

## 5. Exact disjoint-pair law: what survives and what fails

Take the source cell for disjoint pairs `a={i,j}`, `b={k,l}`. Let `A_0,B_0` be their outside-singleton sets, `U subset A_0`, `V subset B_0`, and M their 2-by-2 cross matrix. Set `r=M_ik+M_il`, `c=M_ik+M_jk`, and let its fixed total be s. The exact feasible conditions remain

`|U|=q_0-r`, `|V|=q_1-c`.

The law of each feasible `(M,U,V)` is proportional to

`prod_{xy cross} w_xy^(M_xy) * prod_{u in U}(w_iu/w_ju) * prod_{v in V}(w_kv/w_lv)`.  (A4)

Overlapping outside sets add no constraint: their assignments concern different edges. The conditioning identities `E_a^w=E[.|X]`, `X=(c,V)`, and `E_b^w=E[.|Y]`, `Y=(r,U)`, remain exact. If `A_r=e_{q_0-r}(theta_{A_0})`, `B_c=e_{q_1-c}(theta_{B_0})`, and `t_rc` is the sum of the cross-matrix activity products with margins r,c, then `P(r,c) proportional A_r B_c t_rc`. This includes zero coefficients for infeasible subset sizes.

Replace the unweighted swap projection by `g_ab^w=I-E[.|orbit of T_ab]`. On the two alternating central cross matrices it is the **weighted two-state heat-bath** projection, and elsewhere it is zero. It is not `(I-T_ab)/2`. Its off-diagonal heat-bath probability is `W(G')/(W(G)+W(G'))`; the Metropolis cross Laplacian has energy between one and two times its energy. Its range still lies in `(functions of X + functions of Y)^perp`, because the orbit preserves X,Y. Define `R_ab^w` by weighted centering and projection of the source equality indicator on each a-fiber.

### 5.1 The s=2 interaction survives exactly

For s=2, the cross table has only `(r,c)=(0,1),(2,1),(1,0),(1,2),(1,1)`; its positive entries are respectively

`w_jk w_jl`, `w_ik w_il`, `w_il w_jl`, `w_ik w_jk`, `w_ik w_jl+w_il w_jk`.

The center has two matrices, with their possibly unequal conditional weights. If `c!=1`, r=1 and the conditional distribution of U is the same weighted `(q_0-1)`-subset law for either c. If c=1, the conditional distribution of `(r,U)` is independent of V. Consequently `Law(Y|X)` depends only on whether c=1. The symmetric assertion holds for X given Y. When a side event is absent the law factors; if both side events occur, the center is feasible by the same subset-size argument as the source, and positive weights give it positive mass.

In the remaining case put `D_r={r!=1}`, `D_c={c!=1}`, with probabilities p_r,p_c, and centered unit indicators v,u respectively. The side events are disjoint, so

`<u,v>=-rho`, `rho=sqrt[p_c p_r/((1-p_c)(1-p_r))]<1`.

The preceding conditional-law calculation proves the same rank-one correlation decomposition as the source, now in the actual weighted inner product. On the plane spanned by u,v, write f=xu+yv. Its h_a and h_b images are `y(v+rho u)`, `x(u+rho v)`, whose inner product is `xy rho(1-rho^2)`. Therefore twice this is at least `-(x^2+y^2)(1-rho^2)`. The two residual lines lie in the weighted equality-projection ranges: on c=1, `v-E_a^w v` is a fixed scalar times the weighted centered indicator that k,l are assigned equally; on c!=1 it vanishes. The orthogonal remaining part contributes twice its squared norm and dominates `2||g_ab^w f||^2`. This proves, on every s=2 cell,

`2<h_a^w f,h_b^w f> >= 2||g_ab^w f||^2-||R_ab^w f||^2-||R_ba^w f||^2`.  (A5)

For s=0,4, X,Y are independent and the stronger nonnegative bound holds. This is an exact weighted analogue on these cells, derived from the law rather than asserted by changing inner products.

### 5.2 The s=1,3 “independent” cases are no longer independent

For s=1 the four entries `t_rc` are the four individual cross activities in a 2-by-2 table, up to reversing the row/column order. Row/column factors A_r,B_c do not change its odds ratio. It is independent exactly when `w_ik w_jl=w_il w_jk`, provided both margins have two feasible values. For s=3 the same assertion uses reciprocal activities, after extracting their common product.

Here is an actual complete-host graph cell, for every rational `1<t<=e^beta`. Take n=6, all degrees one, pairs `{0,1}`, `{2,3}`, outside vertices 4,5, and restrict to the cell with 4 assigned to the first pair and 5 to the second. It has exactly four states

`G_rc={ {r,2+c}, {1-r,4}, {3-c,5} }`, `r,c in {0,1}`.

Give edges 02 and 13 activity t, and every other complete-host edge activity one. The conditional table is `(t,1;1,t)/(2(t+1))`. Let `u=(-1)^r`, `v=(-1)^c`; then `rho=<u,v>=(t-1)/(t+1)>0`. For `f=u+v`,

`2<h_a^w f,h_b^w f>=-2rho(1-rho^2)<0`.

But the cross total is one, so `g_ab^w=0`, and only one vertex of b is a singleton for a (and conversely), so both equality error projections vanish. Thus the unchanged local inequality is false for **arbitrarily small beta>0**. At `t=101/100` the exact negative quantity is `-80800/8120601`. Extending f by zero off this common invariant cell gives the same negative sign in the full graph space, multiplied by the positive cell mass. This disproves that local sufficient lemma, not (AG), positivity of the full disjoint sum, or W.

There is a quantitative local replacement, but its naive sum is insufficient. For a positive 2-by-2 law with entries a,b,c,d, its correlation has absolute value

`|ad-bc|/sqrt[(a+b)(c+d)(a+c)(b+d)] <= |sqrt(ad)-sqrt(bc)|/(sqrt(ad)+sqrt(bc))`.

The inequality follows by applying `x+y>=2sqrt(xy)` to the two pairs of marginal products. Its right side is `tanh(|log(ad/bc)|/4)`. The cross log-odds is at most 4beta, so this is at most `tanh(beta)`. Conditional independence of the subset labels given r,c leaves just that one correlation sector. The two-projection plane calculation then bounds the negative interaction by

`-tanh(beta)(||h_a^w f||^2+||h_b^w f||^2)`.

There are `binom(n-2,2)` disjoint b for each a. Even before the s=2 comparison issue, the naive global error bound is `tanh(beta) binom(n-2,2)<f,H_w f>`. This is an upper bound on the loss of this proof, not a lower bound on a spectral gap or evidence of slow mixing.

### 5.3 The sharp equality-projection slice comparison also fails

On a weighted `N=3,q=1` slice with theta=(t,1,1), write `p=(t,1,1)/(t+2)`. Let S be the sum of the three weighted orthogonal projections onto centered equality indicators, and G the sum of the three two-site weighted heat-bath complements. For `f=1_{first label occupied}`, direct calculation gives

`<f,(S-G)f> = 2t(t-1)/[(t+1)(t+2)^2] >0` for t>1.

Indeed each equality indicator is the occupancy indicator of the third label. Its projection energy is `p_k(f_k-E f)^2/(1-p_k)`. The heat-bath energy on pair ij is `p_i p_j(f_i-f_j)^2/(p_i+p_j)`. Summing gives the displayed difference. At t=101/100 it is `20200/18210801`. This weighted slice is itself a genuine pair fiber: take degrees `(1,2,1,1,1)` on five vertices, no outside edges or edge 01, and activity `w_02=t`, others one. Thus the uniform source's exact `S<=G` has no unchanged weighted extension, even after replacing the invalid swap projection by the correct heat bath. A weakened comparison is not ruled out; it must be paid in the *aggregate*.

### 5.4 The exact remaining aggregate obligation

Projection algebra still gives, with ordered disjoint sum `D_w=sum_{a disjoint b}h_a^w h_b^w`,

`H_w^2-H_w = sum_T[(H_T^w)^2-H_T^w] + D_w`.  (A6)

The source has nonnegative triple corrections and a nonnegative full disjoint sum. The weighted construction has not bounded their **combined** negative part. A precise sufficient missing inequality is

`sum_T <f,((H_T^w)^2-H_T^w)f> + <f,D_w f> >= -(1-c)<f,H_w f>`,  (A7)

for one absolute beta_0,c>0 and all the quantifiers of W. A polynomially small c would also suffice with corresponding uniformity. The new slice lemma already pays the subsequent switch comparison. The two local counterexamples explicitly prevent calling an unchanged proof a PASS; they do not justify calling (A7) false. No dimension-uniform tensorization, logarithmic Sobolev estimate, or cancellation for (A7) is asserted.

## 6. Construction B: a completely worked weight-cancelling flow

This construction uses neither weighted row tensorization nor the uniform source spectral gap. It also isolates exactly why a bounded-defect encoding would help arbitrary degrees.

### 6.1 Paid theorem on complete-host matchings

**Lemma B1 (technical matching subclass).** Let `n>=4`, `d_i in {0,1}` be graphical, `m=sum d_i/2`, `|Omega_d|>1`, and `|log w_e|<=beta<infinity`. For the exact chain of W,

`gap(P_w) >= [2m n^4 D_n e^(8beta)]^(-1)`.  (B1)

Together with `log(1/pi_min)<=M log 2+2beta m`, this proves polynomial mixing from every start for every fixed beta on this class. Constants may depend on fixed beta. Inactive vertices remain in the proposal denominator D_n. This is a deliberately loose explicit bound, not an optimization or a substantial nomination.

**Paths.** For ordered endpoint matchings X,Y on the active vertices, their symmetric difference consists of vertex-disjoint even alternating cycles. Common edges are fixed. Order cycles by their least vertex. On each cycle write

`v_0,v_1,...,v_(2k-1)`

with v_0 least and `v_0 v_1` in X; then the X edges are `v_(2r) v_(2r+1)` and Y edges `v_(2r+1) v_(2r+2)` with cyclic indices. After j pivot switches, `0<=j<=k-1`, the current matching on this cycle consists of

`v_1v_2, ..., v_(2j-1)v_(2j)`, the pivot `v_0 v_(2j+1)`, and remaining X edges.

For `j=0,...,k-2`, switch the pivot and `v_(2j+2)v_(2j+3)` into `v_(2j+1)v_(2j+2)` and `v_0v_(2j+3)`. All four vertices are distinct and the new edges are absent in the current matching; the host is complete. Thus every step is a legal switch. The cycle uses k-1 steps, and the full path has length at most m. Completed cycles agree with Y; unstarted cycles agree with X. If X=Y the path is empty. These deterministic paths route demand `pi(X)pi(Y)` and conserve it at each interior state.

**Encoding and exact product cancellation.** At the departure state Z of a path edge define the integer edge array

`E=1_X+1_Y-1_Z`, `W(E)=prod_e w_e^(E_e)`.

It always satisfies `W(X)W(Y)=W(Z)W(E)` and has every active degree one as an integer array. At the start of an active cycle (j=0), E is already a perfect matching F. Store the active least vertex a=v_0 and its X-neighbor b=v_1, along with flag zero.

At an interior departure (`1<=j<=k-2`), E has precisely one negative edge `ap`, with `a=v_0`, `p=v_(2j+1)`, and no entry two. Its positive support has degree two at a,p and degree one elsewhere. Put `b=v_1`, `c=v_(2j)`. Delete positive edges ab,pc, erase the negative edge ap, and insert bc. The result F is a perfect matching: a,p now have degree one, b,c recover degree one, and all other degrees are unchanged. The four vertices are distinct; b,c were matched to a,p in the positive support, so bc was absent. Store flag one and `(a,p,b,c)`. In edge-array notation,

`E=1_F+1_ab+1_pc-1_bc-1_ap`,

so `e^(-4beta)<=W(E)/W(F)<=e^(4beta)`. At cycle starts the ratio is one. For every departure, F belongs to the *same* state space, not a nearby degree space.

**Endpoint-to-path incidence is injectively encoded.** Fix Z. From F and the code, reconstruct E by the preceding formula, or E=F for flag zero. The array `E+1_Z=1_X+1_Y` identifies all common edges (multiplicity two) and all alternating cycles (multiplicity one). The code identifies the active cycle and which of its two colorings belongs to X. On each earlier cycle, Z equals Y; on every later cycle Z equals X. These observations uniquely reconstruct both endpoints. No exponentially many independent cycle-color bits remain. There are at most `n^2+n^4<=2n^4` possible codes. The same reconstruction suffices for a fixed *directed transition*, which has at most one occurrence on an endpoint path. Paths have no repeated states: each step completes a new Y edge on the first unfinished cycle, except that its pivot is replaced, and the terminal edge completes that cycle.

**Congestion, normalization, and mixing.** Injectivity and weight cancellation give, at any directed edge `e=(Z,Z')`,

`sum_{(X,Y):e on path} pi(X)pi(Y) <= 2n^4 e^(4beta) pi(Z) sum_F pi(F) =2n^4 e^(4beta)pi(Z)`.

Multiplying by the path-length bound m accounts for Cauchy–Schwarz along each path. The exact chain capacity is

`Q(e)=min(pi(Z),pi(Z'))/D_n >= e^(-4beta)pi(Z)/D_n`,

because a switch changes four activity factors. Therefore the length-weighted directed congestion is at most `rho=2m n^4 D_n e^(8beta)`. Finally,

`Var_pi(f)=(1/2)sum_X,Y pi(X)pi(Y)(f(X)-f(Y))^2 <= rho D_P(f)`.

To see the last inequality without a flow black box, telescope along each routed path, apply Cauchy–Schwarz with its length, sum the demands, and collect each directed transition's squared difference. The factor one half turns the directed capacity sum into the usual Dirichlet form. This proves (B1); half-laziness and the point-mass L2 estimate then give the stated mixing conclusion. ∎

This proof pays length, legality, exact product weights, same-degree repair, code multiplicity, endpoint reconstruction, conservation, capacities, and stationary normalization. It also shows why I19 cannot be amplified at fixed beta simply by adding matching vertices or isolated vertices. It proves nothing about a hypothetical higher-degree phase separation.

### 6.2 Why this does not extend automatically to arbitrary degrees

For general degree vectors, pairing red and blue half-edges at each vertex decomposes `X triangle Y` into alternating circuits, but those circuits need not be vertex-disjoint simple cycles. A pivot chord may be occupied by a common edge or by an untouched circuit. The matching repair above then need not be simple or degree preserving. Randomizing pairings introduces a large number of route descriptions; their normalized multiplicity must be paid rather than bounded by raw counts.

The inspected unified primary construction addresses these issues with a different sweep, pairing reconstruction and exceptional-entry control. Its algebraic encoding still has the exact weighted identity `W(X)W(Y)=W(Z)W(A_X+A_Y-A_Z)` when W is extended to integer entries. Its Lemma 8.1 pays the normalized pairing incidence before Lemma 8.2 counts the compatible encodings. The latter explicitly uses the ratio of realization counts for perturbed degree sequences; its repair can end in `d+1_x+1_y`, not necessarily d. The accepted all-degree uniform spectral gap supplies neither that count ratio nor a bounded-distance same-degree repair. Unweighted P-stability alone would also require care when replacing counts by weighted partition functions.

A precise sufficient general flow interface is the following. Construct unit routings for every ordered X,Y, of length at most `ell(n)`, using legal switches. At every directed edge with departure Z, assign each route occurrence an encoding `F in Omega_d` and a code from at most `B(n)` values, with total routing probability at most one per `(F,code)` for fixed Z. Require

`1_X+1_Y-1_Z=1_F+Delta`, `sum_e |Delta_e|<=r(n)`.

Then the same calculation proves congestion at most

`D_n ell(n) B(n) exp(beta(r(n)+4))`.  (B2)

Thus polynomial ell,B and `r=O(log n)` (or a constant) would prove fixed-beta W; more generally a directly proved weighted encoding-sum bound would do. **GAP:** no such all-degree routing/repair is constructed here. B2 is a conditional reduction, not a proof disguised as an encoding lemma.

The source's Havel-style connectivity path cannot be inserted as a substitute. A concrete failure of its hub encoding already occurs in matchings. On n=4k vertices let R have edges `(4r,4r+1),(4r+2,4r+3)`, and let X have `(4r,4r+2),(4r+1,4r+3)` in every block. Let Y agree with X on blocks r>=1 and use R on block zero. The source's deterministic highest-residual-degree, label-tie-breaking hub is R. A route from X to R and then to Y passes through Z=R, where E has entry two on `2(k-1)` common endpoint edges and minus one on `2(k-1)` hub edges. Its L1 distance from *every* simple graph array is at least `4(k-1)`. This only rejects that proposed use of the connectivity construction; Lemma B1 supplies a better route for these very endpoints. Uniform mixing does not manufacture a weight-cancelling path family.

### 6.3 Contribution disposition

B1 is a complete technical construction in a standard degree class. Its mechanism is the familiar alternating-cycle complement encoding, sharpened only enough to expose a constant-size repair on a complete host. The source matching companion already uses product-preserving overlays, and the current primary permanent paper explicitly reconstructs endpoints from a complement encoding plus an active-cycle choice. The graph-specific extra step here is a four-edge repair available because matching cycles are disjoint and all host edges exist. This concrete reduction is why B1 is not nominated as substantial. An all-degree solution of the unresolved repair problem would be a materially different contribution and would require fresh independent review.

## 7. Diagnostics, seal, and handoff

Run from `/home/mj-kang/Documents/Dev/math/openai-proof-research`:

```sh
python -B frontier/experiments/i77_weighted_switch_mixing/verify.py
```

The verifier is offline and read-only. It checks every assigned sealed artifact, immutable reference hashes, the exact four-ledger drift allowlist and snapshots, the full fixed corpus against SHA-256 and Git blob identities, both search line multisets, selected source references and exact passages, capture-time version bindings, HTTP-response hashes, PDF text replays, fresh raw pins, and independent rational diagnostics. It never fetches, rewrites a source, refreshes a seal, or writes bytecode. `seal-v1.json` excludes itself and the final verifier output; its purpose is immutable provenance, not analytic certification.

The standard-library diagnostic uses exact rational arithmetic and exact Schur-complement PSD checks, not floating eigenvalues. It checks 15 weighted slice Poincaré matrices and 702 coupling marginal/drift identities, the two explicit negative source-analogue witnesses, six nontrivial/degenerate s=2 cell inequalities, and the full weighted three-row coefficient law in the 15-state example. Literal graph enumeration on 3, 6 and 15 states independently checks the source proposal normalization, detailed balance, conditional projection identities, gauge invariance, switch multiplicity two, (A2), and the exact global expansion (A6). For all 105 K8 matchings it checks 11,025 ordered demands, 25,620 path incidences, every endpoint reconstruction, four-edge repair, exact product-weight identity and total congestion. The K6 I19 partition polynomial and escape formula are recomputed at four dyadic activities. These checks are meaningful finite tests of the new constructions; they prove no all-n mixing assertion by themselves.

The first diagnostic run passed without code or mathematical repairs; its original stdout and empty stderr remain preserved. An initial shell read omitted the intended working directory and was repeated at the correct directory without any write. The T3 brief read initially exceeded the tool's text limit; the successful paginated read recovered all bytes. Quastel–Yau v2 was an early literature lead; the live version page prompted capture and use of Quastel v3, while retaining v2. These provenance corrections do not change an issued proof or refresh any old seal.

**Handoff:** I72's scoped comparison and I19's scoped obstruction pass their original applicability audit. New Lemmas A1/A2 and B1, the exact weighted laws, the s=2 analogue, and the two local obstructions are proved here as technical partials. **W and its all-degree fixed-beta aggregate/flow alternatives remain GAP.** No fixed-small-beta counterexample has been produced. The most useful next obligation is the combined estimate (A7), or the explicit all-degree bounded-defect, bounded-multiplicity flow interface (B2). Neither local failure is a disproof of W. Parent-controlled ORIGINAL-proof and contribution reviews remain necessary before any future nomination; no accepted count is increased.
