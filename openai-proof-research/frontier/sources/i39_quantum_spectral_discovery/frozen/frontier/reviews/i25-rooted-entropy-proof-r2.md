# I25 rooted matching entropy — independent full-proof review R2

Date: 2026-10-09. **Verdict: PASS for the full universal rooted theorem, and hence for its stated unrooted and counting consequences. No mathematical repair is required.** The ancillary full-polytope Klee local-maximum assertion also passes. This is a source-relative proof verdict under the instruction to accept all proofs at `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`; it is not merely a covariance-kernel or finite-example PASS. It is not a significance decision, priority claim, or accepted-count increment.

Reviewed candidate: [I25 resumed report](../iterations/i25-matching-entropy-improvement-resumed.md), **32,900 bytes**, SHA-256

`154c12153988580f2845680f6824168c981e1f420c36c623886788b79f780824`.

The decisive new deduction is valid: root propagation makes the corrected entropy defect exactly additive across every tight odd-cut split. Induction consequently excludes tight cuts at a positive global maximum, permitting the degree-equation dimension bound there. The indicator-modified covariance trace then supplies a strict contradiction for every order above the four-vertex base at coefficient `3/2 + epsilon`. Passing to the endpoint is legitimate. Neither I22's unpaid separator term nor its insufficient general-face trace is being dropped.

## 1. Scope, frozen record, and source contracts

I read AGENTS.md, the current ledger, the complete candidate and complete [I22 report](../iterations/i22-combinatorial-discovery.md), including its original separator objection. The ledger remains at four accepted substantial findings toward ten. The historical original and resumed discovery briefs are frozen verbatim as task JSON; the operative review obligations are recorded in [review-brief.txt](../sources/i25_rooted_entropy_proof_r2/review-brief.txt). No agents were started. All writes were confined to this report and the assigned R2 source/experiment directories. Neither candidate nor original/resumed research files, shared indexes, staging area, commits, or other projects were modified by this review.

[inputs.json](../sources/i25_rooted_entropy_proof_r2/inputs.json) identifies 68 frozen inputs, including the candidate, I22, both historical task records, immutable upstream pin, complete preprint tree, ledger, author contracts/seal, selected pinned sources, primary literature bytes, and diagnostic scripts/results. [preservation.json](../sources/i25_rooted_entropy_proof_r2/preservation.json) records 1,297 files in the original and resumed source/experiment trees, including all 1,226 original files and vendor files. The original vendor tree and shared corpus were not copied or imported. Parent verification output and shared-ledger/index drift are reported separately from changes to immutable mathematical inputs.

The actual source is *Entropy and Face Dimension of the Perfect-Matching Polytope*, at the pinned path `preprints/Entropy-and-Face-Dimension-of-the-Perfect-Matching-Polytope-September-23-2026/build/`. I read the following complete files, including their proofs: sections `01-introduction`, `02-polytope`, `03-entropy`, `04-consequences`, `05-weighted`, `10-examples`, and appendices A, B, C. The algorithm-only sections 06–09 are not dependencies of this theorem and are not claimed as full proof reads. The FPRAS companion was read at its actual main-theorem and weighted-intermediate-input passages, not treated as a prescribed-mean sampling theorem. All 18 selected pinned files have independently checked Git-blob/SHA-256 identities against the frozen complete, untruncated tree. Their exact raw URLs are in the frozen [pinned manifest](../sources/i25_rooted_entropy_proof_r2/frozen/frontier/sources/i25_matching_entropy_improvement_resumed/pinned-manifest.json).

The proof dependencies are these precise interfaces:

- `02-polytope.tex`, `geom:thm-polytope` and `geom:lem-face`: the degree/nonnegativity/odd-cut description, relative interior of the minimal face, its active-row direction space, and support of every realizing law on that face. The no-nontrivial-tight-cut branch of `geom:prop-rank` explicitly supplies codimension at most `2m`; the general bound is only `3m-2`.
- `geom:lem-gluing`: conditional gluing on the shared crossing **label**, preserving every marginal. `geom:lem-reduction`: exact probability-preserving removal of zero and one coordinates, with the residual polytope/face identification.
- `03-entropy.tex`, `ent:continuity`: attainment and continuity on the whole polytope. `ent:exponential`: a finite parameter and a law positive on all atoms of the minimal face; all finite tilts remain entropy maximizing at their own means in that same face. Its proof handles redundant constraints and boundary means explicitly.
- `ent:covariance-range` and `ent:second-variation`: covariance range equals the face tangent space, and first-order stationarity removes the acceleration term. The candidate's changed Hessian is derived below, rather than assumed covered by the source's unrooted formula.
- `ent:components`, the proof of `H<=F`, `cons:variational`, and the source's structural-count evaluations: used only for the reported consequences.
- `10-examples.tex`, `ex:lem-expansion-face` and `ex:prop-klee-face`: the minimal face at uniform Klee means is precisely the triangle spanned by three edge-disjoint matching vectors. This, not a claim that the graph has only three total matchings, is the ancillary example's premise.

The stronger source appendices do not supply a missing premise by fiat. Appendix A's laminar and quotient proofs still yield the general codimension `3m-2`; its direct entropy bounds have coefficients three/four. Appendix B's complete normalized inverse-covariance proof gives `F-H <= 8m(1-exp(-F/m))`; it does not produce a star reserve. Appendix C's singleton-loop counting reduction does not enlarge the candidate's loopless scope. These inspected proofs are accepted upstream inputs, not themselves being audited for truth.

[read-contracts.json](../sources/i25_rooted_entropy_proof_r2/read-contracts.json) preserves 20 exact read slices: nine complete entropy-source files, two companion passages, the two full reports, and seven primary-literature passages. The verifier also independently validates all 62 inherited statement contracts and the author's ten proof-read slices. Byte validation of a contract is distinguished from a claim to have reviewed every unrelated algorithmic proof.

## 2. Exact statement that passes

Let `G=(V,E)` be any finite undirected loopless multigraph, with each parallel edge a distinct labelled coordinate, `|V|=2m>=2`, and at least one perfect matching. Let `P(G)` be the convex hull of its labelled perfect-matching incidence vectors. For **every** `x in P(G)` and **every** `v in V`, define, with natural logarithms and continuous endpoint products,

\[
H(x)=\max_{\mathbb E\mathbf1_M=x}\operatorname{Ent}(M),\qquad
F(x)=-\sum_e x_e\log x_e,\qquad
B(x)=-\sum_e(1-x_e)\log(1-x_e),
\]
\[
b_v(x)=-\sum_{e\in\delta(v)}(1-x_e)\log(1-x_e),\qquad
W_v(x)=B(x)-b_v(x),\qquad D(x)=F(x)-H(x).
\]

Then

\[
\boxed{D_G(x)\le\tfrac32 W_{G,v}(x).}
\]

All boundary means, disconnected graphs, absent/unusable edges, forced edges, and finite labelled parallel multiplicities are included. A graph with no perfect matching has no feasible mean. The empty graph has `F=B=H=0`; it has no rooted assertion. No bound on degree or number of tight cuts is assumed. No finite-parameter exponential representation on **all** matchings is assumed at a boundary mean. No polynomial sampler or prescribed-mean optimizer is concluded.

## 3. Independent reconstruction of the full proof

### 3.1 The root reserve pays the separator exactly

Take an odd set `S` with both shores of size at least three and `x(delta(S))=1`. Complement it if needed so the designated root `v` lies in `S`; since the original order is even, its complement is also odd. Retain `S` in `G1`, contracting its complement; retain the complement in `G2`, contracting `S` to `z`. Discard edges wholly inside the contracted shore. Retain the original label on every surviving edge, including each crossing edge in **both** children. These operations create no loops; they may create parallel edges, which remain distinct. The child orders are even, at least four, and strictly smaller.

For every parent law with mean `x`, the crossing count is a positive odd integer with expectation one, hence equals one almost surely. Its two restrictions are child matchings with common crossing label `L`. Conversely, any two child matchings with the same crossing label glue uniquely to a parent matching crossing once. In particular the child means are feasible without any appeal to a relaxed polytope.

Write `q_e=x_e` on the cut, and let `h(q)` and `b(q)` be its categorical and complementary entropies. For every parent law, the chain rule and conditional subadditivity give

\[
\operatorname{Ent}(M)\le H_1(x_1)+H_2(x_2)-h(q).
\]

Choose maximizing laws at these **fixed** child means, whose crossing-label marginals both equal `q`. Draw `L~q` and, given `L`, draw the two child matchings independently from their respective conditional laws. This realizes the original mean and attains the displayed entropy. Terms with `q_e=0` require no conditional distribution. Thus

\[
H=H_1+H_2-h(q),\quad F=F_1+F_2-h(q),\quad
B=B_1+B_2-b(q),\quad D=D_1+D_2.
\]

The star at the retained root in `G1` has the same labelled coordinates as the parent root star. The star at `z` in `G2` is exactly the cut. Therefore

\[
W_v=B_1+B_2-b(q)-b_v
=(B_1-b_v)+(B_2-b_z)=W_{1,v}+W_{2,z}.
\]

It follows for every real `c` that

\[
(D-cW)_{G,v}=(D-cW)_{G_1,v}+(D-cW)_{G_2,z}. \tag{R2-A}
\]

This is an exact identity, not an inequality with an omitted separator. Edge by edge: a crossing edge incident to the root is uncharged in both children, while any other crossing edge is charged once in `G1` and uncharged in `G2`. An internal edge is charged in its one retained child exactly when it was charged in the parent.

An inherited root may itself have been created by an earlier contraction. Nothing above requires it to be an original vertex: it is an ordinary vertex of the current loopless labelled graph, with its actual star. Inductively, arbitrary further valid splits telescope (R2-A). No laminar ordering of all original tight cuts is necessary. Strictly decreasing child orders make the recursion finite. In particular, the sum of leaf root-star reserves equals the original reserve plus the sum of all split complementary entropies. This resolves the precise positive-separator objection in I22.

### 3.2 Parallel labels and the small-order base

For each parallel class `C_a`, put `y_a=sum_{e in C_a}x_e<=1` and, when `y_a>0`, `r^a_e=x_e/y_a`. A labelled matching specifies a collapsed matching `Y` and a chosen label in each selected class. Conditional entropy is at most the sum of the label entropies. Averaging over `Y` and using concavity gives an upper bound `sum_a y_a h(r^a)` for the extra entropy: the aggregate conditional label distribution, given that a class is selected, is precisely `r^a`. A maximizing collapsed law with independent label choices of these distributions attains the upper bound. Consequently

\[
H_G(x)=H_{\rm simple}(y)+\sum_a y_a h(r^a),\qquad
F_G(x)=F_{\rm simple}(y)+\sum_a y_a h(r^a).
\]

Thus `D` is invariant. A zero class contributes zero and is simply ignored. For `beta(u)=-(1-u)log(1-u)`, concavity and `beta(0)=0` imply `beta(x_e)>=x_e beta(y_a)/y_a` within a positive class. Summing proves `sum beta(x_e)>=beta(y_a)`. Each class is wholly incident or wholly nonincident to a given root, so `W_G,v>=W_simple,v`. The inequality transfers from collapsed to labelled graphs in the required direction for nonnegative `c`; there is no illicit cancellation of label entropy in `B`.

On two vertices, `F=H` and `W_v=0`, however many parallel labels exist. On four vertices, after collapse and padding missing edges by zero, the three possible perfect-matching types are disjoint pairs of edges. A feasible mean determines their probabilities `p=(p1,p2,p3)`. For each root one of each type's two edges is incident to it. Hence `H=h(p)`, `F=2h(p)`, `D=h(p)`, and `W_v=b(p)`.

For completeness, the scalar inequality `h(p)<=3b(p)/2` really does hold on the entire closed ternary simplex. Set

\[
f(u)=-u\log u+\tfrac32(1-u)\log(1-u),\qquad
f''(u)=-1/u+\tfrac{3/2}{1-u}.
\]

The second derivative changes sign at `a=2/5`. On the simplex boundary, `sum f=(1-3/2)h(p,1-p)<=0`. At an interior maximum all first derivatives agree. Two coordinates at least `a`, one strictly above, violate the second derivative test along their difference; two equal to `a` violate stationarity with the smaller third coordinate. If all coordinates are at most `a`, strict decrease of `f'` forces equality, giving `sum f=log(8/9)<0`. Otherwise exactly one is above `a`, and the other two are equal below `a`; write the vector as `(t,t,1-2t)`, where `0<t<1/3`.

For `g(t)=2f(t)+f(1-2t)` and `u=(1-2t)/t>=1`,

\[
g'(t)/2=\log u-\tfrac32\log((u+1)/2)=k(u),\qquad
k'(u)=\frac{1-u/2}{u(u+1)}.
\]

The function `k` rises from zero, then falls to minus infinity, with exactly one further zero. Because `u` decreases with `t`, `g` first decreases and then increases. Its maximum on `[0,1/3]` is at an endpoint, whose values are `0` and `log(8/9)`. This covers every remaining possibility for a positive maximum and proves the scalar inequality. Therefore the two- and four-vertex rooted bases pass for all means and labelled multiplicities. They also hold for every `c>3/2`, since `W>=0`.

### 3.3 Boundary reductions, including loss of the root

Delete every zero-mean edge. Every law at that mean omits it, and its contributions to `F`, `B`, and each root star vanish. More strongly, every feasible mean of the resulting graph zero-extends to a mean of the original graph with the same objective. Thus a global maximizer remains a global maximizer after this operation, even though order has not decreased.

If an edge has mean one, every realizing law contains it. All other edges at its two endpoints have mean zero. Delete those endpoints and the forced edge. The source's bijection of laws preserves `F,H,B`, and the remaining order strictly decreases. If the root survives, its nonzero star coordinates survive and `W` is unchanged. If the root is deleted, its entire complementary star entropy was zero, so the original `W_v=B`. For any residual root `w`, the smaller rooted assertion yields

\[
D=D_{\rm residual}\le c(B-b_w)\le cB=cW_v.
\]

If no vertices remain, all these quantities are zero. This argument needs only a smaller-order inequality at the residual mean; it does **not** need to transfer global maximality to a different residual-root objective. That distinction prevents a possible deleted-root circularity.

### 3.4 Attainment, face laws, and the modified trace

For a fixed finite graph and root, `E_c=F-cW_v-H` is continuous on compact `P(G)`, so it attains a maximum. The source's continuity statement is global, not just relative-interior continuity: compactness of the law simplex gives upper semicontinuity; the finite inequality description and mixing along an extendible segment give lower semicontinuity. Thus a boundary maximizing sequence cannot evade attainment.

At a point with all retained coordinates in `(0,1)`, let `T` be its minimal-face tangent space and `d=dim T`. The maximizing law is positive on **all face atoms** and has a finite exponential parameter `theta` on those atoms. One can see positivity by mixing with a full-support law of the same mean; a previously zero probability increases entropy by a positive `t log(1/t)` term. Stationarity of entropy in the law fiber gives the exponential representation even with redundant constraints. Its covariance `K` has kernel `T^perp`, since zero variance means a linear functional is constant on the affinely spanning face atoms. Therefore `im K=T` and `rank K=d`.

Tilt the face law by `theta+ta` and denote its mean by `y(t)`. The same finite Gibbs variational comparison makes it entropy maximizing at its own mean; it remains in the same minimal face. Hence

\[
y'(0)=Ka,\quad y''(0)\in T,\qquad
H(y(t))=\log Z(\theta+ta)-(\theta+ta)\cdot y(t).
\]

For `J=F-cW_v`, its diagonal Hessian is

\[
A_{ee}=-1/x_e+\frac{c\,\mathbf1_{e\notin\delta(v)}}{1-x_e}.
\]

At a local maximum of `E_c`, both signs of every tilt are feasible and

\[
0=E_c'(0)=(\nabla J+\theta)\cdot Ka\qquad\text{for all }a.
\]

The vector `grad J+theta` is thus orthogonal to `T`, so the acceleration term vanishes in the second derivative:

\[
0\ge E_c''(0)=(Ka)^TA(Ka)+a^TKa.
\]

For positive covariance eigenvalues `lambda_i` and orthonormal eigenvectors `u_i`, substitute `a=u_i`, divide by `lambda_i`, and sum. This gives

\[
0\ge d+\operatorname{tr}(KA).
\]

It neither inverts an ambient covariance kernel nor assumes that `A` and `K` commute. Since each coordinate is Boolean, `K_ee=x_e(1-x_e)`. The degree equations give `sum_e x_e=m` and, critically, `sum_{e not incident to v}x_e=m-1`. With `s=|E|`,

\[
\boxed{0\ge d-s+m+c(m-1).} \tag{R2-T}
\]

The root term costs exactly `c` relative to the source's unrooted trace. Its coefficient is not guessed by substituting a new objective into an old theorem. The calculation uses smooth finite tilts only, so it does not demand smoothness of `H` across different faces.

### 3.5 The induction is global and closes for every graph

Fix any `epsilon>0` and put `c=3/2+epsilon`. Induct on `m` with the simultaneous assertion for **every graph of order `2m`, every mean, every root**, using the same constant `c` at all smaller orders. Sections 3.2–3.3 establish the small-order and fixed-coordinate steps.

Suppose there is a counterexample at order `2m`, `m>=3`. For that particular finite graph and that particular root, maximize `E_c` on its polytope; the maximum is positive. No maximization over the class of all graphs or edge multiplicities is required. Delete zero edges, preserving the positive global maximum. A value-one edge would reduce to a smaller-order instance and contradict positivity, so all retained coordinates lie strictly between zero and one.

If a nontrivial odd cut is tight at this maximum, its two child orders are smaller. Both rooted inequalities are available at the restricted means by induction, irrespective of whether those means optimize any child objective. Identity (R2-A) then says the parent defect is nonpositive. Thus **there is no nontrivial tight odd cut at the positive global maximum**. This is the justified point where the stronger dimension estimate becomes available.

Positivity leaves no active nonnegativity rows. Singleton odd cuts and their complements are the degree rows. All other odd-cut inequalities have strict slack. Because the graph is finite, there are finitely many such inequalities, and sufficiently small two-sided perturbations preserving degrees remain feasible. Therefore `T` is the kernel of the `2m` degree rows, and `d>=s-2m`. Redundancy, bipartite components, and disconnectedness can only increase this lower bound; row independence is unnecessary.

Combining with (R2-T),

\[
0\ge d-s+m+c(m-1)
\ge(c-1)m-c
=\frac{m-3}{2}+\epsilon(m-1)>0,
\]

a contradiction for every `m>=3`. This proves the assertion at coefficient `3/2+epsilon` for every order and root. For any fixed `G,x,v`, the finite sum `W_v` is nonnegative and finite. Taking `epsilon` down to zero gives `D<=3W_v/2`, including `W_v=0`. No uniform bound across all graphs or convergence of maximizing points is required. The epsilon step is essential to this particular proof at `m=3`: the endpoint trace lower bound alone is zero, not contradictory.

This completes a universal proof. It is not an inference from the finite numerical audit.

## 4. Ancillary Section 6: Klee local maxima

The source gives a minimal face with three disjoint matching types of size `m`, partitioning all `3m` edges. On its relative interior, a mean specifies a unique type law `p`. Hence

\[
H=h(p),\quad F=mh(p),\quad B=mb(p),\qquad
E_{3/2}=(m-1)h(p)-\tfrac32m b(p).
\]

At the uniform type law,

\[
E_{3/2}=m\log(8/9)-\log3<0.
\]

For a tangent probability perturbation `sum a_i=0`, the second derivative is `(3-3m/4)sum a_i^2`. Thus for every integer `m>4` the point is a strict face-local maximum. The edge covariance has entries `2/9` within one type and `-1/9` between types, rank two, and positive eigenvalues `m/3`. The separable Hessian is `-3I/4`; on positive covariance eigenvectors the normalized second variation is `1-m/4<0`. These calculations check the full tangent matrix inequality, not just its trace. Every star and every tight-cut sum is constant on the three atoms, so the global matching constraints are respected.

The candidate's extension to a strict local maximum in the **whole polytope** is also correct. To make its uniform estimates explicit, let `ell` be the sum of finitely many active nonnegative slacks exposing this face. If there are outside atoms, let `delta>0` be the minimum of `ell` over them. For any nearby mean `x'` and any realizing law, its outside mass `r` satisfies `r<=ell(x')/delta`, hence tends to zero uniformly as `x'` approaches the uniform face mean `x`. For `r<1`, condition on the face and call the conditional mean `y`. Then `y` tends to `x` uniformly, and `||x'-y||<=C0 r` because the polytope is bounded.

The face law at `y` is unique, so that conditional law has entropy `H(y)` even if the original realizing law was not maximizing. Consequently

\[
H(x')\ge h_2(r)+(1-r)H(y).
\]

The function `J=F-3B/2` is Lipschitz near `x`, since every coordinate of `x` equals `1/3`. Also `H(y)<=log3`. It follows that

\[
E(x')\le E(y)+Cr-h_2(r).
\]

For all sufficiently small positive `r`, `h_2(r)>Cr`. Choose the neighborhood small enough that `y` lies in the strict face-maximum neighborhood. If `r>0`, the last display is strictly below `E(x)`; if `r=0` and `x'!=x`, strict face maximality applies. If there are no outside atoms, the face proof alone suffices. Thus the claimed full local assertion passes with uniform constants, not just along individual transverse curves.

This is ancillary and not used to prove the theorem. It explains why attempting to exclude **all** fractional local maxima would fail: these maxima have negative defect, while matching vertices have defect zero. On these same faces `D=(m-1)h(p)` and `W_v=(m-1)b(p)`. The uniform rooted ratio is the old `c3=log3/[2log(3/2)]` for `m>1`, not a new numerical obstruction.

## 5. Section 9 and other consequences

All stated implications pass with their indicated scope.

First, `sum_v b_v=2B`, since an edge has two distinct endpoints. With `2m` vertices, `max_v b_v>=B/m`. The assertion for **every** root allows selection of a maximizing root at each mean, yielding

\[
H\ge F-\tfrac32(B-\max_v b_v)
\ge F-\tfrac32(1-1/m)B
\ge F-\tfrac32 B.
\]

The inequalities have the right direction, including `m=1` and `B=0`. Next `beta(u)<=u` on `[0,1]`, so `W_v<=sum_{e not incident to v}x_e=m-1`. Thus `0<=D<=3(m-1)/2`; the lower inequality is the source's star-chain-rule upper bound `H<=F`.

For every finite real edge parameter `theta`, the finite Gibbs variational identity gives

\[
\log Z_\theta=\max_{x\in P(G)}[H(x)+\theta\cdot x].
\]

Let `Q_theta=max[F+theta dot x]`. The pointwise two-sided bound just proved gives

\[
Q_\theta-\tfrac32(m-1)\le\log Z_\theta\le Q_\theta.
\]

The extrema are attained by compactness. The bracket is analytic and uses natural logarithms; converting the source's binary-log version introduces no extra coefficient here. It does not assert computational access to either maximizing mean or exponential law.

For `k>=2` edge-disjoint labelled perfect matchings, their uniform mixture has `km` nonzero edge coordinates equal to `1/k`. Each root sees exactly `k` of them. Thus `F=m log k` and

\[
W_v=(m-1)(k-1)\log\frac{k}{k-1}.
\]

Using `log N>=H` and exponentiating gives exactly

\[
N(G)\ge k^m(1-1/k)^{(3/2)(m-1)(k-1)}
\ge k^m e^{-(3/2)(m-1)}.
\]

The coarse inequality follows from `(k-1)log(1-1/k)>=-1`. Extra ambient edges have zero coordinates in the selected mixture and cause no problem. For a `k`-regular graph with all odd cuts of size at least `k`, the uniform vector satisfies the full matching-polytope constraints, so exactly the same substitution applies without an edge partition. The formula involving `1/k` is asserted for `k>=2`; at `k=1` the graph itself is a matching. Empty graphs are handled separately.

After zero/fixed-coordinate deletion, residual components have even order and their matching laws form a Cartesian product. Conditional subadditivity gives the entropy upper bound by the sum of component maxima; independent maximizing component laws attain it. Hence `D` is additive across components and the componentwise rooted consequence is valid.

Finally, the six-vertex suggestion is correctly conditional. If a rooted `c3` theorem were established there, the two-/four-vertex `c3` bases plus the same induction would handle all larger orders, since for `m>=4`, `(c3-1)m-c3>=3c3-4>0`; indeed `3c3-4=log(256/243)/(2log(3/2))`. No six-vertex `c3` proof or optimality claim follows from the present argument. The old source examples give the unrooted universal lower limit `c3`; the rooted lower bound already occurs at `K4`.

## 6. Adversarial challenges: disposition

- **Unpaid positive separator:** resolved by exact identity (R2-A), for labelled crossing edges and arbitrary compatible maximizing child laws. The unrooted separator term in I22 remains positive; it is paid, not discarded.
- **Root reserve exhausted after several splits:** resolved by propagation of the actual retained root and rooting the other child at its contraction vertex. The edgewise identity holds again when a root was itself contracted earlier.
- **Circular leaf theorem or unjustified choice of a favorable leaf maximum:** resolved by strong induction on vertex count, uniform over all smaller graphs/means/roots. Child maxima are never assumed. A single positive parent global maximum is used.
- **General face rank still only proves coefficient two:** resolved only after positivity and induction exclude every nontrivial tight cut. Applying `d>=s-2m` before that point would be invalid; the candidate applies it afterward.
- **Boundary maximum or unbounded exponential parameters:** resolved by attained continuous `H`, zero/one reductions, and the finite exponential representation on the minimal face, not on the ambient matching set.
- **Deleted root, disconnected graph, or two-vertex parallel component:** resolved by Section 3.3 and the two-vertex base. No connectedness hypothesis is introduced.
- **Parallel collapse loses label entropy or root identity:** resolved by exact equal increments in `F,H`, complementary-entropy monotonicity, and classwise root incidence.
- **Stationarity fails in constrained directions; acceleration was silently ignored:** resolved by `im K=T`, stationarity for all exponential tilts, and `y'' in T`. No simultaneous diagonalization is used.
- **Six vertices at exactly `c=3/2`:** resolved by proving every strict coefficient first, then taking the pointwise endpoint limit. The endpoint trace alone does not suffice.
- **Klee transverse directions invalidate a face-local statement:** resolved by the exposing-slack mass bound and the `h_2(r)` entropy gain. This ancillary assertion is stronger than the tangent calculation and has been checked separately.
- **Finite Gibbs tests are mistaken for universal proof:** resolved by the all-order proof above. Numerical records support only their finite, explicitly specified instances.

**Unresolved mathematical objections to the stated rooted theorem: none found. Required repairs: none.** Open issues outside this verdict remain optimality of `3/2`, the conditional six-vertex `c3` improvement, computational prescribed-mean access, and independent significance/prior-art assessment.

## 7. Numerical audit, independent diagnostics, and primary comparison

I inspected the author's complete resumed diagnostic script, including exact enumeration, its rational logarithm tail estimate, outward rounding, Gibbs maximality requirement, and the distinction between high precision and interval certification. Its 75-law/564-root screen is finite. In particular, arbitrary rational laws would not suffice to evaluate `H`; the use of positive activity-product Gibbs laws at their own means is justified by the finite relative-entropy comparison. No optimizer flag, denominator floor, or finite grid supplies the universal theorem.

The independent [R2 diagnostic](../experiments/i25_rooted_entropy_proof_r2/diagnostics.py) imports no author code. It checks six asymmetric tight-cut Gibbs examples, including extra parallel labels and both shore orientations, with **44 root checks**. It compares entropy identities exactly as rational linear combinations of logarithms of primes, verifies the conditional-product law and every charged label, and checks a nonuniform parallel-collapse example with unequal class multiplicities. It also verifies forced/zero-coordinate reductions for all six roots of a boundary example and the empty residual case. On Klee graphs through twelve vertices, **42 root decompositions** test repeated root propagation, including already contracted roots, and the full rational matrix identity `K^2=(m/3)K`; 54 rational trace evaluations supplement the symbolic expression. Results are in [results.json](../experiments/i25_rooted_entropy_proof_r2/results.json). These are targeted finite diagnostics, not exhaustive graph coverage or a machine-checked universal proof.

I separately re-enumerated the suspect retained ten-vertex rooted law and evaluated it at **100 and 180 decimal digits**, summing absence probabilities directly. Interpreting the stored decimal parameters exactly, both computations agree to more than 75 decimal places in the ratio:

\[
(F-H)/W_v=1.001710029407370914571647773688833\ldots.
\]

This supports the candidate's withdrawal of the old `1.367744980429948` value. It is a precision-stability check of that stored law, not a rigorous interval certificate or a reconstruction of the optimizer's pre-serialization binary state. I did not rerun author scripts into their output directories while the parent was using them.

I read the fresh primary comparison passages, retained their version/PDF/text bytes, and checked live version pages. Gurvits's [Theorem 2.2, v11](https://arxiv.org/abs/1106.2844v11) is a weighted permanent lower comparison, giving the stronger coefficient-one prescribed-mean bound on bipartite graphs by entropy duality. It does not cover the new nonbipartite assertion. The rank/count/staircase passages of [Abdi–Cornuéjols–Dadush–Dalirrooyfard v2](https://arxiv.org/abs/2505.14497v2), revised 2026-04-20, concern regular graphs, minimum odd cuts, and the old cubic obstruction. They do not state the rooted arbitrary-mean invariant reviewed here.

[Singh–Vishnoi](https://arxiv.org/abs/1304.8108v1), Lemma 2.3 and Theorems 2.6–2.8, explicitly use an interiority promise and generalized weighted counting/marginal access. Those hypotheses explain why no prescribed-mean algorithm follows merely by invoking an unweighted FPRAS. [Dong–Jain's girth paper](https://arxiv.org/abs/2609.02017v1), Theorem 3.1, is a bipartite entropy **upper** comparison using conditioning and a good-vertex information-flow argument. Their [permanent approximation theorem](https://arxiv.org/abs/2609.11049v1) concerns weighted bipartite counts. Neither inspected interface substitutes for the rooted lower-bound proof.

A bounded fresh web query is preserved in [web-comparison.json](../sources/i25_rooted_entropy_proof_r2/web-comparison.json); irrelevant search hits were not used as premises. This is not an exhaustive novelty screen. The correct proof-level comparison is the combination of the root reserve, separator additivity, and positive-global-maximum induction with the inherited no-cut covariance argument. Whether that combination meets the substantial-contribution gate belongs to a separate review.

## 8. Reproduction and final disposition

From the project root, only the assigned R2 paths are written by:

```sh
PYTHONDONTWRITEBYTECODE=1 python frontier/experiments/i25_rooted_entropy_proof_r2/diagnostics.py
PYTHONDONTWRITEBYTECODE=1 python frontier/experiments/i25_rooted_entropy_proof_r2/verify.py --reproduce
```

The verifier checks the [R2 artifact seal](../sources/i25_rooted_entropy_proof_r2/artifact-seal.json), all frozen inputs, the author's existing 70-artifact seal, the 1,297-file preservation inventory, 18 pinned Git/SHA identities, 62 inherited statement contracts, ten inherited proof passages, seven inherited primary passages, 20 R2 read contracts, and 20 primary artifacts. It reproduces only the independent R2 diagnostics and requires byte-identical results. Its [verification output](../sources/i25_rooted_entropy_proof_r2/verification.json) separates shared-ledger, parent-verifier, and Git-index drift. The seal excludes only itself and the mutable R2 verification output; it has no circular digest dependency.

**Final disposition: full-statement proof PASS, with no required repairs.** The root reserve closes the actual all-graph induction, including labelled multiplicities, arbitrary feasible boundary means, all roots, and the endpoint coefficient. Sections 6 and 9 pass within their stated scope. Significance, project acceptance, and worldwide priority remain unassigned by this review.
