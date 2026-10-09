# R011 — A rooted entropy bound for perfect matchings

**Accepted 2026-10-09 as the fifth substantial finding.** This is one deduction under the stipulated truth of `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. The [complete proof](../iterations/i25-matching-entropy-improvement-resumed.md) passes [independent full-proof review](../reviews/i25-rooted-entropy-proof-r2.md) without repairs. The [separate significance review](../reviews/i25-rooted-entropy-novelty-r3.md) judges the combined mechanism substantial. Parent reproduction and evidence checks pass. Worldwide priority, human peer review and formal proof certification are not established.

## Exact theorem

Let G=(V,E) be any finite undirected loopless multigraph with |V|=2m≥2 and at least one perfect matching. Parallel edges are distinguished labels. For every x in the convex hull P(G) of perfect-matching incidence vectors, define, using natural logarithms and 0 log 0=0,

\[
H_G(x)=\max_{\mathbb E\mathbf1_M=x}\operatorname{Ent}(M),\qquad
F(x)=-\sum_e x_e\log x_e,\qquad
B(x)=-\sum_e(1-x_e)\log(1-x_e).
\]

For each vertex v let

\[
b_v(x)=-\sum_{e\ni v}(1-x_e)\log(1-x_e),\qquad W_v=B-b_v.
\]

Then, **for every feasible mean x and every vertex v**,

\[
\boxed{F(x)-H_G(x)\le\tfrac32 W_v(x).}
\]

All boundary means, zero or forced coordinates, disconnected graphs and finite parallel multiplicities are included. The empty graph has F=B=H=0 separately, with no rooted assertion. A graph without perfect matchings has no feasible mean. H is the maximum entropy at the specified mean; replacing it by the entropy of an arbitrary matching law is false.

Since the sum of b_v over vertices is 2B, the theorem implies

\[
H_G(x)\ge F(x)-\tfrac32(B(x)-\max_v b_v(x))
\ge F(x)-\tfrac32(1-1/m)B(x).
\]

The pinned source gives coefficient 2(1−1/m). Thus the finite-order coefficient is reduced by 25% for every m>1. The statement is not a degree-bounded or fixed-order extension.

## Proof and source dependencies

The full written proof and its independent reconstruction are linked above. The argument uses the accepted manuscript *Entropy and Face Dimension of the Perfect-Matching Polytope*: `geom:thm-polytope`, `geom:lem-face`, `geom:lem-gluing`, `geom:lem-reduction`, `ent:continuity`, `ent:exponential` and the covariance calculation `ent:second-variation`. [Exact pinned contracts and read passages](../sources/i25_matching_entropy_improvement_resumed/source-contracts.json) specify the original files and statements.

Write D=F−H. A tight nontrivial odd cut has crossing distribution q of total mass one. Contract each shore, retaining crossing labels in both children. Every parent matching used by a law of mean x crosses once. Conditional independence of maximizing child laws given the crossing label yields

\[
H=H_1+H_2-h(q),\quad F=F_1+F_2-h(q),\quad
B=B_1+B_2-b(q),\quad D=D_1+D_2.
\]

Retain the designated root v in child 1 and root child 2 at its contracted vertex z. Its root star is the cut, so b_z=b(q), and the parent root star is unchanged in child 1. Consequently

\[
W_v=W_{1,v}+W_{2,z},\qquad
(D-cW_v)=(D_1-cW_{1,v})+(D_2-cW_{2,z}).
\]

This exact identity pays the positive separator term that would remain for the unrooted potential D−cB. It remains valid when an inherited root was created by an earlier contraction.

Fix c=3/2+ε, ε>0, and induct on m, simultaneously over all graphs, means and roots. The two-vertex case is D=W=0. On four vertices collapse parallel classes: the same label-entropy term is added to F and H, while W can only increase. In the resulting simple graph the three possible matching types have probabilities p; D=h(p) and W_v=b(p). The scalar ternary inequality h(p)≤3b(p)/2 supplies the base. Its complete elementary calculus proof is in the reviewed report, including boundary probabilities.

Suppose the continuous function E=F−cW_v−H has a positive global maximum on P(G). Compactness and the source's continuity theorem give attainment. Delete zero edges, preserving the maximum. A value-one edge reduces to smaller order: if it removes the root, its original b_v is zero, and any residual root gives D≤c(B−b_w)≤cB. An empty residual graph has zero defect. Thus every remaining coordinate is strictly fractional.

A nontrivial tight odd cut would give two smaller rooted instances whose defects sum to E, contradicting positivity. At the positive maximum there are therefore no such cuts. Only degree equations constrain the minimal-face tangent space, giving d≥s−2m, where s is the retained edge count.

Use the maximizing exponential law on that face and its covariance K. Its range is the tangent space. For J=F−cW_v the diagonal Hessian is

\[
A_{ee}=-1/x_e+c\,\mathbf1_{e\not\ni v}/(1-x_e).
\]

Stationarity along finite exponential tilts cancels their acceleration term; the second derivative test gives (Ka)ᵀA(Ka)+aᵀKa≤0. Summing on positive covariance eigenvectors after division by their eigenvalues gives

\[
0\ge d+\operatorname{tr}(KA)=d-s+m+c(m-1).
\]

Here K_ee=x_e(1−x_e), the total edge mean is m, and the mean outside the root star is m−1. Combining with the no-cut dimension bound gives

\[
0\ge(c-1)m-c=(m-3)/2+\varepsilon(m-1)>0
\]

for m≥3. This contradiction closes the induction. For each fixed graph, mean and root, W_v is finite and nonnegative, so letting ε decrease to zero proves the endpoint coefficient 3/2. The strict-coefficient argument is needed at six vertices; the endpoint trace alone gives no contradiction there.

## Consequences and limits

For finite real edge log weights θ, define Z_θ as the sum of exp(θ·1_M) over perfect matchings and Q_θ=max_{x∈P(G)}(F(x)+θ·x). Since W_v≤m−1, Gibbs duality gives

\[
Q_\theta-\tfrac32(m-1)\le\log Z_\theta\le Q_\theta.
\]

If G has k≥2 edge-disjoint perfect matchings, or is k-regular with every odd cut having at least k edges, the feasible uniform mean gives

\[
N(G)\ge k^m(1-1/k)^{\frac32(m-1)(k-1)}
\ge k^m e^{-\frac32(m-1)}.
\]

The source's corresponding coarse loss was 2(m−1). These are consequences of the same finding, not additional entries in the count. They do not claim to improve every specialized bipartite, dense-graph or expanding-graph counting theorem. No new efficient prescribed-mean sampler or optimizer follows without additional oracle hypotheses.

The optimal universal coefficient is still undetermined between the inherited obstruction log(3)/(2 log(3/2))≈1.35476 and 3/2. An old numerical value near 1.3677 was a rounding artifact and is not a lower-bound result.

## Significance and validation

The new contribution is the combination of the all-roots allowance, exact separator compensation and positive-global-maximum induction. Applying the rooted trace to the source's unrestricted face bound still gives threshold two; using the old unrooted objective still leaves an unpaid separator term. The source's no-cut bound becomes applicable only after the new induction excludes tight cuts. The source operations, scalar base and final counting substitutions are inherited ingredients.

The independent significance audit checks full source proofs and primary literature on nonbipartite Bethe corrections, prescribed-mean bipartite entropy, brick/cut rank formulas, common tight-face geometry, recent counting bounds and entropy/counting duality. It identifies a substantive bridge beyond those inspected interfaces. This supports the project's contribution standard; it does not certify exhaustive priority.

The parent read the complete candidate, both reviews and decisive source proofs. The author's diagnostics reproduce 75 rational-activity laws and 564 certified rooted inequalities, plus high-precision correction of 33 retained laws. R2 independently verifies labelled gluing, root propagation, parallel collapse, fixed-coordinate reductions and the covariance identities. R3 adds exact scope and reduction checks, including a counterexample to replacing maximum entropy by arbitrary-law entropy. All three evidence verifiers pass. These finite checks validate formulas and provenance; the universal statement rests on the written argument and stipulated source interfaces.

Verification records: [candidate](../experiments/i25-resumed-parent-verification.json), [full-proof review](../experiments/i25-proof-r2-parent-verification.json), [significance and acceptance](../experiments/i25-novelty-r3-parent-verification.json).

**Parent decision:** accept R011 as one fifth substantial deduction. The theorem, weighted bracket, counting consequences and ancillary obstruction analysis belong to this single finding. Historical candidate/review status text stays unchanged; this record and TEN-FINDINGS.md govern current acceptance. Research continues toward ten, with five remaining.
