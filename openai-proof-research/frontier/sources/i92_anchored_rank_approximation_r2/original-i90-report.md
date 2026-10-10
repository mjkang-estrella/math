# I90 — anchored low-rank quantitative approximation

**Author-level outcome: Q88 is proved, with exponent one, by weighted statewise continuation.** Independently, **I88 Propositions A, A′ and B: ORIGINAL PASS WITHOUT REPAIRS**, at all their original stated scopes. The new argument is not a repair of those propositions. It replaces a support-counting step with a dimension-controlled variation envelope and, critically, moves badness from vertices to vertex–state pairs. A clipped local-type observable prevents the discrepancy error from being multiplied by rank.

For the actual parameters and inherited finite metric of I88, the result is

\[
\operatorname{rank}T+1>
 \frac{k}{4VH}\rho^{-n},\qquad
\operatorname{rank}T\ge \frac{k}{8VH}\rho^{-n}.
\tag{Q90}
\]

It holds already for \(p\ge1\), \(n\ge2\), \(\tau_m(n)\le1/(40V)\), \(\|T\|\le2p\), and anchor errors strictly below one, with domain \(X_m\) and codomain either \(X_m\) or the full block free space \(X\). Thus Q88 has the explicit choices \(c_p=k/(8VH)\), \(\alpha_p=1\), and \(n_p=2\), for its previously fixed choices of \(\Delta,k\). The subscript p includes those fixed source choices. There is no assertion uniform over unboundedly varying choices of these constants.

A second, quantitative compactness argument gives a finite-net obstruction and an explicit **linear**, not exponential, rank bound in depth. It uses the same statewise bridge, without a bidual limit or local reflexivity. The two routes are developed below and are not two findings.

The candidate is submitted for parent proof and contribution review, **not accepted or counted here**. The finite-dimensional envelope is classical Auerbach/ℓ1 sensitivity geometry. The proposed contribution is its correctly scoped use with weighted pair continuation and bounded local-type transfer on the actual graph sequence. Those modifications are elementary; their having closed Q88 does not by itself establish substantial status. A concrete reduction and the strongest inspected antecedents are given below so a technical disposition can be assessed without confusing it with a proof gap. Eight accepted findings remain the supplied project state.

## 1. Immutable brief, original audit, and scope

All statements and lower proof operations of `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are true premises for this task. The audit checks their applicability, not upstream truth. External literature is independently checked evidence. No apparent contradiction among sources is used. S88, finite binary D88, and I89 group discovery are not reopened.

The complete original I88 brief, its complete findings/report, and the finalized parent response are preserved without truncation as `original-i88-brief.txt`, `original-i88-report.md`, and `finalized-parent-response.json` in the owned I90 source directory. The first is the brief field of the finalized original task record; the latter two are byte copies of the finalized artifacts. These are part of this report's evidence, not summaries replacing the supplied material. The I88 seal SHA-256 is

`a4af4b269cef192734166e228ca2e95d6fd08ee25f03d4163a2fc4de0c9277c6`.

Its report hash is `32e04f5d5d6e26753018d627c57dc4013d75cb2eff24b3e989d0c5aa2af14d7a`. The offline I88 evidence replay is retained separately from this mathematical verdict. Original files were not edited.

AGENTS and the four named ledgers were read for rules, acceptance standard, current count, prior dispositions, and I88/I90 scope; complete frozen ledger bytes are retained. Historical material is not treated as a current count. Only those four informational inputs may drift. The supplied finalized I85/I86 and I87 status is used as scope information from the frozen ledgers; their files are not dependencies. No active I89 file, parent wrapper in progress, or mutable working artifact is bound.

### 1.1 Source contracts and the finite metric

Write F for `Failure-of-Bounded-Approximation-in-a-Lipschitz-Free-Space-over-a-Uniformly-Discrete-Metric-Space-September-26-2026`. Its complete proof sections `introduction.tex`, `reduction.tex`, `blocks.tex`, `operators.tex`, `walks.tex`, and `tests.tex`, and references, were read. All used theorem/lemma interfaces and their implementing lower operations were checked.

F fixes, before any operator,

\[
\begin{gathered}
L=10p,\ R=30p,\ K=10p(R+1),\ D=K+2L+5,\\
B=4R+D=300p^2+150p+5,\quad V=1+4pB,\\
\Delta\ge4\text{ even},\quad V/\Delta<1/20,\\
Q=\Delta^{2L+1},\quad H=\Delta^{D+1},\quad
k>2\Delta QH,\quad \rho=\Delta QH/k<1/2.
\end{gathered}\tag{1}
\]

The points of \(M_p\) are graph vertices and anchors, not edge interiors. All source graph edges have length one; source vertices attach to the anchor for their label by length R; distinct anchors have an edge of length \(2R+\|v-w\|_\infty\). Positive integer path lengths attain their infimum. Separation is at least one and diameter is at most B. The label map h is 1-Lipschitz for the **full shortest-path metric**. A source vertex x of color i has \(h_i(x)=0\), shares its label with \(a(x)\), and has \(d(x,a(x))=R\). Anchors include the basepoint o.

Every full closed radius-2L metric ball has at most Q points: a path that short cannot use an attachment or anchor edge since \(R>2L\); an anchor's such ball is a singleton. Every label has at most H coordinates below D. Loops have two distinct reversed incidences and parallel edges remain distinct. These facts persist on a subset with the inherited metric; in particular they hold for

\[
N_m=A_p\cup\bigcup_{j\le m}V(G_j),\quad
X_m=\mathcal F(N_m),\quad X=\mathcal F(M_p).
\]

The actual bump is \(b_x(t)=L(1-\|h(x)-h(t)\|_\infty/K)_+\); it takes values in [0,L], has Lipschitz constant at most L/K, and equals L at a(x).

No induced-subgraph shortest-path metric is substituted. Future source vertices could shorten long paths between anchors. Even when that happens, the inherited metric and the full-space label bound are precisely what the proofs use. For a real scalar C-Lipschitz function on N_m, the formula \(\inf_{z\in N_m}(f(z)+C d(z,t))\) extends it to M_p, preserving its restriction and constant. Consequently the inclusion \(X_m\to X\) is isometric. The increasing union is dense because it contains every evaluation. Neither T nor a vector-valued map is extended by that scalar argument.

F's `prop:coefficients` applies both to M_p and to N_m:

\[
\frac12\sum_{j\ne o}|c_j|\le
 \left\|\sum_{j\ne o}c_j\delta_j\right\|
 \le B\sum_{j\ne o}|c_j|.\tag{2}
\]

The sign/2 test proves injectivity and the lower bound; completeness gives closed range and density gives surjectivity from ℓ1. Thus arbitrary vectors of X have unique absolutely summable coordinates. This is a property of this bounded separated block, not of arbitrary free spaces or the unbounded wedge.

F's graph lemma gives local-type convergence at each fixed radius. There are finitely many possible induced rooted colored radius-n types for fixed \(\Delta,k,n\), so convergence of all their frequencies gives convergence in total variation. Here
\(\tau_m(n)=\sup_E|P_m(E)-P_{\rm tr}(E)|=\tfrac12\sum_t|P_m(t)-P_{\rm tr}(t)|\).
The source deterministic selection supplies no fixed numerical vertex-count schedule. Q90 conditions on the observable \(\tau_m(n)\), never on an invented schedule or a relabeled subsequence.

### 1.2 Proposition A — ORIGINAL PASS WITHOUT REPAIRS

The original quantifiers are p≥1, n≥2, m≥1 with \(\tau_m(n)\le1/(40V)\), a bounded real linear T on X_m of norm ≤2p and anchor errors <1, and a common finite coordinate support S containing o. The codomain enlargement to X with any finite \(S\subset M_p\) also passes. No endomorphism-specific step was used in that proof.

The augmented signed measure in original equation (4) has mass one, including its explicitly assigned basepoint coefficient. The sign test takes values in [-1,1] on S and zero elsewhere, hence is 2-Lipschitz by separation. Subtracting its value at o leaves the same Lipschitz constant. This gives TV≤1+2∥Tδ_x∥≤V. The anchor comparison uses vectors \(\delta_x,\delta_{a(x)}\) in the domain, ∥T∥≤2p, distance R, and bump slope L/K. Its loss is at most \(L(2pR+1)/K\le L/5\), so the weaker original lower bound 3L/4 holds.

The rare event in (6) uses only source colors along walks and the fixed state relation on S. Full labels of source vertices need not be radius-n determined: only their necessary own-color condition is used. On a tree a nonbacktracking n-walk visits n+1 distinct vertices. At most \(\Delta^n |S|Q^n\) walk/state pairs each have probability at most \((H/k)^{n+1}\). For the realized operator and support, the resulting union of types is a fixed subset of the finite type space. The deterministic TV inequality is uniform over every such subset, including one selected after G_m. No probabilistic independence from the selected operator is asserted.

At a good root, all positive continuation records are <n. A strict maximum yields at most one exceptional incidence per state; ties yield none. The two prepend inequalities use the appropriate **other outgoing incidences**, so loops and parallel edges do not require distinct vertices. When the competing continuation is zero, the edge itself supplies length one. Both inequalities cannot hold if both prescribed directions are nonexceptional. The edge test follows: for a cross pair closer than 2L, positivity of either bump makes both endpoint–state pairs compatible and triggers this alternative; otherwise both values vanish. Within sets, and for farther cross pairs, the Lipschitz bound is direct. Empty prescription data simply admit the zero extension, as explicitly provided by F's invoked `lem:edge-test`; the abbreviated extension formula in I88 does not change this existence claim.

The signed errors are controlled by variation, not by positive mass. Reversal preserves the uniform incidence distribution, including both loop orientations. If the claimed support lower bound failed, (6) gives \(\beta\le1/(20V)\). Then the right-hand side of (8) is strictly greater than \(11L/10=11p>2p\). The strict degree inequality provides the strictness even at equality in the support or discrepancy bounds. This proves the original claim, with no new assumption or repaired argument.

### 1.3 Proposition A′ — ORIGINAL PASS WITHOUT REPAIRS

The statement covers every N≥1, any N distinct nonbasepoint coordinates of the infinite block, any norm-one functional φ on X, and every bounded U whose range uses at most s nonbasepoint coordinates, \(0\le s\le N\). Equation (2) makes \(v_N=(BN)^{-1}\sum\delta_{x_i}\) nonzero and of norm ≤1. Thus \(\phi\otimes v_N\) has rank exactly one and norm ≤1. Outside U's support at least N−s unchanged coefficients are \(\phi(u)/(BN)\). Applying (2) to their absolute contribution and taking the supremum over the unit ball gives precisely \((N-s)/(2BN)\). Norm attainment is unnecessary. The threshold η<1/(4B) forces more than N/2 coordinates. This rules out universal support sparsification for arbitrary rank-one maps on this very X, but says nothing adverse about anchored Q88.

### 1.4 Proposition B — ORIGINAL PASS WITHOUT REPAIRS

The full scope p≥2, 1≤λ<p, 0≤ε<1/2, every integer r≥0, and codomain X passes. Its negation yields an increasing cofinal sequence of domain indices. Auerbach bases in ranges of dimensions ≤r give finitely many factors with ∥v_li∥≤1 and ∥φ_li∥≤λ. Zero padding is harmless. Hahn–Banach extends the functionals, not the operators. Banach–Alaoglu for the finite product of balls in X* and X** yields a subnet; it need not be a sequence. Cofinality of a subnet preserves eventual containment of each fixed X_j.

At each fixed vector of the dense union, scalar coefficients and scalar evaluations of the vector factors both converge, so their finite products and sums converge. Norm lower semicontinuity gives the operator norm and the anchor error bounds in X**. Rank of the displayed finite sum is at most r. No weak compactness or reflexivity of X is used; this block is ℓ1-isomorphic and is not reflexive.

The finite-dimensional local-reflexivity domain contains both the range and **all anchor evaluations**. Theorem 2.4 of the retained primary Goucher–Kania paper gives a linear map into the canonical X, fixes its intersection with X, and has norm at most 1+η. This is exactly the version needed; no preservation of extra pairings is required. The strict λ<p and ε<1/2 permit the two displayed budgets simultaneously, including ε=0. Composition is finite-rank and contradicts F's pinned fixed-anchor obstruction at norm p and error <1/2. The rank-zero case is the same forbidden zero map. Identity maps certify finiteness of least endomorphism rank because λ≥1. No effective m_0 is hidden in this proof, and no endpoint λ=p was claimed.

## 2. The weighted continuation theorem

The following is the analytic bridge. It is stated independently of linear operators so the role of each hypothesis can be checked.

**Lemma W (weighted statewise obstruction).** Use F's data (1), one actual source graph G_m, and n≥2. Let S be either a finite subset of M_p or any countable subset, with its actual restricted metric and labels. At every source vertex x suppose an absolutely summable real signed measure μ_x on S satisfies

\[
\|\mu_x\|_{\rm TV}\le V,\qquad
\int b_x\,d\mu_x\ge3L/4,\qquad
\left|\int f\,d(\mu_x-\mu_y)\right|\le\lambda
\tag{3}
\]

for every oriented source edge x→y and every 1-Lipschitz \(f:M_p\to[-L,L]\). Suppose a finite positive measure ν on S dominates each variation measure: \(|\mu_x|\le\nu\). Put \(a_n=(H/k)\rho^n\). Then

\[
\boxed{\quad
\nu(S)a_n+V\tau_m(n)
\ \ge\ \frac38-\frac{\lambda}{4L}-\frac V\Delta.
\quad}\tag{4}
\]

No positivity, stochastic transition kernel, or nonnegative factorization of μ is assumed.

**Proof.** Use exactly F's compatibility condition \(\|h(x)-h(j)\|_\infty\le D-4\) and state transitions \(d(j,j')\le2L\). Mark **(x,j)** bad when an n-step matched nonbacktracking walk starts at x with initial state j. If (x,j) is good, take the largest positive matched length beginning through each incidence, or zero. These records lie in {0,…,n−1}. Declare only a strict maximum exceptional. If (x,j) is bad, declare every incidence exceptional at that pair. This differs from declaring every state at a bad vertex exceptional.

For e:x→y and compatible j,j′ with an allowed transition, if either pair is bad the corresponding direction is exceptional. If both pairs are good, the source prepend proof applies word for word to these two pairs: maxima A_x,A_y over competing directions give
\(r_x(e,j)\ge1+A_y\) and \(r_y(\bar e,j')\ge1+A_x\). Prepending a walk that reaches length n would itself make its starting pair bad; thus in the good case these genuinely are finite records. If neither direction were exceptional, \(A_x\ge1+A_y\ge2+A_x\), impossible. It is irrelevant whether other states at x or y are bad. This proves the endpoint alternative at the required finer scope.

For the resulting E_e, prescribe b_x on S\E_e and −b_y on S\E_reverse. The same bump/label argument as in §1.2 gives consistent 1-Lipschitz data. For countable data the infimum extension replaces the finite minimum. It is finite because values lie in [-L,L] and M_p is bounded; it agrees on the data, is 1-Lipschitz by the triangle inequality, and remains so after clipping. Empty data use zero. Thus there is an admissible f_e. Absolute summability makes all its integrals well defined. Consequently

\[
\lambda\ge3L/2-2L\bigl(|\mu_x|(E_e)+|\mu_y|(E_{\bar e})\bigr).\tag{5}
\]

Let \(B_x\subset S\) be the bad states and \(w(x)=|\mu_x|(B_x)\). At each good pair a state contributes to at most one direction, and at each bad pair to all directions. Hence, in fact,

\[
\frac1\Delta\sum_{e\in\mathcal D(x)}|\mu_x|(E_e)
\le \frac{\|\mu_x\|_{\rm TV}}\Delta
 +(1-1/\Delta)w(x)
\le V/\Delta+w(x).\tag{6}
\]

Reversal and averaging in (5) imply

\[
\mathbb E_{x\in G_m}w(x)
\ge\frac38-\frac{\lambda}{4L}-\frac V\Delta.\tag{7}
\]

For each fixed state j define F_j(t), taking values zero or one on the finite space of radius-n colored source types, as follows. It records whether that rooted type has a nonbacktracking length-n source walk and a length-n state walk in S starting at j whose successive source colors lie in \(C_{j_s}=\{i:h_i(j_s)<D\}\). Full source-label compatibility is discarded here, so \(1_{j\in B_x}\le F_j(t_x)\). The state graph, its metric, and all the sets C_j are fixed, even when selected from the realized G_m and T. The source type is the only variable in F_j. At a fixed j there are at most Q^n state sequences and Δ^n source walks on a regular tree. Color independence along each tree walk gives

\[
\mathbb E_{\rm tr}F_j\le\Delta^nQ^n(H/k)^{n+1}=a_n.\tag{8}
\]

This retains the **actual metric degree Q**, including self-transitions, and the **actual low-color bound H**. We do not quotient labels or invent adjacency of basis indices or net points. For countable S each length-n state neighborhood is finite by Q, so F_j is still a well-defined type event.

Now set

\[
g(t)=\min\left\{V,\sum_{j\in S}\nu(j)F_j(t)\right\}.
\tag{9}
\]

Domination gives \(w(x)\le\sum_j\nu(j)F_j(t_x)\), and TV gives w(x)≤V, so w(x)≤g(t_x). The deterministic total variation inequality for any function taking values in [0,V] gives

\[
\mathbb E_m w\le\mathbb E_m g
\le\mathbb E_{\rm tr}g+V\tau_m(n)
\le\sum_j\nu(j)\mathbb E_{\rm tr}F_j+V\tau_m(n)
\le\nu(S)a_n+V\tau_m(n).\tag{10}
\]

The bounded-function TV inequality follows either by level sets or by separating positive and negative coordinates of P_m−P_tr. Nonnegative summation justifies interchange for countable S. Since it holds for every bounded function on the type space, it also holds for this operator-selected g; no independence is needed. Combine (7) and (10). ∎

**Why the clipping is essential to this estimate.** Summing the separate bounds \(P_m(F_j)\le a_n+\tau_m(n)\) would give \(\nu(S)(a_n+\tau_m(n))\). With \(\nu(S)=O(rV)\), fixed discrepancy would then allow only a constant lower bound for rank. Clipping before transfer costs Vτ, with no dimension factor. This is a stronger argument, not a suppressed error term.

## 3. Approach I: a finite-dimensional envelope proves Q88

**Lemma E (classical finite-dimensional domination, with proof).** If E is a real d-dimensional subspace of ℓ1(S), then there is a positive ν_E on S of mass d such that

\[
|u(j)|\le\|u\|_1\nu_E(j)\qquad(u\in E,\ j\in S).\tag{11}
\]

For d=0 use zero. For d>0 choose an Auerbach basis u_1,…,u_d in the ℓ1 norm and set \(\nu_E(j)=\sum_i|u_i(j)|\). Each basis vector has norm one and each coordinate functional has norm one, so (11) follows by expansion and the triangle inequality, and ν_E(S)=d. Existence of that basis is elementary even for a subspace of infinite ℓ1: identify E with \(\mathbb R^d\), maximize the absolute determinant of d vectors in its compact unit ball, and use a maximizing independent tuple. Every vector of that tuple has norm one, since otherwise scaling it up would increase the determinant. Replacing its ith column by any unit vector shows that the ith coordinate functional has norm ≤1. The dual pairing with its own unit vector gives equality. No compactness of the ambient ℓ1 unit ball is used. ∎

**Theorem Q90.** Fix p≥1, the entire F construction, m≥1 and n≥2. Let \(T:X_m\to X\) be bounded real linear, of rank r, with \(\|T\|\le2p\) and \(\max_{a\in A_p}\|T\delta_a-\delta_a\|<1\). If \(\tau_m(n)\le1/(40V)\), then (Q90) holds. The endomorphism version follows by isometric inclusion.

**Proof.** By (2), write Tδ_x in its unique ℓ1 coordinates and augment at o:

\[
\mu_x(j)=c_x(j)\ (j\ne o),\qquad
\mu_x(o)=1-\sum_{j\ne o}c_x(j).
\tag{12}
\]

This works on all M_p, with absolutely convergent sums; one can take S=M_p. Finite codomain uses S=N_m. For every Lipschitz g,
\(\int g\,d\mu_x=(T\delta_x)(g-g(o))+g(o)\).
The sign test remains 2-Lipschitz on the countable separated block, including infinitely many nonzero coordinates. Absolute convergence therefore gives TV≤V. The anchored bump calculation in §1.2 yields \(\int b_x d\mu_x\ge3L/4\), and the edge pairing is bounded by \(\lambda=2p\). Thus (3) holds.

Let C:X→ℓ1(M_p\{o}) be the bounded inverse coefficient map. Define \(J_0c\) to equal c away from o and \(-\sum c\) at o. This is bounded into ℓ1(M_p) and linear. Then every μ_x belongs to

\[
E=\operatorname{span}\{\delta_o\}+J_0 C(TX_m),\qquad d=\dim E\le r+1.
\tag{13}
\]

Here \(\delta_o\) in ℓ1 denotes unit mass, whereas in the free space it is zero; the notation is explicitly distinguished. By Lemma E, ν=Vν_E dominates all |μ_x| and has mass Vd≤V(r+1). Apply (4):

\[
V(r+1)(H/k)\rho^n
\ge\frac38-\frac{2p}{4L}-\frac V\Delta-V\tau_m(n)
>\frac38-\frac1{20}-\frac1{20}-\frac1{40}=\frac14.
\tag{14}
\]

This proves the first inequality of Q90. Put \(A_n=k\rho^{-n}/(4VH)\). From k>2ΔQH and Δ>20V, \(A_n>\Delta Q/(2V)>10Q\ge10\), hence \(A_n-1\ge A_n/2\). Since r>A_n−1, the asserted weaker bound r≥A_n/2 follows. In Q88, p≥2, norm≤p/2 and error≤1/4 satisfy the stronger theorem's hypotheses. ∎

**All complexities remain distinct.** r is ordinary real linear rank. d is the dimension of the augmented **signed-measure** subspace in TV norm, at most r+1. ν is a positive **dominating measure**, not a finite-support replacement and not a distribution of operator outputs. Its mass is at most Vd, but its support can be arbitrarily large or countably infinite. No nonnegative-rank bound, positive decomposition of T, or transport kernel is asserted. The coefficient bound (2) is used to place range vectors in ℓ1 and to justify their representation; its upper factor B is not confused with r. Lemma E is entirely compatible with A′: a diffuse unit vector in a one-dimensional subspace has an envelope of mass one, however large its support.

**Quantitative variant.** Without the discrepancy threshold, the argument proves

\[
(r+1)V(H/k)\rho^n\ge
\frac38-\frac{\lambda}{4L}-\frac V\Delta-V\tau_m(n),\tag{15}
\]

whenever the same TV and bump hypotheses follow from the operator. In particular one may retain \(\lambda=\|T\|\) rather than 2p. A positive right side is the exact applicability condition of this displayed version. There is no error-dependent inverse modulus hidden in it.

## 4. Approach II: quantitative compactness without a bidual limit

We first tried to quantify I88 B directly. An Auerbach factorization controls finitely many factors in norm, but does not supply a numerical bound for when a weak-star subnet meets a prescribed collection of tests. Local reflexivity controls distortion on a chosen finite-dimensional space; it supplies neither a graph radius for that choice nor local-type information about its vectors. Quantifying the theorem's norm distortion alone therefore leaves precisely the missing link. This is a failure of that route to an effective rate, not a counterexample to Q88 or to local reflexivity.

A genuine replacement is possible using finite TV covers of the output measures and Lemma W's pair records. It keeps every center as a measure on the **original** metric state space.

**Lemma C (finite-cover obstruction).** Assume the measures in (3). Suppose there are M signed measures \(\sigma_1,\dots,\sigma_M\) on S with \(\|\sigma_i\|_{\rm TV}\le W\), such that every μ_x is within η in TV of one of them. Then

\[
\eta+MW(H/k)\rho^n+V\tau_m(n)
\ge\frac38-\frac\lambda{4L}-\frac V\Delta.
\tag{16}
\]

**Proof.** Define bad pairs and w as before. For the center chosen for x,
\(w(x)\le |\sigma_i|(B_x)+\eta\le\sum_i|\sigma_i|(B_x)+\eta\).
Set \(\nu=\sum_i|\sigma_i|\); its mass is at most MW. Thus
\(w(x)\le\min(V,\eta+\sum_j\nu(j)F_j(t_x))\).
Apply bounded TV transfer and (8) to this function. The tree expectation is at most η+MWa_n. Combine with (7). This pays the conversion from a finite list of diffuse measures to a weighted estimate; the list is never declared to be a set of coordinate states. ∎

For an actual rank-r T, the μ_x belong to the radius-V ball of the d≤r+1 dimensional E of (13). A maximal η-separated set of that ball has at most \((1+2V/\eta)^d\) points and is an η-net. Indeed, its disjoint open η/2 balls lie inside the radius V+η/2 ball; d-dimensional Lebesgue volume scales as radius^d. The volume bound also proves finiteness, allowing a maximal set; closed-ball boundary equalities do not affect volumes. All centers lie in E and have TV≤V. This argument uses compactness only in a specified finite-dimensional normed ball, with a proved explicit bound.

Taking η=1/16, W=V and the same bounds as Q90 gives

\[
M>\frac{3k}{16VH}\rho^{-n},\qquad
r+1>
\frac{n\log(1/\rho)+\log(3k/(16VH))}{\log(1+32V)}.
\tag{17}
\]

This is an explicit **linear-in-n** rank obstruction. It is weaker than Approach I, not an alternative proof of the exponential conclusion. It shows exactly what a quantitative finite-dimensional compactness replacement buys, including its dependence on τ through (16). Without the weighted pair/TV conversion, an elementary covering lemma alone gives no such conclusion on these graphs. Conversely, that conversion is shared by both routes, so (17) is a supporting consequence, not a separate substantial candidate.

As a robust variant, if each μ_x has TV distance ≤ζ to a d-dimensional E, choose near points of norm ≤V+ζ (or V+ζ+ε and let ε decrease). Cover that ball at radius η. The same proof yields
\[
\zeta+\eta+(V+\zeta)(1+2(V+\zeta)/\eta)^d a_n+V\tau_m(n)
\ge\frac38-\frac\lambda{4L}-\frac V\Delta.
\tag{18}
\]
For a finite family the best-approximation points exist, since E is finite-dimensional; this also justifies taking ζ equal to the maximum distance. No linear selection, positivity, or local reflexivity is required. The finite-net count controls an approximation dimension, not nonnegative rank.

## 5. Failed conversions, exact limitations, and contribution comparison

1. **Raw support counting:** F's finite-support perturbation has no support-cardinality bound in r. I88 A′ refutes such a bound for arbitrary operators. The new proof does not provide it even for anchored operators; it bypasses it.
2. **Unclipped weighting:** summing individual TV discrepancy errors incurs ν(S)τ rather than Vτ. At fixed τ this spoils exponential rank growth. The cap in (9) is necessary for our retained error budget.
3. **Whole-root badness:** a root can be bad because of a state carrying no μ_x mass. A small common envelope does not control that root indicator through its mass. This is why pairwise records had to be proved, not just inserted into the original β estimate.
4. **Label quotienting:** two states sharing a label need not be close; all anchor copies of one source label can occur in many remote metric locations. Merging states can turn an arbitrary number of distant successor sets into neighbors of a single quotient state. Neither Q nor a probability product survives automatically. Our state graph never changes.
5. **Finite nets as support or probability kernels:** M diffuse signed centers may have unbounded common support. Taking absolute values is used only for an upper envelope. It neither preserves the anchor pairings nor defines a linear positive approximant. Lemma C proves the weaker legitimate conversion and its linear rate.
6. **Quantitative local reflexivity alone:** its distortion parameter has no observable-depth content. A qualitative subnet, any arbitrary block reindexing, and an inverse modulus without effective dependence are not used in Q90.

The actual metric blocks, local colored-tree construction, bumps, scalar extension, and incidence reversal all remain F's work. Even the prepend inequalities are inherited lower operations. The new complete deduction is the following precise three-step refinement: (i) continuation and error accounting for individual pairs, (ii) a rank-controlled classical ℓ1 envelope, and (iii) clipping the weighted event before transferring empirical type distributions. It yields a rank bound where F and I88 A retain support cardinality. An asserted exponential bound obtained merely by substituting an exponential net size into A would instead be linear in rank versus depth; (17) makes that loss explicit.

The full-domain searches identify no other manuscript using the same matched-walk/exceptional-direction free-space mechanism. This is bounded evidence, not a semantic-exhaustion or worldwide-priority claim. The strongest relevant source comparisons actually read were:

- **F's abstract obstruction and full implementation:** `rem:abstract-obstruction` already abstracts all metric/label hypotheses and its proof gives qualitative impossibility. It does not give dimension-controlled envelopes or the clipped weighted-pair estimate. Q90 uses that same geometry and strengthens its finite quantitative output; it does not construct a new space.
- **Cotype–cotype companion:** complete coefficient, Walsh-growth/decay, and compact-domain operations were read. Its finite-rank Hilbert factorization has an operator-dependent constant; its uniform decay assumes primal/dual cotype at the specified moment lengths. X here is ℓ1-isomorphic and its dual is ℓ∞-isomorphic, so no uniform finite dual cotype applies. In finite X_m those constants may grow with dimension; one cannot invoke them with fixed data. Its finite nets retain moment lifts in larger subspaces, not metric states with degree Q. None supplies (4).
- **Metric-entropy duality counterexample:** the complete matrix-to-body and positive/signed compression operations were read. They approximate logarithmic distance profiles through partition labels and group positive coefficient mass into pivot slots, then handle signed coefficients by two positive parts. The profile and partition hypotheses are absent here, and label replacement does not retain our metric successor bound. This is a real signed compression operation, but not a support sparsification or rank theorem for these anchored maps. Its different use of the letter Q denotes list size, not F's metric degree.
- **Nuclear-norm ultrapower obstruction:** its complete nuclear-finiteness operation uses representation spectral gaps, reduced density operators, and min/max tensor norm equality; it imposes no representation-dimension bound. Nuclear C*-algebra approximations and ordinary Banach operator rank are distinct. This search hit contributes no bridge and is not used.

The classical component deserves explicit attribution. Dasgupta–Drineas–Harb–Kumar–Mahoney, *Sampling algorithms and coresets for ℓp regression*, SIAM J. Comput. 38 (2009), §3.1, explains Auerbach conditioning and bounded coordinates; §3.2 uses row weights for norm-preserving sampling. The exact p=1 envelope calculation in Lemma E is that standard geometry, with a self-contained proof here. Their sampling does not claim approximation of a diffuse vector by coordinate truncation in its original ℓ1 norm, so it does not contradict A′. [Author-hosted primary PDF](https://www.cs.purdue.edu/homes/pdrineas/documents/publications/Drineas_SICOMP_09.pdf).

Woodruff–Yasuda, *New Subset Selection Algorithms for Low Rank Approximation: Offline and Online*, retained arXiv:2304.09217v1 (18 April 2023), introduction, and the scoped §8 sensitivity statements, further develops spanning-set conditioning and sensitivity sampling for matrix losses. The inspected operations concern approximation costs and reweighted samples. They do not assert that original metric adjacency or individual signed-measure integrals survive coordinate sampling. No such transfer is imported. [Primary version record](https://arxiv.org/abs/2304.09217).

Naor's *Impossibility of almost extension*, Proposition 6, Remark 7, and complete proof, explicitly uses signed measures to encode almost extensions, and distinguishes convex-hull-valued extensions via probability measures. This confirms the relevant signed-versus-positive distinction; it supplies neither a rank hypothesis nor the matched-state inequality. [Author-hosted primary PDF](https://web.math.princeton.edu/~naor/homepage%20files/almost-ext.pdf).

Ben-David–Childs–Gilyén–Kretschmer–Podder–Wang's graph paper §6.1.2 uses nonbacktracking continuation lengths to infer parent consistency. In the retained arXiv v1 these are Algorithm 1 and Lemma 58, not the final publication's Algorithm 6.1 and Lemma 6.3 cited by F. The actual algorithm and complete consistency proof were read. They ignore specified loops/double edges during that test and have no signed state family or rank envelope. F already supplies the required incidence adaptation; we claim no new parent-direction principle. [Primary version record](https://arxiv.org/abs/2006.12760).

Godefroy–Ozawa's *Free Banach spaces and the approximation properties*, Proposition 7 and proof, obtains finite pairs requiring large exact extension norms through a compact AP obstruction and a diagonal limit. By duality the range is prescribed. It does not give rank complexity for arbitrary ranges on a specified graph sequence. [Primary v2 PDF](https://arxiv.org/pdf/1201.0847v2). Goucher–Kania Theorem 2.4 is the exact external input to original B, as audited, and is not needed in Q90.

**Contribution boundary.** The proof resolves Q88 as formulated, on its intrinsic observable depth. It is more than the old support estimate or elementary-net extraction because (4) retains weighted state variation and a rank-independent discrepancy error, and Lemma E costs only d, not exp(d). However all ambient geometry and most edge mechanics are stipulated source operations, and the added argument is short and elementary. The record does not certify that this meets the project's unusually strict substantial-contribution threshold. Parent alone decides whether this finite quantitative strengthening merits independent significance review or technical closure. No new-to-literature or ninth-finding claim is made here.

The result has no claimed optimal exponent, no numerical graph-size schedule, no general theorem for arbitrary locally tree-like metrics, no unbounded-wedge rate, and no new AP/BAP equivalence. It uses fixed p with astronomically large fixed Δ,k,H,Q; being explicit does not make the constants practical. Identity operators on X_m ensure that the hypotheses are nonvacuously satisfiable at every stage under Q88's norm allowance; when τ is small the theorem simply forces their competitors to have large rank. It does not bound rank above or approximate those identities constructively.

## 6. Evidence, stress tests, preseal record, and handoff

`search.py` scanned all **10,373 original blob positions**, through the frozen I88 augmentation of the immutable I79 map, with original bytes and PDF text reused in place. The complete tree has 13,223 entries and 749 manuscripts. The I14 inventory was enumerated using `rg --files --no-ignore` (9,340 bodies); I79 supplies the remaining 1,033 original bodies and 776 PDF extractions. No recursive corpus copy or re-download was made. Three exact ordered search multisets have 84 rank records across 33 manuscripts, 554 state records across 139, and 8 entropy records across 5. Search-result duplication by source/PDF is retained. Search hits in unrelated algebra, statistical mechanics, and group theory are screens, not claims of reading their complete proofs or a second research lane. `read-manifest.json` records actual complete operations and bounded comparison passages, with hashes and line ranges. PDFs representing the F family were inspected at the operative sections and bound to the complete source inventory; no unseen PDF variant is silently equated with TeX.

External response bodies, retrieval headers, URLs, versions, hashes and extracted text are retained. Four bounded web-search responses include irrelevant and secondary hits; these are not mathematical premises. For every primary statement used or compared, the actual text, not the search snippet, was read. The verifier re-extracts new primary PDFs to stdout and checks byte identity of the saved text. It checks inherited corpus extraction hashes and maps rather than re-extracting all 776 corpus PDFs. This limit is deliberate and explicit.

The new exact diagnostic exhausts degree-four permutation multigraphs on up to three vertices, all two-state compatibility assignments, both reflexive symmetric two-state relations, and cutoffs 2,3,4. It tests **pairwise** badness, the endpoint alternative, and signed exceptional-variation averaging; it records cases where rootwise and pairwise badness differ. Further exact checks cover bounded-observable TV transfer, all colors on small degree-two tree balls with fixed state walks, the rational parameter budgets, and diffuse one-dimensional envelopes. They neither instantiate the enormous full F graphs nor certify the analytic theorem. The proofs above supply the universal claims.

`preseal-corrections.md` retains failed paths and corrections, including guessed nonexistent source filenames, truncated displays repaired by targeted reads, the initially inadequate ν(S)τ error, the rejected whole-root weighting, the net-rate loss, and the graph-paper version-label difference. These were preseal developments of I90; none is a repair to I88.

Run, from the repository root:

```
python3 -B frontier/experiments/i90_anchored_rank_approximation/verify.py
```

The single `seal.json` binds the exact owned domain (this report plus the two owned directories, excluding only the seal itself). Its SHA-256 is supplied in the final handoff. The verifier is **offline and read-only**: no fetch, repair, rewrite or reseal, and Python bytecode generation is disabled for subprocesses. It checks owned bytes, frozen inputs, immutable references, I88's unchanged seal and domain, all original Git blob identities and search-body hashes, the complete tree/I79 mapping, exact search outputs, primary PDF re-extractions and finite diagnostics. Evidence PASS explicitly does **not** mean independent proof PASS for Q90 or substantial acceptance. The independent original-proof verdict for I88 A/A′/B is the written analysis in §1, not the verifier's hash output.

**Parent handoff:** preserve I88 original PASS at the audited scopes. Q88 has the complete author proof (Q90), plus the weaker quantitative compactness result (16)–(18); no open localization lemma remains in those proofs. Review the pairwise continuation, clipped adaptive type observable, and signed-measure dimension conversion first. Contribution remains for parent disposition. No shared edit, child, staging, commit, publication, or count change was performed.
