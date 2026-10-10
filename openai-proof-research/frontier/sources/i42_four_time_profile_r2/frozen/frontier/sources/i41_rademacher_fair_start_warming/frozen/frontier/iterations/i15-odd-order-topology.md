# I15: a ternary marked chamber and an individually unrealizable outer element of order three

Research date: 2026-10-08 Pacific / 2026-10-09 UTC.

**Status: one proposed substantial construction, with a complete source-relative proof below, ready for the parent's separate fresh proof and novelty reviews. No independent PASS or contribution acceptance is claimed. Accepted findings remain R006, R008, R009; no R number is assigned.**

The proposed conclusion is a closed connected oriented aspherical topological **four-manifold** \(M\) and \(\alpha\in\operatorname{Out}(\pi_1M)\) of **exact order three** such that neither \(\alpha\) nor \(\alpha^{-1}\) is induced by **any** homeomorphism of \(M\). A hypothetical representing homeomorphism is allowed infinite order. The intermediate construction has an exact cyclic-cover spectrum: its degree-\(d\) cover has a closed four-manifold model if and only if \(3\mid d\).

The new local ingredient is a six-tip marked body with **three alternative terminal caps on each bottom branch**. Its law has leading tensor

\[
 [ [X_0,[X_1,X_2]], [Y_0,[Y_1,Y_2]] ]. \tag{1}
\]

Six forbidden endpoint-color pairs, implemented by ordinary pairwise plumbing, force the deficient color to advance by one in \(\mathbb Z/3\). The new body permits the corresponding three-way cap choice. In particular, the construction is not binary rank amplification. A majority-descent lemma below proves that finite arrangements of the old binary cap choices cannot have the required positive-three/negative-other-cover behavior by that cap-selection method.

The six-tip geometric extension, not the finite color calculation or the cyclic height argument, is the main new proof obligation. It is constructed and checked explicitly in §§4–7. All pinned theorems are accepted as premises, as instructed. Neither their truth nor the completed I07 reviews is re-audited. This report does not claim worldwide priority, a MathDB score, a solution outside the stipulated corpus, or more than one finding.

## 1. Scope, immutable inputs, and primary comparison

The complete brief is retained in [brief.txt](../sources/i15_odd_order_topology/brief.txt). I read the complete I07 proposal, round-2 proof review, and completed novelty round 3, including the all-nonzero-directions replication and the stronger lattice-classification comparison. Their historical accepted counts are superseded by the user's present count of three.

The repository pin is `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` in `https://github.com/openai/math`. The source directory for this report is `frontier/sources/i15_odd_order_topology/`, abbreviated **S15**. Its `inputs/` contains immutable byte snapshots of AGENTS.md, the pin, catalogue, complete inventory, the three I07 reports, and the prior manifests/contracts. `input-manifest.json` records sizes and SHA-256 identities. All 253 cached TeX/BibTeX sources were copied and verified against both their recorded SHA-256 values and Git blob SHA-1 identities in the complete inventory. This is source identity verification, not upstream proof auditing. The inventory has 13,223 entries, 10,373 blobs, 749 manuscript directories, and `truncated: false`.

The complete title/path screen, with explicit search terms, is in `inventory-screen.json`. Among the topology-specific matches, the four strongest applicable manuscripts are already B, MT, PD, and BO below. The unrelated algebraic-geometric equivariance and knot cosmetic-surgery matches do not supply a manifold-realization or marked-grope theorem. No theorem is inferred from a title. `contracts.json` retains exact statements, labels, source line ranges, pinned raw URLs, and hashes for the four topology manuscripts. The older exact contracts and full source bytes are also retained.

An early primary-literature comparison was performed before finalizing the body. It retained the actual high-dimensional odd-prime positive results of Davis–Lück and Hilman–Kirstein–Kremer, the finite-action obstructions of Block–Weinberger, the prescribed-class rigidity theorem of Bartels–Lück, and the TOP/smooth distinction in Davis–Hayden–Huang–Ruberman–Sunukjian. Further primary reads include Davis–Leary, the Davis reflection construction, Avramidi–Okun–Schreve, Davis–Hillman, Arabadji–Baykur, and equivariant surgery of Dovermann–Schultz and Bak–Morimoto. The final comparison in §11 records the dimensions, categories, and exact reasons these statements do not already give the target. Search absence is not evidence of priority.

## 2. Exact source contracts and what they do not assert

All paths below are beneath `preprints/` at the pin:

- **B:** `Nonhomeomorphic-closed-aspherical-four-manifolds-with-the-same-homotopy-type-October-4-2026/build/`.
- **MT:** `A-marked-tensor-obstruction-to-four-dimensional-disk-embedding-September-24-2026/build/`.
- **PD:** `A-PD4-group-without-an-aspherical-manifold-model-September-24-2026/build/`.
- **BO:** `A-boundary-only-obstruction-to-four-dimensional-disk-embedding-September-24-2026/build/`.

**Assignment contract.** B `sections/tensors.tex`, `ten:assignment`, allows any finite loopless multigraph, independently distinguished plus/minus endpoints, and any family \(\mathcal L_v\) of nonempty subsets of incident edges. For characteristic-zero \(K\), algebraic germs \(F_e,b_e\) in blocks \(h_e\), and

\[
 T_v=K[t_e:e\in E_+\(v\)]/\(t_e^2\),\qquad
 S_v=\sum_{e\in E_+\(v\)}\(F_e+t_eb_e\)-\sum_{e\in E_-\(v\)}F_e,
\]

it requires centered-modulo-\((t)\) formal sections with injective central tangent maps whose signed edge-difference map is an isomorphism, exact identities \(S_v(M_v)=0\), and, for each \(L\in\mathcal L_v\),

\[
 \left\(\prod_{e\in L\cap E_+(v)}t_e\right\)
 \left\(\prod_{e\in L\cap E_-(v)}b_e\right\)\(M_v\)
 \in \((\partial_hS_v)(M_v)\). \tag{2}
\]

The conclusion is an assignment of every edge to one endpoint with no \(L\) wholly assigned to \(v\). The ideal is the **actual restricted gradient ideal**. Mixed products of distinct \(t_e\)'s remain. Zero-dimensional blocks are allowed. The theorem already allows six-element laws; no new tensor-assignment theorem is claimed. It does not construct a manifold, a body, or formal data for an arbitrary chosen law.

**Geometry contracts.** MT `sections/01-geometry.tex`, `lem:marked-body` and `lem:exterior-duals`, give the three-tip thickening, independent marked paths and terminal framing adjustment, and one-sided compression/rim calculation. B `sections/chambers.tex`, `ch:four-tip-model`, extends the marked model to two binary branches; `ch:laws` gives the four-slot word. Their statements are not six-tip statements. We prove the two additional surface attachments in §4, then use the side-marked exterior/cofiber calculation of B `ch:exterior-model`, `ch:homotopy-type`, and the full-middle-module argument of `ch:poincare-chamber` after checking their inputs.

**Formal contracts.** B `sections/formal.tex`, `for:edge-input`, imports MT's based single-cut slice, full curvature/gradient ideal, and peripheral holonomy marking. MT `sections/04-algebraicity.tex`, `thm:edge-algebraicity`, provides algebraic central potentials and marked holonomy lifts on the full critical scheme, with its formal comparison. B `for:cuts`, `for:linear`, `for:vertex-identities`, and the proof of `for:formal-data` assemble mixed endpoints. The law-dependent part is `formal.tex`'s four-slot product-ideal argument, which must be replaced by the six-slot proof in §7. The remaining nilpotent correction is MT `lem:tensor-nilpotent-correction` as invoked by B. We retain all its actual-ideal and full-parameter hypotheses.

**Reflection contract.** B `sections/reflection.tex`, `refl:input`, applies to a compact connected oriented smooth four-manifold \(D\) with connected boundary \(S\), free group \(H\), homotopy type \(BH\vee\bigvee^{2k}S^2\), and a specified framed immersed hyperbolic basis of the **whole** middle module, with zero full framed Wall self-intersections. Attaching three-cells must give a collared oriented PD4 pair \((P,S)\), with \(P\simeq BH\) and \(\pi_1S\twoheadrightarrow H\). The full independent-panel reflection is then a finite oriented aspherical PD4 complex; a closed four-manifold model yields a **marked** graph-type filling of \(S\). Its assembly, stable realization, and controlled removal inputs are included in this accepted contract. We do not substitute the weaker statement that some reflected manifold retracts to an input.

**Cyclic contract.** B `sections/cyclic.tex`, `cyc:criterion`, has positive degree two and eventual negative odd degrees. We prove the positive-degree-three version in §9, including arbitrary homeomorphisms and the exact group identification. This modification of its height proof is a transfer step, not the proposed contribution.

BO `thm:main` excludes disjoint locally flat disks with prescribed boundaries for its specified algebraic-dual input. PD `thm:main` gives a nonmanifold PD4 group. Neither supplies a ternary cap selection or an order-three outer class. B's normalizer and full-\(\operatorname{Out}\) calculations for distinguishing unmarked manifold models are **not used** here. Our conclusion does not require a homeomorphism to preserve chambers, ports, a triangulation, or a finite symmetry group.

## 3. Concrete failed alternatives and the ternary finite system

### 3.1 Binary cap choices descend through odd regular covers

**Lemma 3.1 (scope-limited binary descent).** Let a finite cap-selection problem have Boolean variables for cap occurrences, clauses requiring at least one of two alternative caps on each upper torus, and clauses forbidding simultaneous selection of any intersecting pair. Allow additional binary clauses and auxiliary Boolean variables. Suppose a finite group of odd order acts on the variables and clauses and preserves the formula. Any satisfying assignment has an invariant satisfying assignment.

*Proof.* Translate the assignment by every group element and take coordinatewise strict majority. If the majority violated a clause \(\ell_1\veeell_2\), more than half the translated assignments would falsify each literal. Those two subsets intersect, contradicting satisfaction of that clause. Majority commutes with a permutation of the variables, so the resulting assignment is invariant. Unary clauses and repeated literals cause no exception. If a formula uses auxiliary variables, take their majority too and then forget them. ∎

For a regular odd-degree cover of a downstairs finite body arrangement, use the deck action on the lifted cap occurrences. An invariant selection descends. Remove surplus choices on any binary branch to obtain one cap per branch; deleting selected caps preserves every nonintersection condition. Thus a positive filling obtained by the source's binary disjoint-cap compression in a 3-cover already gives that same cap-compression filling downstairs, which then lifts to every cover. It cannot coexist with a proved nonfilling of some other cover.

This is a limitation of the **binary selection implementation**, not a theorem that every marked filling descends under an odd cover. It includes arbitrary finite replication and binary auxiliary-variable networks. It does not exclude other fillings or other topological mechanisms. The Boolean fact is classical majority closure; no independent substantial-finding credit is claimed for it.

A three-way clause is outside this closure: \((1,0,0),(0,1,0),(0,0,1)\) all satisfy \(x_0\vee x_1\vee x_2\), but their majority does not. Consequently no existential conjunction of binary clauses can define this ternary cap availability relation. The new branches implement precisely this change of availability.

### 3.2 Merely using three colors also fails

Keeping only same-color edge bundles and asking for a deficient color forces adjacent deficient colors to differ, not to advance by one. The 4-cycle coloring \(0,1,0,2\) satisfies those inequalities, although \(3\nmid4\). Thus a proper-three-coloring gadget does not give the required cyclic spectrum. We instead forbid **every ordered pair except a prescribed successor**.

### 3.3 The exact successor gadget

Let \(C=\mathbb Z/3\). Define

\[
 \mathcal B=\{\(a,b\)\in C^2:b\ne a+1\}.
\]

There are six such ordered pairs. For each \((a,b)\in\mathcal B\), take five plumbing types \((a,b,q)\), \(1\le q\le5\). The initial port has color \(a\), the terminal port color \(b\); every plumbing generator has height (1). There are \(m=30\) plumbing types, 60 ports, and exactly 20 ports of each color at a block.

For \(d\ge2\), let \(\Gamma_d\) have vertices \(\mathbb Z/d\), and for each type an edge from \(v\) to \(v+1\), with the indicated endpoint colors. Keep all directed lifts as distinct unoriented edges with specified initial/terminal ports. When \(d=2\), the edges \(v\to v+1\) and \(v+1\to v\) of the same type are distinct. The graph is loopless, and the incident edges correspond bijectively to the 60 ports at each vertex.

Let \(\mathcal L_v\) contain every six-element incident-edge set having two ports of each color.

**Lemma 3.2.** An endpoint assignment avoiding all \(\mathcal L_v\) exists if and only if \(3\mid d\). If \(3\mid d\), there is a cap-color selection with one selected color per vertex and **at most one selected endpoint at each plumbing**.

*Proof.* For an endpoint assignment, let \(D(v)\subset C\) be the colors in which \(v\) receives at most one edge. If \(D(v)\) were empty, two received edges of each color would make a forbidden set. Thus \(D(v)\ne\varnothing\).

If \(a\in D(v)\), \(b\in D(v+1)\), and \(b\ne a+1\), the five edges of type \((a,b,q)\) could receive at most two endpoint assignments in total. All five must be assigned, a contradiction. Hence

\[
 D\(v\)\times D\(v+1\)\subset\{\(a,a+1\):a\in C\}.
\]

Since both sets are nonempty, both are singletons. Write \(D(v)=\{s(v)\}\). Then \(s(v+1)=s(v)+1\), which closes around the cycle exactly when \(3\mid d\).

Conversely let \(s(v)=v\bmod3\). Select every port of color \(s(v)\) at vertex \(v\). An edge could have both ends selected only if \((a,b)=(s(v),s(v)+1)\), a pair omitted from \(\mathcal B\). Thus at most one end is selected. Assign each edge to an unselected end, choosing arbitrarily when neither is selected. Each vertex receives zero edges of its selected color, so no law is wholly received. ∎

There are deliberately edges with neither end selected: per consecutive pair, ten of the thirty edges have zero selected ends and twenty have one. The positive geometric argument needs only the absence of **two** selected ends; it never needs exactly one. This differs from the binary source and is essential.

## 4. The six-tip marked body: construction, framing, and compression

The bottom surface \(F\) is a punctured torus with branches \(a,b\). On each attach a punctured torus \(U\). Its first basis curve is a terminal tip of color 0. On its second basis curve attach another punctured torus \(W\), whose two basis curves are terminal tips of colors 1 and 2. There are five punctured tori in one body: \(F\), two \(U\)'s and two \(W\)'s. Each bottom branch therefore has the rooted three-tip shape \([X_0,[X_1,X_2]]\). Its depth is two below the bottom branch, not an infinite grope.

For every ordered sextuple of distinct ports with colors \((0,1,2,0,1,2)\), every independent sextuple \(c_i\in\{1,l_1,\ldots,l_9\}\), and every independent sign \(\epsilon_i\in\{1,-1\}\), install one such body with based tips

\[
 X_i=c_i x_{p_i}^{\epsilon_i}c_i^{-1},\qquad 1\le i\le6. \tag{3}
\]

Here \(x_p\) is the based meridian of that port in the outside piece. The same finite list is installed in every block. The number of bodies is

\[
 k=\(20\cdot19\)^3\,10^6\,2^6
   =3{,}511{,}808{,}000{,}000{,}000. \tag{4}
\]

This large number is finite. No bound on manifold complexity is part of the theorem; the body list is an exact finite specification and need not be enumerated into a file.

**Lemma 4.1 (six marked primitive tip annuli).** This surface tree has a smooth three-dimensional handlebody thickening of genus six, marked as a boundary join of six longitudinal-annulus collars. The finite list (3) can be placed with disjoint body sheets in the source plumbing outside pieces. The bottom surfaces are proper inward pushes of disjoint boundary surfaces. All terminal caps are embedded and framed, miss body sheets away from their own attachments, and can intersect other terminal caps only at opposite branches of a plumbing chart.

*Proof of the new thickening step.* Start from B's marked genus-four thickening of its four-tip body. At the second tip of each bottom branch, replace the terminal longitudinal-annulus collar by the thickening of a punctured torus, glued along that torus's initial-boundary annulus. This is exactly the primitive-annulus attachment used in MT's three-tip construction, now performed twice in disjoint neighborhoods.

A longitudinal-annulus collar is an annulus times an interval; attaching it adds a collar to the new punctured-torus thickening. Extend the latter's two meridian disks across that collar. Move the feet of the old connecting tubes into the complement of the finitely many disk strips. The old meridian disk dual to the replaced tip is replaced by these two disks; the other old meridian disks stay disjoint. Each replacement raises the genus by one and creates no connecting cycle. After both replacements there are six disjoint meridian disks, each dual to exactly its marked terminal annulus, and cutting along all six gives a ball.

Each cut annulus becomes a rectangle joining only the two faces of its own disk. The six rectangles and their face neighborhoods are disjoint disks on the ball boundary. The smooth ball-isotopy argument in MT `lem:marked-body` standardizes these marked neighborhoods and reattaches the handles. This proves an identification of the **annuli and transported surface tree**, not just a free-group basis. The lower initial boundary and internal surface markings are carried with the tree.

For placement, reserve a separate product track for every terminal occurrence in the finite list, then join the six collar neighborhoods by thin tubes along a rooted tree in the three-dimensional outside face. Choose the path from the outside basepoint to terminal \(i\) in the class \(c_i\kappa_{p_i}\). Finitely many arcs in a three-manifold can be separated relative to their prescribed ends; repeated portions get parallel tracks. There is no compatibility relation among six external conjugators. Different body trees and their narrow neighborhoods are disjoint. The construction is done in the initial boundary away from thin attaching solid tori, then the returning tracks are extended to the ports. Thus plumbing changes neither the path markings nor the bottom-surface boundary-push property. This is the finite-placement argument of B applied to the just-proved six-annulus model.

For framing, use the oriented normal in the three-dimensional body and the collar direction. In each terminal solid-torus neighborhood perform \((\theta,z)\mapsto(\theta,\phi(\theta)z)\), where \(\phi\) has the integer degree needed to remove the framing discrepancy and is 1 near connector feet. Transport the complete marked body before fixing its final initial-boundary link. Construct the return collar afterward as

\[
 \(\theta,s\)\longmapsto\(\theta,r(s)i\phi(\theta),u(s)\).
\]

Choose \((r,u)\) as in MT/B: it departs in the positive \(r\)-direction, ends vertically at \((0,1)\), and \(u\) increases for \(s>0\). Its normal quotient frame is \((\phi,r'\partial_u-u'i\phi)\). Its terminal winding is the prescribed degree, while its terminal product circle is unchanged. The six primitive annuli make these corrections independent. Connector feet and external paths remain fixed; internal path changes are words in the six terminal generators and introduce no extra-handle generator. At all five symplectic pairs, separate the two attachments onto opposite normal sides. Place bodies at an inner collar level and continue terminal tracks into separated parallel core disks. The original product plumbing chart has intersections only between opposite branches; a core has no self-plumbing. These facts prove all the stated incidence and framing properties. ∎

**Lemma 4.2 (three-way compression).** For either bottom branch and any one of its three terminal tips, compression gives an embedded framed branch disk using only parallel copies of that chosen terminal cap and body sheets. It has two cap sheets for color 0 and four for color 1 or 2. Distinct such disks have no intersections except those coming from opposite selected plumbing branches, apart from the intended bottom collar intersection used to construct a rim dual.

*Proof.* To use color 0, compress \(U\) directly along its first basis curve. Cut the punctured torus to a pair of pants and fill the two new boundaries with oppositely oriented parallels of the chosen cap. The \(W\)-branch is unused and is not part of the disk. To use color 1 or 2, first compress \(W\) along that chosen terminal cap, producing an embedded framed disk bounded by the second basis curve of \(U\). Compress \(U\) using two parallels of that disk. This yields four parallels of the one chosen terminal cap. At each stage the one-sided compression is the product model of MT `lem:exterior-duals`; the outgoing collar has the inherited framing, so its use at the next stage adds no Euler twist. Reserve separated parallel collars at the finitely many stages. Each disk uses one port core, with no self-plumbing; disjoint body neighborhoods eliminate all other intersections. ∎

These lemmas are the asserted new geometric extension. The proof does not treat a finite cap model as a manifold proof, does not infer an embedding from a commutator identity, and does not assume the source four-tip statement already has arbitrary arity.

**Lemma 4.3 (six-slot law).** The based initial boundary of each body is a word \(L\) that becomes 1 when any terminal generator becomes 1, and

\[
 L\equiv [[X_1,[X_2,X_3]],[X_4,[X_5,X_6]]]\pmod{\Gamma_7F_6}.
\]

*Proof.* Read the punctured-torus boundary commutator first at each \(W\), then at each \(U\), then at \(F\). Setting any leaf to 1 kills its successive ancestor commutators, ultimately the root. Internal basing changes conjugate subtree words by words in the six tips. Their constant terms are 1 when the tips vanish, so they preserve the degree-six initial term. Signs are fixed by orienting the five symplectic pairs; reversing specified tips is already in the installed list. The framing transports in Lemma 4.1 do not alter the terminal core words. ∎


## 5. The chamber, full middle module, and all lifted data

Start with the uncolored plumbing block of B: \(2m+9\) one-handles, \(2m\) product-framed cancelling two-handles, mutually plumbed in \(m=30\) distinct pairs, and no self-plumbing. Denote the resulting compact smooth four-manifold by \(X\). The tree development by blocks meeting in contractible product balls gives
\[
 X\simeq B F(\tau_{a,b,q},l_1,\ldots,l_9).
\]
Colors are labels on ports, not framings or changes to the plumbing chart. The outside face is the source's \((\#^9 S^1\times S^2)\setminus\operatorname{int}\nu L_{60}\), with free meridians \(x_p\) and extra loops \(l_s\); each \(x_p\) dies in the block. The join still interchanges meridian and longitude. Install Lemma 4.1's finite body list.

Remove product tubes only around the bottom punctured tori \(F_j\), leaving \(E\). All upper surfaces, cap disks, and their null-homotopies remain in \(E\), apart from their truncated bottom attaching collars. Each branch loop is nullhomotopic in \(X\), since all terminal loops are capped there. The entire \(F_j\to X\) is nullhomotopic. Replace each \(F_j\times S^1\) tube side by \(V_j\times S^1\), where \(V_j\) is the solid-torus compression body that compresses the \(a_j\)-curve of \(F_j\), exactly as in B. Call the result \(D\) and its boundary \(S\).

The new upper stages do not change this replacement. The bottom surfaces still satisfy the precise boundary-push and product-trivialization hypotheses of the side-marked exterior model. Its pushout preserves the actual tube-side maps and normal-circle generator. Consequently the cofiber calculation gives
\[
 H=\pi_1D=F(\tau_{a,b,q},l_1,\ldots,l_9,z_1,\ldots,z_k),
 \qquad D\simeq BH\vee\bigvee^{2k}S^2. \tag{5}
\]
Explicitly \(F_j\to V_j\times S^1\simeq T^2_{b_j,z_j}\) cones off a trivial \(a_j\)-loop and kills \(b_j\); cancelling that one/two-cell pair leaves \(S^1_{z_j}\vee S^2\vee S^2\). The six tips do **not** add six sphere summands: only the unchanged bottom replacement creates middle homology. Killing all \(z_j\) recovers the original boundary marking into \(\pi_1X\). Surgery along the initial-boundary link leaves \(S\) connected.

### 5.1 Algebraic duals without an unproved deep-sheet cancellation

For the initial algebraic middle calculation choose the **shallow color-0 terminal cap on each bottom branch**, at every body. Lemma 4.2 then gives two-sheet compression disks just as in B. Let \(f_j\) be the truncated \(a_j\)-disk, and \(C_j\) the \(b_j\)-disk. Compress the rim torus over \(b_j\) with two parallels of \(C_j\) to obtain \(g_j\). The local \((s,t,r,\theta)\) collar calculation of B, ch:exterior-duals, gives one intersection between \(f_j\) and \(g_j\), based to contribute \(1\), and no inter-body collar intersections.

At a remaining plumbing intersection, fix the outer parallel-copy index of \(C_j\) and the opposing sheet. The two inner cap sheets have opposite signs. Their based paths differ by the unused second basis loop of \(U\). **In this new body that loop is the boundary of \(W\), not a terminal cap circle.** It is nevertheless nullhomotopic in \(E\): compress \(W\) along either one of its framed terminal caps, all of which remain after removing the bottom tubes. Its nullhomotopy need not be disjoint from the selected disks to give equality in \(\pi_1E\). A small normal turn about the undeleted upper surface also bounds in \(E\). The two intersection labels are thus equal and their coefficients cancel, with the outer rim index held fixed. No bottom normal-circle generator is killed or identified in this argument.

It follows that
\[
 \lambda(f_i,g_j)=\delta_{ij},\qquad \lambda(g_i,g_j)=0
 \quad\text{over }\mathbb Z[\pi_1E]. \tag{6}
\]
Each \(g_j\) uses only a single selected port core, which has no self-plumbing, and separated collars, so it is individually embedded with trivial normal bundle. Different spheres may intersect. Closing \(f_j\) with the meridian disk of \(V_j\) gives a framed sphere \(u_j\) in \(D\). The source's framing match uses only the outgoing \(a_j\)-collar and the unchanged bottom compression body. Hence (6) holds for \(u_i,g_j\) over \(\mathbb ZH\).

This deliberate shallow choice removes any need to assert an unverified general cancellation formula for arbitrary iterated compression. Deeper disks will be used only in the positive filling, where the selected caps are disjoint and there are no unwanted plumbing intersections to cancel.

### 5.2 Whole-module basis, zero quadratic invariants, and duality

The remaining B ch:poincare-chamber calculation now applies to precisely (5)–(6). For clarity, its required algebra is as follows. The hermitian matrix of the \(u_i\)'s has even identity coefficient on its diagonal, by their framing parity. Since \(H\) is free it has no nonidentity order-two element. Write each diagonal entry as \(z+\bar z\), taking halves at the identity and one coefficient from each nonidentity inverse pair. Subtract suitable combinations of the \(g_j\)'s from the \(u_i\)'s, with triangular halves off the diagonal, to make all \(u\)-pairings zero without changing cross-pairings. Tubing yields framed immersed representatives.

The full framed Wall invariant lies in the additive quotient \(\mathbb ZH/\langle h-h^{-1}\rangle_{\mathbb Z}\), retaining the identity coefficient. Symmetrization sends each nonidentity inverse-pair coefficient injectively to the corresponding pair and doubles the identity coefficient. Thus \(\lambda(v,v)=0\), with the framing, implies the full \(\mu(v)=0\); no reduced quotient is substituted.

There are \(2k\) such classes in the free rank-\(2k\) module in (5). Their hyperbolic pairing supplies a one-sided inverse to their basis matrix. Matrix rings over this free-group ring are directly finite: map a one-sided inverse to each finite quotient, obtain the reverse identity in its finite-dimensional complex regular representation, and use residual finiteness to separate finite supports. Thus the matrix is invertible, proving a basis of the **whole** middle module.

Attach three-cells on that basis, forming \((P,S)\). The basis-realizing map \(BH\vee\bigvee^{2k}S^2\to D\) is a homotopy equivalence by the universal-cover homology criterion; the three-cells kill all sphere summands, so \(P\simeq BH\). The regular-coefficient duality argument of B applies to the same nonsingular absolute/relative middle summands. In homology the attachments quotient out those summands without new third homology; in cohomology the pullbacks identify their annihilators. Naturality of cap product descends duality from \((D,S)\) to \((P,S)\) for all local coefficients. This gives an oriented finite PD4 pair with the unchanged boundary collar. Duality and graph type give \(H_i(P,S;\mathbb ZH)=0\) for \(i=0,1\); hence \(H_0(S;\mathbb ZH)\cong\mathbb Z\) and \(\pi_1S\twoheadrightarrow H\).

Define
\[
 w:H\twoheadrightarrow\mathbb Z,\qquad
 w(\tau_{a,b,q})=1,\quad w(l_s)=w(z_j)=0.
\]
For each \(d\ge1\), let \((D_d,P_d,S_d)\) be the \(w\bmod d\) cover. The boundary is connected by surjectivity. Each replacement piece has height zero: its longitude dies and its normal circle has height zero. Thus all bodies and replacements lift individually. Restriction of the full free middle module to \(\mathbb ZH_d\) gives exactly \(d\) copies of each basis sphere; projection of pairing coefficients onto \(H_d\) gives the standard lifted hyperbolic form. The framed Wall projection retains the identity and both elements of every retained inverse pair, so it preserves zero. Three-cells, collars, and orientation lift. All of refl:input therefore holds for every lifted chamber, not just for the 3-cover.

## 6. Positive fillings in every degree divisible by three

Assume \(3\mid d\). At each block \(v\), select every port of color \(s(v)=v\bmod3\). Every bottom branch has exactly one terminal tip of that color. Use Lemma 4.2 to compress it. Because no plumbing has two selected ends, all used cap parallels are disjoint, including across different bodies and across the two branches of one body. The presence of unselected ends at both sides of some plumbing causes no intersection and imposes no surgery requirement.

Construct \(u_j,g_j\) using these branch disks. The unchanged bottom collar model gives exactly one geometric intersection within each pair and no others. For deeper color-1 or color-2 choices, reserve four cap sheets per branch and their further rim parallels; the finite list permits arbitrarily many separated tracks. Their framing is the iterated product framing proved in Lemma 4.2. Pairing/direct-finiteness and the rank \(2dk\) from (5) show that these embedded pairs again form a full hyperbolic middle basis; they need not be the particular shallow immersed basis chosen downstairs.

Remove disjoint neighborhoods of these pairs. Each is a punctured \(S^2\times S^2\), since the two spheres are framed and meet once. Replace each by a four-ball along its standard \(S^3\) boundary, giving a compact oriented topological four-manifold \(V_d\) with boundary \(S_d\). These are interior operations and preserve the boundary marking. Van Kampen preserves \(H_d\), since the removed neighborhoods and their boundaries are simply connected. The complement is connected by rerouting paths along the connected boundary of a removed neighborhood.

In the universal cover, Mayer–Vietoris identifies the sum of the neighborhood \(H_2\)'s with the full old \(H_2\). The complement has zero \(H_2\), and its \(H_3\) is precisely the sum of the boundary \(S^3\) classes. Inserting balls kills those classes, creates no \(H_4\), and leaves no other reduced homology. Local finiteness justifies the direct sums in this lifted computation. The new universal cover is simply connected and acyclic, hence contractible by the homological Whitehead theorem for CW-type spaces. Thus \(V_d\simeq BH_d\simeq P_d\).

The classifying map preserves the boundary group marking, so its boundary restriction is homotopic to \(S_d\to P_d\). The boundary collar extends that homotopy, giving a homotopy equivalence \((V_d,S_d)\to(P_d,S_d)\) equal to the identity on \(S_d\). This is a **marked filling**, not just an unmarked graph homotopy type. No unproved general disk-embedding statement is invoked.

## 7. Negative fillings: all formal and geometric hypotheses

Suppose \(d\ge2\) and \(S_d\) has a marked graph-type filling. Undo the law surgeries by attaching the dual two-handles. Their attaching circles are exactly the individually lifted normal-circle free generators \(z_j\), because \(w(z_j)=0\). They cancel those free factors in the graph homotopy type. The result is a compact topological four-manifold \(W_d\) with boundary \(\partial X_d\), the original graph marking, and disjoint proper cocore disks bounded by all six-slot law curves.

### 7.1 Cuts, smoothing, slopes, and boundary normalization

The cut construction of B for:cuts uses the universal covering **tree of the plumbing multigraph**, not a line. Our graph still has 30 edges per directed step and nine extra loops at each vertex. Forget those extra loops in the graph marking. Prescribe the map to its universal tree on the outside faces, law-disk neighborhoods, and join-torus collars. The associated tree bundle has contractible fiber, so the compatible prescriptions extend. Use the source's punctured smoothing away from the finitely many prescribed disks and collars; choose the map constant near the punctures, smooth over edge interiors, and take regular cuts.

For connectedness, the component graph of the cuts in the tree cover has fundamental group a quotient of that of the covered \(W_d\). The latter is generated by the named extra loops, each contained in one piece; the component graph is a tree. The prescribed outside faces and join collars form its principal plumbing subtree. Every off-principal branch has a unique attaching vertex and trivial stabilizer under the deck action. An orbit can meet the branches at a fixed principal vertex at most once. Finitely many quotient component orbits therefore imply that only finitely many such pieces attach there; merge them by discarding their closed cuts. This yields one connected cut \(Y_e\) per prescribed edge, with exactly its join torus as boundary, and connected vertex pieces containing their law disks. No step depends on four versus six slots or equality of the port colors at a join.

Here
\[
 b_1(W_d)=b_1(\Gamma_d)+9d=(30d-d+1)+9d=38d+1.
\]
The graph type gives \(H^2(W_d)=H^3(W_d)=0\). Mayer–Vietoris makes the signed degree-two restriction an isomorphism and the degree-one restriction surjective. Its kernel is \(H^1(W_d)/H^1(\Gamma_d)\), identified by evaluations on the \(9d\) named extra loops. Imposing zero such evaluations removes exactly that kernel. Half-lives/half-dies gives a one-dimensional boundary-cohomology image for each torus-boundary cut. The two vertex restrictions annihilate their respective bounding longitudes, the two original coordinate slopes. Surjectivity therefore forces the line to be one of those coordinate lines. It independently designates the plus and minus ends of each cut; these signs have no relation to \(a,b\in C\).

Topological vertex pieces use precisely the source's filled punctured-form complex: functions constant near each puncture and positive-degree forms zero near punctures. It computes filled cohomology and supports coefficientwise Stokes with no contributions at punctures. Only the compact smooth three-manifold cuts enter the single-edge theorem.

On every outside face, the free port-meridian/extra-loop marking still has the disjoint dual-disk and dual-sphere strips used by B. A plus port is normalized in its \(\zeta_e\) polarization and a minus port in its \(\xi_e\) polarization. This simultaneously supplies the boundary strip representative with zero action. The based slice gauge is the identity on the **entire torus**, so its gauges agree with the outside normalization and introduce no unrecorded peripheral conjugation. The new body paths were fixed in that very outside face. These are the boundary-normalization facts used here; no new theorem about normalizers of boundary subgroups in a full outer automorphism group is needed.

### 7.2 The law-independent formal construction

Apply B for:edge-input to each cut with its verified boundary line. At each vertex use the source's based cohomological contraction and finite residual curvature list \(r_v\), with ideal \(I_v\). The signed restriction isomorphism gives injective central tangent maps with isomorphic total edge difference. Degree-two restriction and the relative/absolute trace pairing give a unit full-column minor for the gradient coefficient matrix against \(r_v\). No regular-sequence or independence assumption on \(r_v\) is needed.

Assign the nine adjoint-spanning matrices \(g_{ab}(\sigma)=\exp(a\sigma e)\exp(b\sigma f)\), \(a,b\in\{0,1,2\}\), to the identity and eight of the named loops, leaving the remaining loop trivial. These nine adjoints span \(\operatorname{End}_{\mathbb C((\sigma))}(\mathfrak{sl}_2)\), as in MT. Every port meridian is trivial in the common flat background. Graph-cycle transports are free groupoid generators, so there is no compatibility relation preventing this background.

The mixed-endpoint Stokes calculation of B for:vertex-identities now gives action in \(I_v^2\) and gradient equal to a matrix times \(r_v\), with the unit minor just checked. The plus-end boundary term is canceled by the edge potential's \(\epsilon_e\operatorname{tr}(u_ev_e)/2\) adjustment; the minus-end variation vanishes in the fixed polarization. The correction by \(I_v\)-multiples gives exact zero action and preserves the actual gradient ideal. This part of B's proof precedes the use of any law word and applies unchanged to the present cuts.

Use MT's **marked** algebraicity and formal comparison separately on each edge to obtain common algebraic central germs \(F_e\) and algebraic lifts \(G_e\) of the specified peripheral holonomy on the full critical scheme. Absorb the gradient-ideal discrepancy of the logarithmic coefficient by a coordinate change linear in its own \(t_e\), made only at the plus end and equal to identity at \(t_e=0\). The two ends retain the same central edge coordinates. Recenter at the common background in the joint \(\sigma\)-adic rings **before** passing to \(K=\mathbb C((\sigma))\). Subsequently only centered or nilpotent-constant substitutions are made. This retains algebraicity, marked holonomy, the actual residual ideals and unit minors. No reduced representation variety or unmarked critical locus is substituted.

### 7.3 A proved six-slot product-ideal law

Fix a six-set \(L\in\mathcal L_v\) and order it as \((0,1,2,0,1,2)\). Fix lifts \(X_1,\ldots,X_6\) of its based port logarithms, vanishing at the background, in \(T_v[[y_v]]\). Let \(J_L\) be the ideal generated by products of one scalar matrix coordinate from each \(X_i\), and \(Q_L\) the ideal generated by the actual law matrices minus identity for the installed independent conjugator/sign choices on those six ports.

Every law bounds a disk in the vertex piece, hence vanishes in the flat quotient by \(I_v\). Off-shell words are evaluated using the fixed logarithm lifts and agree with holonomy only in that quotient; off-shell homotopy invariance is not assumed. Brunnianity puts every entry in \(J_L\); every higher term is in \(\mathfrak m_vJ_L\), because each contains at least one factor from every slot and at least one additional factor. This statement is first an identity in independent logarithms and remains an ideal statement after substitution, including nilpotent coefficients.

The leading six-linear tensor
\[
 T(U_1,\ldots,U_6)=[[U_1,[U_2,U_3]],[U_4,[U_5,U_6]]]
\]
is nonzero on \(\mathfrak{sl}_2\). With \([e,f]=h,[h,e]=2e,[h,f]=-2f\),
\[
 T(e,h,f,h,h,e)=[-2h,4e]=-16e. \tag{7}
\]
Choose an output functional detecting this value. For any six chosen input coordinates, rank-one endomorphisms carrying those coordinates to the six vectors in (7) make that scalar product a multiple of an output coordinate of \(T\). Expand each endomorphism independently in the nine prescribed adjoints. The installed six independent conjugators therefore span **all** coordinate products in \(J_L\) modulo \(\mathfrak m_vJ_L\). Internal path changes are identity at the background and affect only the higher terms already considered. Consequently
\[
 Q_L\subset J_L\cap I_v,\qquad J_L=Q_L+\mathfrak m_vJ_L.
\]
Nakayama for the finitely generated module \(J_L/Q_L\) over the complete local ring gives \(J_L\subset I_v\). This is an inclusion in the actual ideal, with no radical or power substitution.

For the plus inputs the flat logarithm is \(-t_eT_e\); choose one nonzero coordinate of each \(T_e\). At each minus input, every entry of \(G_e-1\) is in the ideal generated by the port logarithm. Thus, writing \(I=L\cap E_+(v)\), \(J=L\cap E_-(v)\),
\[
 \left(\prod_{i\in I}t_i\right)
 \prod_{j\in J}(G_j-1)_{r_js_j}(M_v)\in I_v \tag{8}
\]
for every choice of matrix entries. Parameters from plus ends outside \(L\) have remained in the ring throughout.

Finally take the algebraic perturbation
\[
 b_e=-\epsilon_e\operatorname{tr}\left(T_e[(G_e-1)-\tfrac12(G_e-1)^2]\right).
\]
At a plus end, specializing only its own parameter to zero gives \(G_e(M_v)-1\in(I_v,t_e)\). The logarithmic remainder has cubic order and its internal derivative quadratic order, yielding \(t_eR_e(M_v)\in t_eI_v^3\) and \(t_e\partial_hR_e(M_v)\in t_eI_v^2\). B/MT's nilpotent correction restores exact zero potential with displacement in \(I_v\), preserving that ideal and its unit minor. It iterates in powers of the full nilpotent ideal; distinct-parameter products are not discarded. Since each \(b_e\) is a polynomial without constant term in \(G_e-1\), (8) gives exactly (2). Formal graph reparametrization preserves these memberships and the central tangent isomorphism.

All hypotheses of B ten:assignment are now verified for the whole graph and the six-set law family. Its endpoint assignment contradicts Lemma 3.2 unless \(3\mid d\). Therefore **no marked filling exists for any \(d\ge2\) with \(3\nmid d\)**. For \(d=1\), a marked filling would lift to a marked filling in degree two, already excluded. Together with §6 this proves the exact marked-filling spectrum for every positive \(d\).


## 8. Reflection and the exact closed-manifold cover spectrum

Apply B refl:input to \((D,P,S,H)\). Choose a finite flag triangulation of the smooth closed three-manifold \(S\), take its dual panels, and give every panel its own coordinate in \(A_0=(\mathbb Z/2)^{\mathcal V}\). Form
\[
 Q=\mathcal R_{A_0}(P).
\]
It is a finite connected oriented aspherical PD4 complex. Folding onto a chamber induces a split epimorphism \(G=\pi_1Q\to H\). Compose with \(w\), still denoted \(w:G\twoheadrightarrow\mathbb Z\), and let \(Q_d\) be the cover corresponding to \(G_d=w^{-1}(d\mathbb Z)\).

**Theorem 8.1 (ternary cyclic spectrum, under the pinned contracts).** For every positive integer \(d\),
\[
 Q_d\text{ has a closed topological four-manifold model}
 \quad\Longleftrightarrow\quad 3\mid d. \tag{9}
\]

*Positive direction.* The pullback of \(P_d\to P\) along the folding map is \(Q_d\). It uses one copy of \(P_d\) per element of \(A_0\), reusing the original downstairs panel label at each lifted panel. For \(3\mid d\), replace \(P_d\) by the marked filling \(V_d\) of §6 and make the same identifications. At a point of the boundary the incident lifted panels project to distinct downstairs panels, so the local sector identifications are the usual manifold reflection charts. Label parity supplies a consistent orientation. The result \(M_d\) is closed and connected. The relative homotopy equivalence is the identity on the boundary and on all panel intersections. Collars and the finite subcomplex structure make the diagrams cofibrant, so their gluings are homotopy equivalent. Thus \(M_d\simeq Q_d\), hence \(M_d\) is aspherical and has dimension four. A global smooth structure on this reflected output is not needed or claimed.

*Negative direction.* The lifted boundary triangulation of \(S_d\) is flag: a clique projects to distinct adjacent downstairs vertices, the downstairs simplex exists, and edge-lift uniqueness puts the whole clique in a lift of that simplex. Give **each lifted panel its own independent coordinate**, obtaining \(A_d\) and the full reflection \(\widehat Q_d=\mathcal R_{A_d}(P_d)\). Sending each coordinate to its downstairs coordinate induces \(\widehat Q_d\to Q_d\). It is onto and is injective on every incident-panel subgroup; equivalently its kernel acts freely on every chamber sector. This gives finite covering charts. Each coordinate is realized by crossing a nonempty panel and \(P_d\) is connected, so the covering space is connected. This proves the full-versus-reused-label comparison for this chamber, without invoking the source parity chamber.

If \(Q_d\) had a closed manifold model, lift that model through this finite covering. Apply refl:input to the lifted chamber data checked in §5.2. It produces a marked filling of \(S_d\), impossible by §7 when \(3\nmid d\). A hypothetical unoriented model does not escape: the oriented aspherical PD4 complex has trivial dualizing-module orientation character, which is the orientation character of every aspherical manifold model. The boundary marking supplied by refl:input is exactly the one needed, so no unmarked-filling substitution occurs. This proves (9). ∎

This use of independent panel labels is necessary. Directly applying refl:input to the reused-label reflection would omit a hypothesis. Nothing in the argument assumes arbitrary homeomorphisms preserve any panel or chamber.

## 9. The order-three cyclic criterion for arbitrary representatives

The following transfer is included with proof; it is a modification of B cyc:criterion, not a second proposed finding.

**Lemma 9.1.** Let \(Q\) be finite, connected and aspherical, \(G=\pi_1Q\), and \(w:G\twoheadrightarrow\mathbb Z\). Put \(G_d=w^{-1}(d\mathbb Z)\). Suppose \(Q_3\) has a closed topological \(n\)-manifold model \(M\). Choose \(\gamma\in G\) with \(w(\gamma)=1\). For \(j=1\) or \(2\), if \(Q_{3R+j}\) has no closed \(n\)-manifold model for every sufficiently large integer \(R\), then the outer automorphism of \(G_3\) represented by \(\operatorname{Ad}_{\gamma^j}\) is induced by no homeomorphism of \(M\).

*Proof.* Let \(h\) be a hypothetical homeomorphism representing that class. Its universal-cover lift \(u\) can be corrected by a deck transformation so that
\[
 u a u^{-1}=\gamma^j a\gamma^{-j}\qquad(a\in G_3). \tag{10}
\]
This is an exact automorphism identity, not just an equality in an outer group. Let \(K=\ker w\), \(X=K\backslash\widetilde M\). Since (10) preserves \(K\), \(u\) descends to a homeomorphism \(h'\) of \(X\). The element \(\gamma^3\in G_3\) acts as the generator \(T\) of the cyclic deck group \(X\to M\). Because \(\gamma^j\) centralizes \(\gamma^3\), \(h'T=Th'\).

Represent \(w/3:G_3\to\mathbb Z\) by a map \(M\to S^1\) and lift it to a continuous height \(\tau:X\to\mathbb R\) with \(\tau(Tx)=\tau(x)+1\). A compact set \(C\subset X\) meets all \(T\)-orbits. Its height lies in some \([a,b]\). For any bounded interval \([A,B]\), its preimage is a closed subset of the finite union of \(T^kC\) for \(A-b\le k\le B-a\), hence compact. Thus \(\tau\) is proper.

The function \(\tau(h'x)-\tau(x)\) is \(T\)-invariant and bounded in absolute value by some \(c\). For an integer \(R>c+1\), let \(F_R=T^Rh'\). Then
\[
 0<R-c\le\tau(F_Rx)-\tau(x)\le R+c. \tag{11}
\]
No nonzero power fixes a point. If a translate of a compact set intersects another compact set, (11) bounds the exponent, so the cyclic action is properly discontinuous. Heights tend to both infinities along each full orbit, and its first nonnegative height is at most \(R+c\). The compact band \(\tau^{-1}([0,R+c])\) meets all orbits. Therefore \(N_R=X/\langle F_R\rangle\) is a closed connected topological \(n\)-manifold, with contractible universal cover \(\widetilde M\).

It remains to identify its group correctly. The lift
\[
 Z_R=\gamma^{3R}u
\]
is legitimate because \(\gamma^{3R}\in G_3\) is an actual deck transformation of \(\widetilde M\); no action of \(\gamma\notin G_3\) on that manifold is presumed. Equation (10) gives
\[
 Z_R k Z_R^{-1}=\gamma^{3R+j}k\gamma^{-(3R+j)}
 \qquad(k\in K).
\]
The deck group over \(N_R\) is generated by the faithful deck group \(K\) and \(Z_R\), with quotient the infinite cyclic group freely generated by \(F_R\). Thus every word has unique normal form \(kZ_R^a\); the exponent is detected downstairs and then faithfulness detects \(k\). Map this word to \(k\gamma^{(3R+j)a}\). Every element of \(G_{3R+j}\) has the same unique form because its height is a multiple of \(3R+j\). The displayed conjugation formula proves multiplicativity. Hence
\[
 \pi_1N_R\cong K\rtimes_{\operatorname{Ad}_{\gamma^{3R+j}}}\mathbb Z
       \cong G_{3R+j}.
\]
No cyclic finite extension was assumed split. Only the extension by the infinite cyclic height quotient splits, by the explicitly chosen lift; the finite quotient cocycle is not discarded. Since \(Q_{3R+j}\) and \(N_R\) are aspherical CW-type spaces, they are homotopy equivalent, contradicting eventual nonrealization. The proof never assumes any finite order of \(h\) or \(u\). ∎

## 10. Exact target theorem

**Theorem 10.1 (proposed new construction).** Relative to the accepted pinned corpus, there is a closed connected oriented aspherical topological four-manifold \(M\) and an injection
\[
 C_3\longrightarrow \operatorname{Out}(\pi_1M)
\]
whose image intersects the image of \(\operatorname{Homeo}(M)\) only in the identity.

*Proof.* Use \(Q,w\) of Theorem 8.1 and let \(M=M_3\). Identify \(\pi_1M=G_3\). Since \(G_3\) is normal in \(G\) and \(G/G_3\cong C_3\), conjugation defines a homomorphism \(C_3\to\operatorname{Out}(G_3)\). Its generator is \(\alpha=[\operatorname{Ad}_{\gamma}]\). Its cube is inner, specifically \(\operatorname{Ad}_{\gamma^3}\), so \(\alpha^3=1\). Theorem 8.1 and Lemma 9.1 with \(j=1\) exclude any homeomorphism representing \(\alpha\). It cannot be the identity class, since the identity homeomorphism represents that class. Therefore its order is **exactly three** and the homomorphism is injective.

If a homeomorphism represented \(\alpha^2=\alpha^{-1}\), its square would represent \(\alpha\), again impossible. Alternatively apply Lemma 9.1 with \(j=2\), since all degrees \(3R+2\) are also excluded. Each outer automorphism is represented by a homotopy self-equivalence of the aspherical CW-type manifold. The manifold has dimension four throughout the chamber surgery and reflection. ∎

The theorem excludes arbitrary orientation and arbitrary order of the representing homeomorphism. It does not assert that all of the outer automorphism group is \(C_3\), that \(M\) is asymmetric, or that no topological homeomorphisms of order three exist in unrelated classes. The exact cyclic-cover spectrum, the marked local law, and the final outer-class obstruction are one mechanism, not separate counted findings.

## 11. Final primary-literature review and significance limits

The final search found a relevant **August 2026 paper by Kremer that was not in the retained I07 comparison**. Its actual Theorems B and D were read and its versioned PDF retained. Thus the final comparison is not merely a repetition of the completed novelty review. Source bytes, URLs, version identities, text hashes and passage records are in S15/literature and reading-index.json. Search responses are retained in early-search*.json, primary-versions.json, final-search*.json, and final-primary-open.json.

**Odd-order positive realization.** Davis–Lück, published 2024, Theorem 1.4, assumes an extension \(1\to\pi\to\Gamma\to G\to1\), an oriented closed \(d\)-manifold model for \(B\pi\), \(d\ge5\), hyperbolic \(\pi\), cyclic odd-order nontrivial finite subgroups, and conditions (M), (NM), (OH). They mean unique maximal finite overgroups, their self-normalization, and the specified boundary-map surjectivity in equivariant homology. The conclusion is a proper cocompact oriented manifold model for the proper classifying space, pseudofree and unique up to equivariant homeomorphism. This is positive high-dimensional realization, not the target's obstruction. [Published author offprint](https://jfdavis.pages.iu.edu/papers/dl5.pdf).

Hilman–Kirstein–Kremer, arXiv:2409.02220v1, Theorem A and Corollary 1.2, remove the homological condition for an extension by an odd-prime \(C_p\), when \(\pi\) is the hyperbolic fundamental group of a closed orientable aspherical manifold of dimension at least five and the extension is pseudofree: every nontrivial finite subgroup is its own normalizer. Their positive conclusion does not include dimension four. [Primary version](https://arxiv.org/pdf/2409.02220v1).

Kremer, arXiv:2608.30620v1, Theorem B, goes beyond discrete fixed sets: for an oriented aspherical \(d\)-manifold with word-hyperbolic fundamental group, **\(d\ge6\)**, and an odd-prime subgroup \(C_p\) of the outer group, it constructs a topological action if the homotopy fixed-point space is homotopy equivalent to a PL manifold of dimension at most \((d-2)/2\). Theorem D assumes a smooth semifree isometric odd-order action on a nonpositively curved closed manifold of dimension at least six, with fixed-set codimension at least three, and concerns block homeomorphisms of the complement quotient. Neither covers arbitrary TOP four-manifolds or supplies individual nonrepresentation. The retained PDF is dated September 1, 2026; the arXiv submission is August 31. [Primary version](https://arxiv.org/pdf/2608.30620v1).

**Finite-action versus individual obstruction.** Block–Weinberger's Theorem 1.6 gives a \(C_2\) generalized-Nielsen counterexample with centerless group. Theorem 1.5 obstructs extension of specified aspherical actions, including a prime-order quotient in its construction; it is not a theorem excluding every homeomorphism in an order-three class of a four-manifold. Their Proposition 1.2 explicitly needs dimension at least five and Borel hypotheses for the torsion-free-extension realization argument. Raymond–Scott's earlier extension obstruction is discussed there, but the present construction already has the extension \(1\to G_3\to G\to C_3\to1\). It therefore cannot be explained as nonexistence of that extension. No direct reread of Raymond–Scott's original paper is claimed. [Primary published manuscript](https://math.uchicago.edu/~shmuel/Nielsen.pdf).

Arabadji–Baykur, arXiv:2304.10399v3, Theorems A and B, concern order-two subgroups of smooth mapping class groups of four-manifolds with finite fundamental group. The quotient defining those mapping classes already supplies diffeomorphism representatives; the issue is realizing the finite group relations. Their projective-twist and symplectic Torelli results likewise do not yield the aspherical TOP individual obstruction. The later publication is Advances in Mathematics 463 (2025), 110112; the retained v3 is explicitly dated October 11, 2023. [Primary version](https://arxiv.org/pdf/2304.10399v3).

**Rigidity and dimension four.** Bartels–Lück's Theorem A gives prescribed-homotopy-class TOP rigidity in dimensions at least five for their class containing hyperbolic and finite-dimensional CAT(0) groups. Proposition 0.3(ii) adds dimension four only with Freedman goodness. No such goodness hypothesis has been proved for this construction, so high-dimensional Farrell–Jones conclusions do not erase the four-dimensional obstruction. [Retained arXiv v2](https://arxiv.org/pdf/0901.0442v2).

Davis–Hillman, arXiv:2501.12512v2 (June 29, 2026), Theorems A–D and the introductory prescribed-relative-class rigidity statement, classify compact aspherical four-manifolds with elementary amenable group; the closed case has polycyclic PD4 group. Our group \(G_3\) retracts onto the nonabelian free group \(H_3\) through the restricted chamber folding map, hence is not elementary amenable. Their elementary-amenable rigidity theorem is a genuine four-dimensional positive result but does not apply. [Primary version](https://arxiv.org/pdf/2501.12512v2).

Davis–Hayden–Huang–Ruberman–Sunukjian, Theorem 1.1, constructs closed aspherical smooth four-manifold pairs that are **homeomorphic** but not diffeomorphic. It is a close comparator for reflection of local exotic behavior, but the category distinction is decisive. The retained author manuscript is dated December 10, 2024; the Annals publication is volume 204 (2026), pp. 777–794, published online September 13, 2026. [Author manuscript](https://people.math.osu.edu/davis.12/papers/dhhrs.pdf), [publication](https://annals.math.princeton.edu/2026/204-2/p06).

**Equivariant surgery.** Dovermann–Schultz, retained June 2006 version 2.0.0, Theorem I, treats degree-one equivariant normal maps of smooth simply connected \(C_p\)-manifolds, \(p\) odd, in dimension \(4n\ge8\), with closed \(2n\)-dimensional fixed sets and a fixed-set homotopy equivalence. The obstruction includes both a Wall-group class and equality of fixed-set self-intersections. It assumes actual actions and does not produce the required TOP four-dimensional class. [Primary manuscript](https://math.ucr.edu/~res/inprogress/mid0614.pdf).

Bak–Morimoto, Theorems 1.1–1.2, require compact connected oriented smooth \(G\)-manifolds of even dimension \(2k\ge6\), a simply connected target, a degree-one \(G\)-framed map and their fixed-set, boundary-homology and bundle hypotheses (A1)–(A4), with the stated projective variant. The resulting equivariant surgery criterion is not an unrestricted four-dimensional realization theorem. Neither this paper nor Dovermann–Schultz licenses removing the dimension or fixed-set assumptions just because the acting group has odd order. [Primary manuscript](https://www.math.uni-bielefeld.de/~bak/bmsurg.pdf).

**Reflection and local constructions.** Davis's Theorem 11.1.1 uses a manifold thickening of the input aspherical complex; its dimension is the thickening dimension. Proposition 11.7.1 assumes an actual finite action on the input pair and an admissible boundary action; Theorem 11.7.3 gives fixed-set/normalizer examples in dimensions at least six. These do not promote an unrealizable outer class merely from a retraction. [Author-hosted book, §§11.1 and 11.7](https://people.math.osu.edu/davis.12/davisbook.pdf). Davis's separate survey, Remark 11.6, does assert relative-to-absolute obstruction transfer, but explicitly in dimensions at least five. It neither supplies the missing ternary chamber nor resolves this dimension-four individual-order question. [Primary survey](https://people.math.osu.edu/davis.12/exotic.pdf).

Davis–Leary, Theorems 1–2, distinguish proper cocompact contractible-manifold actions, finite models for proper classifying spaces, and manifold fixed sets. Their equivariant construction starts with an actual compatible action on a pair. Avramidi–Okun–Schreve, Theorem D, preserves dimension and asphericity when reflecting a compact manifold with flag boundary and gives a retraction, with additional group properties under their hypotheses. These are powerful existing constructions, but their statements do not give the marked manifold-model-to-filling converse used here or preservation of this Homeo-image obstruction from an arbitrary retract. [Davis–Leary](https://people.math.osu.edu/davis.12/examples.pdf), [Avramidi–Okun–Schreve](https://arxiv.org/pdf/2301.06112).

Krushkal–Quinn, *Subexponential groups in 4-manifold topology*, §1.2, explicitly describes contraction across one subgrope by discarding its dual and using two parallels; repeated contractions and their intersection effects are classical. The present report does **not** claim discovery of grope contraction, the six-letter commutator operation, or its leading Lie word. The new proposed contribution is their marked finite installation with the successor obstruction, preserving the exact source ideal and reflection interfaces and giving the odd cyclic spectrum. [Published primary text](https://msp.org/gt/2000/4-1/gt-v4-n1-p14-s.pdf).

The majority argument is classical Boolean constraint theory: Allender–Bauland–Immerman–Schnoor–Vollmer, *The Complexity of Satisfiability Problems: Refining Schaefer's Theorem*, Fact 2.2, its clone table \(D_2\), and proof of Theorem 3.1(3) explain preservation under primitive-positive definitions and the majority/bijunctive connection. The elementary proof in §3 makes the exact limitation self-contained. [Author manuscript](https://people.cs.rutgers.edu/~allender/papers/csp.pdf).

**Contribution judgment requested of the parent.** The order-three height criterion is elementary transfer. The successor constraint itself is finite-state propagation, not a new combinatorial theorem. The six-linear Nakayama argument follows the source's algebra once the word and markings exist. The proposed advance is the new marked three-choice branch construction, with a 3-divisibility spectrum and the resulting order-three individual obstruction in fixed dimension four. Lemma 3.1 explains why this conclusion is not obtained by finite replication or relabeling of the old binary cap-selection mechanism. It is not a theorem excluding every imaginable alternative deduction from the corpus. Because the construction deliberately uses classical grope operations and the strongest source machinery, an independent significance review should test whether this arity change and its geometric verification are substantial enough for the requested gate. A theorem being absent verbatim from the source is insufficient by itself.

No exact duplicate of Theorem 10.1 was established by these primary comparisons. That bounded finding is not worldwide priority certification. No MathDB numerical score or featured status was invented.

## 12. Self-validation, limits, and fresh-review priorities

The deterministic script checks all 49 pairs of nonempty ternary deficiency sets and finds precisely the three successor transitions. It checks actual integer endpoint capacities in every five-edge bundle, exhausts cyclic color assignments through degree nine, propagates transitions through degree fifteen, and constructs full 30-type endpoint/cap assignments for degrees 3,6,...,60. Every positive graph has exactly \(10d\) edges with neither endpoint selected and \(20d\) with one; none has both. It verifies 20 ports per color and the exact finite body count.

The script also checks 88,560 odd-arity majority clause cases, the failed same-color 4-cycle, the truncated noncommutative Magnus expansion through degree six (32 degree-six monomials), each Brunnian specialization, the exact nonzero \(\mathfrak{sl}_2\) tensor value, and an exact nine-adjoint determinant at \(\sigma=1\), namely \(-512\). The latter is a finite check of a nonzero specialization, consistent with the imported adjoint-span theorem; it does not replace that source. An illustrative sheet-sign cancellation fixes the outer index; it is explicitly not a geometric validation.

The initial diagnostic run failed because SymPy was absent. It was replaced by standard-library rational matrix arithmetic and rerun successfully; no dependency installation or other-project change was made. The successful script and retained output are the reproducible artifacts, not the failed environment-dependent version.

These diagnostics certify only finite algebra and combinatorics. Geometry, framings, the middle module, PD duality, formal ideals and closed-manifold conclusions depend on the written proof and accepted contracts. No computer output is described as validating those topological steps.

The fresh proof review should concentrate on:

1. Lemma 4.1: replacing two marked terminal longitudinal collars by punctured-torus thickenings, preserving the transported bottom boundary-push property, six independent external conjugators, and all terminal framings.
2. Lemma 4.2 and §6: the deeper one-sided compression has a framed outgoing collar and uses only one chosen port's parallel cap sheets; at most one selected end per plumbing is sufficient.
3. §5.1: the unused upper loop is now a subtree boundary. Its nullhomotopy remains in the exterior, so the **inner** two-sheet cancellation is legitimate while the outer rim copy is fixed.
4. §7.3: all six independent conjugations, actual product-ideal membership, common algebraic edge coordinates, and full mixed nilpotents survive; no stronger geometric scope is silently assigned to ten:assignment.
5. §§8–10: all lifted chamber hypotheses, the independent-label finite covering, proper/cocompact height quotient, faithful normal-form group identification, and exact order three.

No unresolved estimate or geometric hypothesis is intentionally assumed in the proposed theorem. This is the author's proof assessment, not an independent review. If any of these extensions fails, the target theorem must be withdrawn or marked conditional; Lemmas 3.1–3.2 and the abstract height lemma alone are only technical results, not a substitute accepted finding. In particular, the finite ternary model on its own does not meet the task.

## 13. Reproducibility and seal

From the project root run:

~~~sh
python frontier/experiments/i15_odd_order_topology/checks.py
python frontier/experiments/i15_odd_order_topology/seal.py --verify
~~~

The first deterministically rewrites its own checks.json; the second verifies the report and every file in the assigned source/experiment trees without changing them. The seal excludes only itself. It checks that there are no unlisted artifacts and verifies current hashes against the retained manifest. The input snapshots are part of the seal; later changes to the parent's shared originals do not silently replace them.

The provenance and contract scripts reproduce the byte-copy and exact-statement extraction. They intentionally write only this task's source directory. The literature retrieval scripts are for fresh retrieval, which changes timestamps and may encounter revised author PDFs; they are not the retained-byte verification commands. Compare versions before replacing snapshots or resealing.

Only frontier/iterations/i15-odd-order-topology.md and frontier/{sources,experiments}/i15_odd_order_topology/ were written. No shared indexes or candidates were edited, no files staged or committed, no other projects touched, no R numbers assigned, and no agents spawned. The parent retains integration and fresh independent proof/novelty review.
