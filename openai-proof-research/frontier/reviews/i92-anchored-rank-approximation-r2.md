# I92 — independent original-proof audit of anchored rank approximation

**ORIGINAL PASS WITHOUT REPAIRS:** I90 Theorem Q90, Lemmas W, E and C, and the supporting variants (15)–(18), at their original source-relative scopes. **ORIGINAL PASS WITHOUT REPAIRS:** I88 Propositions A, A′ and B, including the codomain enlargements and strict norm slack stated there. I90's prerequisite-review verdict is correct. No original mathematical claim needed correction or an added hypothesis. There are no unresolved proof objections within these scopes.

This is an independent AI analytic review, not human peer review or formal certification. All source statements **and lower proof operations** at `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are accepted premises. Applicability and the new deductions are audited; upstream truth is not. The contribution decision belongs to the separate I93/parent gate. Eight accepted findings remain the supplied status; this report changes no count and makes no worldwide-priority claim.

## 1. Exact objects, dependencies and evidence identity

The reviewed I90 original is `frontier/iterations/i90-anchored-rank-approximation.md`, SHA-256 `5d35844a2fd42a6e5d15b756e55e53621b27b433e0bd15236ca0e2f0aab5776c`, under the original seal `89f356914c26239322fdd3f1bb42dd9a124be0d6867ce65d02e3bf1276813438`. The I88 original remains under seal `a4af4b269cef192734166e228ca2e95d6fd08ee25f03d4163a2fc4de0c9277c6`. Their complete reports, original briefs and finalized parent responses are bound directly or through the unchanged I90 inventory. Copies of the I90 report, original task brief and finalized parent response, plus the complete I92 brief, are in this review's source directory. Parent evidence replay is not used as a substitute for reading the proofs.

AGENTS was read. The four informational ledgers were read for the current objective, acceptance rules and relevant I88/I90 history; complete bytes were frozen. Only `README.md`, `frontier/README.md`, `frontier/TEN-FINDINGS.md`, and `frontier/iterations/README.md` may drift. No I91 working output or concurrent review is read or bound. No child, shared edit, old-artifact edit, staging, commit or publication was performed.

Write F for the pinned directory

`preprints/Failure-of-Bounded-Approximation-in-a-Lipschitz-Free-Space-over-a-Uniformly-Discrete-Metric-Space-September-26-2026/`.

The operative primary contracts are `build/sections/introduction.tex`, `thm:blocks`; `reduction.tex`, `prop:coefficients`; `blocks.tex`, `lem:local-limit`, `eq:parameters`, `lem:block-geometry`; `operators.tex`, `lem:finite-support`, `lem:measure-bounds`; `walks.tex`, `lem:rare-walks`, `lem:exceptional-directions`; and `tests.tex`, `lem:edge-test`, `eq:average-error`, `rem:abstract-obstruction`. The complete used proof operations were read, including the complete blocks/operators/walks/tests sections. The coefficient proof was read in full. These files are reused in place in the sealed I14 corpus, with exact hashes and passage locators in `read-manifest.json`.

There are eleven original blobs in this F family. Its `main.pdf` is a separately pinned original, not assumed identical merely from its filename. The operative PDF sections 4–6 were read through the retained I79 text, lines 626–986. The labels correspond to TeX as follows: Lemma 4.1 finite support; Lemma 4.2 measures; Lemma 5.1 rare walks; Lemma 5.3 exceptional directions; Lemma 6.1 edge tests; Theorem 1.2 block obstruction; Remark 6.2 abstract criterion. Their hypotheses and proof steps agree at the used scope. This is a scoped comparison, not a claim to have re-read every PDF proof in the corpus.

The mathematical dependency chain for Q90 is F's metric/label/graph operations and coefficient representation, followed by W and the elementary finite-dimensional envelope E. C uses the same weighted-pair part of W, plus an ordinary finite-dimensional volume cover. Q90 does not invoke finite-support perturbation, local reflexivity, the cotype companion, a sampling theorem, or an external graph algorithm. Original B alone uses local reflexivity in addition to classical Auerbach, Hahn–Banach and Banach–Alaoglu.

The primary Goucher–Kania author-hosted publisher-style paper, *Invariant means on Abelian groups capture complementability of Banach spaces in their second duals*, Theorem 2.4, states exactly the local-reflexivity interface used by B: for finite-dimensional F in X**, a map into the canonical X with norm at most 1+η fixing F∩X. The retained paper states this classical theorem with attribution to Lindenstrauss–Rosenthal; it does not prove it there. This review checks the exact external interface and B's complete deduction, and does not claim to re-prove the classical theorem from first principles. Its retained PDF/text/response metadata are immutable I88 evidence. [Primary PDF](https://users.math.cas.cz/~kania/papers/GoucherKania.pdf).

The retained Dasgupta–Drineas–Harb–Kumar–Mahoney publisher PDF, SIAM J. Comput. 38(5) (2009), §3.1, was read at its well-conditioned-basis theorem and complete proof and Auerbach discussion, with the §3.2 boundary inspected. It gives the classical bounded-coordinate background. The determinant proof of E is self-contained and does not rely on a matrix sampling conclusion or an infinite-matrix extension of that paper. [Primary PDF](https://www.cs.purdue.edu/homes/pdrineas/documents/publications/Drineas_SICOMP_09.pdf). A bounded independent web search corroborated these primary locations; search-result dates are not substituted for the retained publication metadata. No new external theorem is imported.

## 2. Metric scope and measures

Fix an **integer** p≥1 and then the entire F construction, including its chosen even Δ and integer k. The shorthand “p≥1” throughout Q90 inherits this integer scope. The quantities are

    L=10p, R=30p, K=10p(R+1), D=K+2L+5,
    B=300p²+150p+5, V=1+4pB,
    V/Δ<1/20, Q=Δ^(2L+1), H=Δ^(D+1),
    k>2ΔQH, ρ=ΔQH/k<1/2.

All are fixed before T. The theorem is not uniform over arbitrarily changing Δ or k while retaining a constant named only by p.

N_m contains **all** anchors and all vertices of G_j for j≤m. Its metric is the restriction of the full M_p metric. Scalar McShane extension proves that X_m=F(N_m) includes isometrically in X=F(M_p); it neither extends T nor permits recomputing distances after deleting future graphs. Every anchor comparison is made between domain vectors already in X_m. Increasing union density follows from the evaluations, and is used only in B.

The full metric facts match every application: attachment length R>2L prevents short state transitions through anchors; an anchor's radius-2L ball is a singleton; source-state successors lie in their original source graph. Thus a state in **any** graph or among the anchors has at most Q successors, counting self-transitions. The count is over metric points, not edge multiplicity. Multiplicity instead remains in the source-incidence count Δ. The label map is Lipschitz even along paths using anchors. Integer path lengths make distances attained despite infinite anchor degree. The actual small-ball and label bounds are not induced-graph assumptions.

The coefficient map from ℓ1 onto X has inverse norm at most two. It applies also to N_m. Every output of a finite-domain operator into full X therefore has unique absolutely summable coordinates, even with countably infinite support. Every Lipschitz function on this bounded block is bounded up to a finite additive constant. All series and pairings used below converge absolutely.

For T of norm ≤2p with all anchor errors <1, augment coefficients by

    μ_x(j)=c_x(j) for j≠o,
    μ_x(o)=1−Σ_{j≠o}c_x(j).

These are signed measures of mass one. The ℓ1 unit mass at o is different from the free-space vector δ_o=0. For any Lipschitz g the affine pairing in I90 (12) is exact. Taking the signs of all μ_x coefficients, including the coefficient at o, gives a 2-Lipschitz bounded test and

    ||μ_x||TV ≤ 1+2||Tδ_x|| ≤ V.

No tail truncation, norm attainment, positivity or probability interpretation is used. The bump has slope L/K and value L at a(x), so

    ∫b_x dμ_x ≥ L−L(2pR+1)/K ≥ 4L/5 ≥ 3L/4.

The original weaker bound is sufficient. For a source incidence x→y, centering at o and canceling the common mass gives an edge-test pairing bounded by ||T||d(x,y)≤2p. A loop gives zero. The whole derivation remains valid for X_m→X and for X_m→X_m.

## 3. Lemma W: full pairwise and countable-state audit

**Verdict: ORIGINAL PASS WITHOUT REPAIRS.** Lemma W does not require μ_x to have mass one. Its three displayed analytic hypotheses, a finite dominating positive measure, and the inherited state geometry suffice. The operator application supplies these hypotheses, including mass cancellation where needed.

The vulnerable continuation step is I90's paragraph immediately after (4). I checked its exact pair scope rather than assuming F's rootwise statement. A good pair (x,j) admits no matched n-walk. Every longer matched walk has an n-prefix, so all its positive incidence records belong to {1,…,n−1}; zero means no positive walk and is not a compatibility claim. This argument works for countable states too: a nonempty bounded set of integer lengths has a realized maximum. Actual finite branching Q additionally bounds the number of state walks of any fixed length.

For a compatible transition across e:x→y, if one pair is bad its direction is exceptional by definition. Otherwise let A_x and A_y be the maxima excluding e and its exact reverse. These sets are nonempty because Δ≥4. A positive A_y has a realizing continuation whose first incidence is not the reverse of e. Prepending e gives r_x(e,j)≥1+A_y. If A_y=0, the edge itself supplies length one. The reverse inequality is identical. If a prepend reached n, goodness of that initial pair would already be contradicted; there is no unjustified equality after truncating a positive record. If both directions were nonexceptional, their own records would be at most the competing maxima, forcing A_x≥1+A_y≥2+A_x. This is impossible. No step says that every state at either vertex is good.

Incidence identities, not distinct endpoints, justify this proof. A loop has two distinct reversed incidences even at one vertex. Parallel edges allow return through a different instance; only the exact reverse is excluded. Self-transitions and repeated states are allowed. Ties give no exceptional direction, precisely as needed for the “at most one” assertion.

For the edge test, use the original prescription b_x on S\E_e and −b_y on S\E_reverse. Across a pair j,j′ of distance <2L, positivity of b_x(j) implies

    ||h(y)−h(j′)||∞ < 1+K+2L = D−4,

and (x,j) is also compatible. The endpoint alternative excludes both prescriptions. The same holds with the roles exchanged. If neither bump is positive, both values are zero. This proves consistency even at j=j′. At distance exactly 2L the trivial height bound already applies. Within each set the slope is ≤1.

For a nonempty countable prescription set P, the infimum of v(j)+d(j,t) lies between −L and L+B. The triangle inequality gives its Lipschitz bound without assuming that the infimum is attained. At a prescribed point the data inequality gives equality with its assigned value. Clipping preserves that equality and the Lipschitz bound; for empty P the zero function is already specified. Thus no compactness or finite-minimum assumption leaks into the countable extension.

The two signed errors are bounded by 2L times **variation** on their respective exceptional sets. Their signs need not agree. If w(x)=|μ_x|(B_x), summing nonnegative absolute masses over the Δ directions gives the sharper original intermediate estimate

    average_e |μ_x|(E_e) ≤ ||μ_x||TV/Δ +(1−1/Δ)w(x).

Tonelli or finite-direction summation justifies this for countable S. Uniform vertex/uniform incidence sampling is uniform on all oriented incidences because the graph is regular. Reversal preserves it, including loop orientations, so both error terms have the same averaged bound. Dividing

    λ ≥ 3L/2−4L(V/Δ+E_m w)

by 4L gives exactly I90 (7), with constant 3/8. There is no missing factor two from signs, orientations or the TV convention.

The second potentially vulnerable step is I90 (8)–(10). Full source labels need not be determined by radius n. They are discarded in favor of the necessary own-color condition: h_i(x)=0 and compatibility imply h_i(j)≤D−4<D, hence i∈C_j, with |C_j|≤H. For a fixed initial state j there are at most Q^n state sequences, even in countable S. On the independently colored tree there are at most Δ^n nonbacktracking source paths; each visits n+1 distinct vertices. Repeated states and overlapping C_j do not destroy independence of those distinct **source colors**. The union bound is therefore a_n=(H/k)ρ^n. On the finite graph loops and repeated vertices need no product estimate: their local types are handled by TV transfer.

The event F_j is defined on a common finite space of rooted induced colored radius-n types. Existence of the walks is invariant under rooted colored multigraph isomorphism, including incidence multiplicity. States, their labels, and their metric transition graph are frozen parameters of the event. In particular one does not recompute the label of a state when evaluating the hypothetical tree type.

For the resulting function

    g(t)=min(V, Σ_j ν(j)F_j(t)),

one has w(x)≤g(t_x). The measure sum converges since ν(S)<∞. Write d_t=P_m(t)−P_tr(t). Since Σd_t=0 and Σ_{d_t>0}d_t=τ_m(n), every g valued in [0,V] satisfies Σg(t)d_t≤Vτ_m(n). This deterministic inequality holds simultaneously for all g; it can be applied after T, ν and the actual graph have selected g. It makes **no conditional independence assertion**. Finally E_tr g≤Σν(j)E_tr F_j≤ν(S)a_n. Combining with the signed lower bound proves (4) at its original finite and countable scopes.

Clipping before this transfer is indispensable to the stated error budget. Transferring every F_j separately gives ν(S)τ; transferring the uncapped sum as if bounded by V would be false. Neither incorrect step appears in the original proof.

## 4. Lemma E, dimension and Q90

**Lemma E: ORIGINAL PASS WITHOUT REPAIRS.** In a real d-dimensional normed subspace E of ℓ1(S), determinant maximization takes place in the compact unit ball of E, not the noncompact ambient ball. A nonzero maximum exists because E has a basis. Every maximizing vector has norm one; replacing one column by any unit vector shows the corresponding coordinate functional has norm at most one. Evaluation at its own basis vector makes this norm exactly one. For u=Σa_i u_i, |a_i|≤||u||1. Therefore

    |u(j)| ≤ ||u||1 Σ_i|u_i(j)|,
    Σ_j Σ_i|u_i(j)| = d.

This is pointwise domination by a finite **mass**, not finite support. The zero-dimensional case has the zero measure, as explicitly stated. The proof is valid for infinite ambient ℓ1 and is classical Auerbach geometry.

For Q90, J_0c has mass zero and ℓ1 norm at most 2||c||1. The coefficient inverse and J_0 are linear and injective. The augmented outputs lie in span{e_o}+J_0C(TX_m), of dimension at most r+1. In fact this full displayed space has dimension r+1, because its second summand has mass zero and e_o has mass one; the weaker bound used by the author is correct. There is no assumption that the affine family μ_x itself is an r-dimensional linear space. Also r is finite automatically because X_m is finite-dimensional, even when the codomain is X.

Lemma E provides ν of mass at most V(r+1) dominating every |μ_x|. Substituting λ=2p into W and using τ≤1/(40V) gives

    V(r+1)(H/k)ρ^n ≥ 3/8−1/20−V/Δ−Vτ > 1/4.

Strictness follows from the fixed strict V/Δ<1/20, even when the allowed norm or discrepancy reaches its endpoint. The anchored bump lower bound does not require an extra strict estimate at this step. Thus

    r+1 > kρ^(−n)/(4VH).

Set A=kρ^(−n)/(4VH). Since k>2ΔQH and Δ>20V, A>ΔQ/(2V)>10Q≥10. Consequently r>A−1≥A/2 and in particular r≥kρ^(−n)/(8VH). No integer rounding is mistaken for equality. Q88's p≥2, norm≤p/2 and anchor error≤1/4 are contained in Q90's hypotheses, so its constants c_p=k/(8VH), α_p=1 and n_p=2 follow with all source choices fixed.

Nonvacuity is genuine: identities of X_m have norm one and zero anchor error. For each fixed n, the source convergence of finitely many type frequencies implies τ_m(n)→0, so there are actual m satisfying the tolerance. The conclusion concerns those m and imposes a lower bound on their dimensions/possible approximant ranks. It gives no graph-size schedule, practical constants, upper bound on optimal rank, or theorem on the unbounded wedge.

## 5. All quantitative variants

**(15): ORIGINAL PASS WITHOUT REPAIRS.** The term −Vτ_m(n) remains in the right side. This is *discrepancy-threshold-free*, not a statement that discrepancy disappears. Under the same TV and bump hypotheses and edge bound λ, W and E give the displayed inequality for every τ. Keeping λ=||T|| is valid. If its right side is nonpositive the inequality still holds, but gives no useful positive rank obstruction. The original “positive right side” qualification is the usefulness condition, not an extra condition needed to prove the inequality. No extension to arbitrary norm bounds without the TV/bump inputs is asserted.

**Lemma C and (16): ORIGINAL PASS WITHOUT REPAIRS.** Let a center σ_i be within TV distance η≥0 of μ_x. The elementary coordinate inequality |μ_x(j)|≤|σ_i(j)|+|μ_x(j)−σ_i(j)| implies w(x)≤|σ_i|(B_x)+η. Summing all center variations gives ν of mass at most MW. This ν need not dominate μ_x, so C correctly reuses W's continuation/lower-bound argument and proves a separate capped upper bound, instead of applying W's domination hypothesis incorrectly. The observable min(V,η+Σν(j)F_j(t)) lies in [0,V] and dominates w. Its tree mean is at most η+MWa_n. Signed centers and countably supported centers are both allowed. A covering family for this nonempty graph is nonempty; finite TV bounds and nonnegative tolerances are the ordinary meanings of the hypotheses.

**(17): ORIGINAL PASS WITHOUT REPAIRS.** For η>0, a maximal separated subset of the radius-V ball in d dimensions is finite: disjoint open η/2 balls fit in radius V+η/2. Lebesgue volume gives M≤(1+2V/η)^d. A finite greedy maximal set is an η-net; boundary choices do not change the volume estimate. Centers belong to the original measure space E and have TV≤V. With η=1/16 and W=V, the strict remainder in the preceding section exceeds 1/4, so MVa_n>3/16. This gives M>3kρ^(−n)/(16VH), followed by the logarithmic inequality in (17), since d≤r+1 and log(1+32V)>0. The resulting bound is linear in n. An exponential net size has not been mislabeled an exponential rank bound.

**(18): ORIGINAL PASS WITHOUT REPAIRS.** Take ζ≥0 and η>0. Finite-dimensional subspaces of a Banach space have best approximations: a minimizing sequence can be confined to a bounded set in that subspace, which is compact. Hence a closest v_x∈E satisfies ||v_x||TV≤V+ζ. Cover this ball by at most (1+2(V+ζ)/η)^d centers of norm≤V+ζ; μ_x is within ζ+η of one. Inserting these values into C gives (18) exactly. Alternatively the author's ε-relaxation converges to the same inequality. The graph's finite family permits simultaneous choices without uniform-selection issues. No linear selection, positive selection, projection, local reflexivity or rank identification is assumed. In d=0 the ball is {0} with one center and the bound remains valid.

## 6. Independent check of original I88 A, A′ and B

**A passes at p≥1**, for finite support S containing o in N_m or anywhere in full M_p, and domain X_m. The common-support event has tree probability at most |S|(H/k)ρ^n. Deterministic TV transfer remains valid for the support chosen after G_m. At a root that is good for all states, the original continuation argument is exactly the specialization checked above. At bad roots all states are exceptional, giving V/Δ+Vβ. If |S|≤kρ^(−n)/(40VH), then β≤1/(20V), and the signed incidence average gives a lower bound strictly exceeding 11L/10=11p for a quantity bounded above by 2p. This contradiction yields the original strict support bound. Empty prescribed edge data are already handled by F's invoked edge-test operation; interpreting the abbreviated finite extension formula with that specified empty case does not repair an original theorem.

**A′ passes at every N≥1 and 0≤s≤N.** Choose arbitrary distinct actual points x_i≠o and any norm-one φ. The coefficient bounds make v_N=(BN)^−1Σδ_xi nonzero with norm≤1, so φ⊗v_N has rank exactly one. At least N−s selected coordinates survive outside a competing support; the lower coefficient bound gives error at least (N−s)|φ(u)|/(2BN). Supremizing over the unit ball yields the original operator-norm bound without requiring norm attainment. The strict η<1/(4B) forces s>N/2.

**B passes at p≥2, 1≤λ<p, 0≤ε<1/2**, for every finite integer r, codomain X and hence X_m. Negating eventual exclusion produces a cofinal increasing sequence of domains. Auerbach coordinates on each finite range, padded by zeros, give factors bounded by one and λ. Hahn–Banach extends only their scalar functionals. The product of the relevant weak-star compact balls has a convergent subnet; one must not demand a convergent sequence in X. At any fixed vector in the dense domain union, eventual membership and finite sums of convergent scalar products give weak-star convergence of outputs in X**. Lower semicontinuity gives norm≤λ and anchor errors≤ε. The limiting finite sum has rank≤r.

The local-reflexivity domain is the span of that range **and all anchor evaluations**. The exact primary theorem fixes the latter and has norm≤1+η. One can choose 0<η<1 with (1+η)λ≤p and (1+η)ε<1/2, including ε=0. Its composition is a forbidden finite-rank operator on X by the pinned block theorem. The r=0 case is the forbidden zero map directly. Identity maps establish finite least admissible ranks in the endomorphism statement because λ≥1. There is no claim at λ=p or quantitative m_0, and Q90 does not try to obtain its rate from this subnet argument.

## 7. Attacks using the actual source geometry

These attacks distinguish real source-compatible objects from arbitrary colored automata. They found no counterexample to the original claims.

**Diffuse rank one on this very X.** Because the anchor span is finite-dimensional and X is infinite-dimensional, Hahn–Banach supplies a norm-one φ annihilating every anchor evaluation. Choose the actual x_i and v_N from A′. Then T_N=φ⊗v_N is norm≤1, rank one, and exhibits the same support obstruction, yet kills every anchor. There is an anchor a≠o with ||δ_a||>1: take a color i outside C_o (k>H), use a source vertex of color i supplied by radius-zero convergence, and its anchor a; h_i(a)=0 while h_i(o)=D, so d(a,o)≥D>1. Thus T_N fails the anchor hypothesis explicitly. A geometrically decaying signed ℓ1 vector on infinitely many actual x_i supplies the analogous countably supported example. Its one-dimensional envelope has finite mass and infinite support. Q90 never claims to approximate either vector by a support bounded only by rank.

**The identity is an actual high-rank test.** For T=Id on X_m, μ_x is the unit mass at x. Along any nonbacktracking source walk take each state equal to the current source vertex; all compatibilities hold and transitions have distance≤1. Since Δ≥4, a walk of every finite length exists, including with loops/multiple edges. Hence (x,x) is bad and w(x)=1. This exercises the bad-pair branch with no approximation assumption violated. Its envelope cost grows with dimension, exactly where W allows this family.

**Anchored operators can actually have signed infinite tails.** In X_m choose a norm-one functional φ annihilating the anchor span; source evaluations make that span proper. Choose distinct actual points outside N_m and a signed infinite coefficient vector c supported there, with ||c||1=1/B and infinitely many coefficients of both signs. Then v=Jc has norm≤1. For the isometric inclusion I:X_m→X, set T=I+(1/2)φ⊗v. This has norm≤3/2≤2p, fixes all anchors exactly, and is injective because ||Tu||≥||u||/2. Its rank is dim X_m, while some source outputs have signed infinite tails. For any m satisfying the type tolerance it is an actual admissible Q90 example in the full-countable codomain. Thus infinite support and negative coefficients are not merely hypothetical boundary cases of the theorem; the proof handles them without truncating them. This construction does not offer a low-rank counterexample.

**A tempting anchor retraction fails the norm bound.** Define a(x) on source vertices and fix every anchor. On finite N_m its linearization is a finite-rank operator fixing anchors. For any source edge with different endpoint colors, the endpoint labels are distinct (the own-color coordinate distinguishes them). Distinct anchors have distance at least 2R: a path either uses a direct anchor edge or must leave and reenter the anchor set through two length-R attachments. Therefore this map has norm at least 2R>2p on a molecule of source-edge norm one. Such differently colored edges occur in the actual sequence by the local limit. This rules out the natural low-rank anchor-fixing candidate without treating its label quotient as a degree-Q state graph.

**Positive ties, zero records and cutoff in an actual tree neighborhood.** Put q=D−4. The finite colored tree type of radius 4D with root z of color 1 and every other vertex of color 2 has positive probability. By F's convergence it occurs in an actual G_m. Take the actual singleton state S={z}. For source vertices at distance t≤q+1 from z, h_1=t, h_2=0 except h_2(z)=1, and all other coordinates are D. Outside color witnesses cannot shorten these distances inside the specified large tree ball. Thus compatibility with z is exactly t≤q locally; the incompatible sphere at q+1 prevents a matched walk from escaping this region.

Set n=2q+1. Every such pair is good. At the root, all outgoing records equal q, so positive ties yield **no** exceptional direction. At a vertex of depth t>0, the direction toward z has record q+t, and every direction away has q−t. The inward direction is uniquely exceptional; at boundary depth q the outward records are zero. Across a root-child edge the alternative is provided at the child, not at the tied root. Choosing n=2q instead makes a boundary pair bad, illustrating the exact cutoff rule. These conclusions use only actual labels and a state self-transition, not invented compatibility flags. The positive-probability occurrence argument is analytic and supplies no practical size schedule. The diagnostic evaluates the radial formulas for p=1,…,8; it does not construct those enormous source balls.

**Adaptive transfer and signs.** The independent finite diagnostic chooses its extremizing observable after seeing both distributions, attaining exactly Vτ. It also displays a failure of uncapped transfer: P=(1/10,9/10), Q=(0,1), and raw values (100,0) have expectation gap 10, although Vτ=1/10 for V=1; clipping yields gap 1/10. This is a test of the transfer operation, not a source-compatible counterexample to W. Signed vectors with overlapping Auerbach supports verify that cancellations neither reduce the variation envelope's needed bound nor create a support claim.

These examples explain how Q90 avoids A′: bad **variation**, not the presence of any bad state, is charged; domination pays dimension times V in total mass; and clipping pays Vτ. The common envelope is allowed to remain diffuse forever. No conversion to finite coordinate support occurs.

## 8. Finite diagnostics, inventories and limits

`diagnostics.py` was independently written using direct path enumeration, rather than importing the author's record recurrence. It checks 9,488 degree-four permutation-multigraph cases on at most three vertices, 103,504 compatible endpoint alternatives, 8,400 cases with loops and 84,528 signed averaging cases. Those tiny fixtures mostly have zero good records; a separate regular nine-vertex fixture with a compatible star explicitly checks positive tied root records, unique leaf directions, and the n=2 bad / n=3 good cutoff. The limitation was noticed and addressed before sealing, not concealed.

There are also 225 adaptively chosen TV extremizers, 6,075 capped transfer cases, 81 overlapping signed-envelope cases, diffuse examples of sizes 2,7,32,257, exact parameter budgets for p=1,…,8, and 62,296 evaluations of the source-compatible radial formulas. These are meaningful finite diagnostics of the implementation and constants, not a proof for all metrics, graphs, signed measures or dimensions. The written arguments above supply the analytic verdict.

The complete corpus identity is the 13,223-entry `preprints-tree.json`: **749 manuscripts and 10,373 original blob positions**. The immutable I79 full map plus I88's original-body augmentation, not the old 719 catalogue or truncated root tree, determine the domain. The I14 inventory has 9,340 originals; I79 supplies the remaining 1,033 originals, including 776 saved PDF text extractions. All bytes are reused in place. The inherited evidence replay verifies every Git blob identity and searchable-body hash and the exact tree/map correspondence.

This review independently searched all 10,373 mapped positions with two bounded exact queries. The continuation query has 55 matching lines across eight manuscripts; the Auerbach/local-reflexivity query has eight lines across two. Ordered path/line/text records, including duplicate representations, are retained and replayed. Hits outside F are lexical screens, not imported dependencies or a claim of complete proof reading. These searches check the relevant interface vocabulary; they do not certify absence of prior art. The old I90 three search multisets are also reproduced unchanged by its verifier. Contribution comparison beyond the checked primary interfaces is left to I93.

The offline read-only verifier checks the exact I92 owned domain, frozen snapshots, immutable references and read passages; the unchanged I90 and I88 seals/domains; complete original brief/report/parent-response preservation; every original/search corpus body through the frozen I90 verifier; the two new exact search outputs; and independent diagnostics. It replays I90's six primary PDF extractions and one additional F primary PDF extraction, comparing saved text bytes. It does **not** re-extract all 776 corpus PDFs. All corpus extraction hashes are checked. Hash replay establishes evidence integrity, not mathematical truth.

Run from the repository root:

    python3 -B frontier/experiments/i92_anchored_rank_approximation_r2/verify.py

The final seal excludes only itself from the exact owned domain. Preseal validation precedes its one-time creation; no later edit or reseal is authorized. `preseal-corrections.md` records review-process corrections and their limits. No original proof was repaired. Evidence PASS and this written ORIGINAL PASS are separate claims; neither establishes substantial contribution.

**Parent handoff:** Q90 closes Q88's stated exponential rank target under the accepted source premises, with finite-domain/full-countable-codomain scope intact. W/E/C and (15)–(18) pass as originally written. I88 A/A′/B and I90's prerequisite audit pass. No mathematical objections remain at the audited scopes. Preserve the original seals and leave acceptance/counting to the separate contribution gate and parent.
