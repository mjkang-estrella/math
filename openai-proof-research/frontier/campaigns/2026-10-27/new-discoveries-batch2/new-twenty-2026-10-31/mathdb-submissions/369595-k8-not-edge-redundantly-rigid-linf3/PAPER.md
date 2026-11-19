# The complete graph K₈ is not edge-redundantly rigid in ℓ∞³

### A formally verified counterexample to a conjecture of Cruickshank, Dewar and Kitson

**Abstract.** In arXiv:2508.00134v1, Cruickshank, Dewar and Kitson conjectured that the complete graph Kₙ is edge-redundantly rigid in ℓ∞^d for every d ≥ 2 and every n ≥ 2d + 2. We show that K₈ is not edge-redundantly rigid in ℓ∞³, refuting the conjecture at d = 3 and n = 2d + 2.

The proof has two parts:
* a self-contained reduction from the analytic definitions to a finite problem: colours and orientations of the 28 edges of K₈, constrained by cut conditions and by seven forbidden four-point patterns;
* a computer-generated unsatisfiability certificate for the resulting propositional instance.

The refutation is formalised in Lean 4 with Mathlib. This covers the source definitions on the relevant domain, every bridge in the refutation, and the certificate, which is checked by kernel reduction using a reverse-unit-propagation checker proved sound in Lean. The proof uses only the standard axioms `propext`, `Classical.choice` and `Quot.sound`. We also show that Kₙ is edge-redundantly rigid in ℓ∞³ for every n ≥ 9. The case n = 9 is formalised, and the extension to n ≥ 10 is proved on paper. Among complete graphs on at least two vertices, the exact threshold in dimension three is n ≥ 9 = 2d + 3.

---

## 1. The conjecture

We summarise the definitions of [CDK, §§2.2, 2.3, 5] (arXiv:2508.00134v1). All graphs are finite and simple.

*Normed spaces.* Let X = (ℝ^d, ‖·‖_X) with unit sphere S_X. A *support functional* for x₀ ∈ S_X is a linear functional φ : ℝ^d → ℝ such that φ(x₀) = 1 and ‖φ‖*_X = 1, where ‖φ‖*_X := sup_{‖x‖_X = 1} |φ(x)|. "The norm on X is smooth at a point x₀ ∈ S_X if there exists exactly one support functional for x₀." The unique support functional is written φ_{x₀}.

*Rigid motions.* A rigid motion of the normed space X is a family of continuous paths α_x : (−1, 1) → ℝ^d, x ∈ ℝ^d, with the following properties: (i) α_x(0) = x for all x; (ii) α_x(t) is differentiable at t = 0 for all x; (iii) ‖α_x(t) − α_y(t)‖_X = ‖x − y‖_X for all t ∈ (−1, 1) and all x, y. The induced affine map η : ℝ^d → ℝ^d, η(x) = α_x′(0), is called an infinitesimal rigid motion of the normed space X. T(X) denotes the collection of infinitesimal rigid motions.

*Frameworks.* A framework in a normed space X is a pair (G, p) consisting of a graph G = (V, E) and a point p ∈ (ℝ^d)^V such that for each edge vw ∈ E, (i) the components p_v and p_w are distinct, and, (ii) the norm ‖·‖_X is smooth at the normalised vector (p_v − p_w)/‖p_v − p_w‖_X. W(G, X) is the set of such p (the well-positioned placements).

*Trivial flexes.* Each η ∈ T(X) induces u ∈ (ℝ^d)^V with u_v = η(p_v), a *trivial infinitesimal flex*.

*Rigidity matrix.* R(G, p) is the |E| × d|V| matrix with rows indexed by E and columns by V × [d]. Its (e, (v, i)) entry is φ_{v,w}(b_i) if e = vw and 0 otherwise. Here φ_{v,w} is the unique support functional at the normalised vector (p_v − p_w)/‖p_v − p_w‖_X, and b₁, …, b_d is the standard basis. "Every trivial infinitesimal flex of (G, p) lies in the kernel of the rigidity matrix R(G, p). If there are no other vectors in the kernel of R(G, p) then the framework is said to be infinitesimally rigid."

*Edge-redundant rigidity* [CDK, §5]. "A framework (G, p) in X is said to be edge-redundantly rigid if it is infinitesimally rigid and every framework obtained by deleting an edge vw from G is infinitesimally rigid. A graph G is edge-redundantly rigid in X if there exists a framework (G, p) in X which is edge-redundantly rigid."

ℓ∞^d is (ℝ^d, ‖·‖∞) with ‖x‖∞ = max_i |x_i|.

> **Conjecture 5.4** [CDK]. For every d ≥ 2 and every n ≥ 2d + 2, the complete graph Kₙ is edge-redundantly rigid in ℓ∞^d.

### What was known

* [CDK, Proposition 5.3] For every d ≥ 2, K_{2d+1} is not edge-redundantly rigid in ℓ∞^d. Its proof combines two facts. Each monochrome subgraph of an edge-redundantly rigid framework is 2-edge-connected, so each has exactly 2d + 1 edges and is a spanning cycle. But the monochrome subgraphs of a complete framework are odd-hole-free [CDK, Theorem 4.3], which rules out an odd spanning cycle.
* [CDK, Remark 5.5] The conjecture holds for d = 2. The authors take a framework of K₆ from the octahedral example of [Dew25, Example 7.10], add a seventh vertex at (0.5, 0.9), and place subsequent vertices at generic points sufficiently close to (0.5, 0.9).
* [CDK, §4] describes infinitesimal rigidity in ℓ∞^d through the *monochrome subgraphs*: G_i consists of the edges vw whose difference p_v − p_w lies in the cone over the facets ±F_i of the unit ball, i.e. has i as its strictly dominant coordinate. This goes back to Kitson's work on polyhedral norms [Kit15]. The source also proves the transitivity property [CDK, Lemma 4.2] that we use as one of our forbidden patterns.

To our knowledge the conjecture was open for every d ≥ 3. The source has one arXiv version (v1, 31 July 2025). We found no later work resolving it, but this search is bounded by the readable literature (§11).

## 2. Results

**Theorem 1.** K₈ is not edge-redundantly rigid in ℓ∞³. Consequently Conjecture 5.4 is false (d = 3, n = 8 = 2d + 2).

**Theorem 2.** For every n ≥ 9, Kₙ is edge-redundantly rigid in ℓ∞³.

**Corollary 3.** For n ≥ 2, Kₙ is edge-redundantly rigid in ℓ∞³ if and only if n ≥ 9.

*Proof of Corollary 3.* Each vertex needs at least two edges of each of the three colours (Proposition 4.4 with a singleton cut), so n − 1 ≥ 6. The case n = 7 is [CDK, Proposition 5.3], n = 8 is Theorem 1, and n ≥ 9 is Theorem 2. ∎

Theorem 1 and the case n = 9 of Theorem 2 are verified in Lean (§10). The extension of Theorem 2 to n ≥ 10 is proved on paper in §9. We make no claim for d ≥ 4. Whether K_{2d+2} fails for every d ≥ 3 is a natural question.

## 3. Notation

For d ≥ 2, x ∈ ℝ^d and k ∈ [d], write **Dom(x, k)** if |x_j| < |x_k| for every j ≠ k, i.e. k is the unique coordinate of maximal absolute value. For a placement p and an edge uv with Dom(p_v − p_u, k), we say that uv has **colour** k. Dom is symmetric under x ↦ −x, so the colour does not depend on orientation. We say that **u < v in colour k** if moreover p_u^k < p_v^k.

## 4. The geometry of ℓ∞^d

**Lemma 4.1 (support functionals).** Let x₀ ∈ ℝ^d with ‖x₀‖∞ = 1.
(a) If Dom(x₀, k), then the support functionals for x₀ are exactly the single functional y ↦ x₀_k y_k. In particular the norm is smooth at x₀.
(b) If the norm is smooth at x₀, then Dom(x₀, k) for some k.

*Proof.* For any c with |c| = 1 and any k, the functional ψ(y) = c·y_k satisfies sup_{‖y‖=1} |ψ(y)| = 1. The bound holds because |y_k| ≤ ‖y‖, and it is attained at y = e_k.

(a) If |x₀_k| = 1, then ψ(y) = x₀_k y_k has ψ(x₀) = x₀_k² = 1, so ψ is a support functional. Conversely, let φ be a support functional. Since the supremum defining ‖φ‖* equals 1 (in particular the set is bounded), |φ(y)| ≤ 1 whenever ‖y‖ = 1.
* For j ≠ k put δ = 1 − |x₀_j| > 0. The vectors y_± = x₀ ± δ e_j have y_k = x₀_k and all other coordinates of absolute value ≤ 1, so ‖y_±‖ = 1. Then 1 ± δ φ(e_j) = φ(y_±) ≤ 1, so φ(e_j) = 0.
* By linearity φ(y) = y_k φ(e_k). From φ(x₀) = 1 we get φ(e_k) = 1/x₀_k = x₀_k.

(b) The maximum ‖x₀‖ = 1 is attained at some k. If Dom(x₀, k) failed, some j ≠ k would have |x₀_j| = |x₀_k| = 1. Then y ↦ x₀_k y_k and y ↦ x₀_j y_j would be two support functionals, distinct because they differ at e_k. ∎

For d ≥ 2, Lemma 4.1 shows that a framework in ℓ∞^d is exactly a placement in which every edge has a colour. This agrees with the monochrome subgraphs of [CDK, §4]. For an edge vw of colour c the support functional is φ_{v,w}(y) = s·y_c, with s = sign(p_v^c − p_w^c), and φ_{w,v} = −φ_{v,w}. The coordinate row displayed in [CDK, Example 2.8(d)] omits the sign, which is included in [CDK, Lemma 4.5].

**Lemma 4.2 (infinitesimal rigid motions).** Every infinitesimal rigid motion η of ℓ∞^d is constant. Conversely every constant map is one.

*Proof.* Constant maps: take α_x(t) = x + tc.

Now let α be a rigid motion, and suppose Dom(z − x, k) with (z − x)_k ≠ 0. Put g(t) = α_z(t) − α_x(t). Then g(0) = z − x, g is differentiable at 0 with g′(0) = η(z) − η(x), and ‖g(t)‖ = ‖z − x‖ on (−1, 1). Since g is continuous at 0, for t near 0 both of the following hold:
* |g(t)_j| < |g(t)_k| for j ≠ k, so ‖g(t)‖ = |g(t)_k|;
* |g(t)_k − g(0)_k| < |g(0)_k|.

The first gives |g(t)_k| = |g(0)_k|, and the second then forces g(t)_k = g(0)_k. So t ↦ g(t)_k is constant near 0, and η(z)_k = η(x)_k.

Given arbitrary x, y and k, let M = 2‖x − y‖ + 1 and z = x + M e_k. Then Dom(z − x, k), and Dom(z − y, k) because (z − y)_k ≥ M − ‖x − y‖ > ‖x − y‖ ≥ |(z − y)_j| for j ≠ k. Hence η(x)_k = η(z)_k = η(y)_k. ∎

The source states dim T(ℓ∞^d) = d. Lemma 4.2 is a self-contained proof of the precise form we need, with no affine-span hypothesis.

**Lemma 4.3 (rows of the rigidity matrix).** Let (G, p) be a framework in ℓ∞^d, vw an edge of colour c, and s = sign(p_v^c − p_w^c). For every u ∈ ℝ^{V×[d]}, (R(G, p)u)_{vw} = s·(u_{(v,c)} − u_{(w,c)}).

*Proof.* Only the columns (v, i) and (w, i) contribute, with entries φ_{v,w}(b_i) = s[i = c] and φ_{w,v}(b_i) = −s[i = c] (Lemma 4.1). ∎

**Proposition 4.4 (cut condition).** Let (Kₙ, p) be an edge-redundantly rigid framework in ℓ∞^d. Then:
(i) every pair u ≠ v has a colour;
(ii) for every edge uv, every cut ∅ ≠ S ⊊ V and every colour k, there is an edge ab ≠ uv with a ∈ S, b ∉ S and colour k.

*Proof.* (i) is Lemma 4.1(b) applied to the framework condition.

(ii) Suppose not, and let H = Kₙ − uv. Define U ∈ ℝ^{V×[d]} by U_{(x,i)} = 1 if i = k and x ∈ S, and 0 otherwise. Take an edge vw of H with colour c. By Lemma 4.3 its row of R(H, p)U is s(U_{(v,c)} − U_{(w,c)}). This vanishes in both cases:
* if c ≠ k, both terms are 0;
* if c = k, the edge vw does not cross S by assumption.

So U lies in the kernel of R(H, p). Since (H, p) is infinitesimally rigid, the displacement x ↦ (U_{(x,i)})_i equals η∘p for some η ∈ T(ℓ∞^d). By Lemma 4.2, η is constant, so U_{(a,k)} = U_{(b,k)} for a ∈ S and b ∉ S, i.e. 1 = 0. ∎

Equivalently, every colour class is a connected, bridgeless spanning subgraph. The refutation uses only the cut form. The converse is used for Theorem 2.

**Proposition 4.5 (converse).** Let (Kₙ, p) be a framework in ℓ∞^d. Suppose that for every colour k, the colour-k edges of Kₙ form a connected spanning graph, and remain so after deleting any one edge. Then (Kₙ, p) is edge-redundantly rigid.

*Proof.* Let H be Kₙ or Kₙ − e, and let u be in the kernel of R(H, p). By Lemma 4.3, u_{(v,c)} = u_{(w,c)} for every edge vw of H of colour c. By connectivity, x ↦ u_{(x,k)} is constant for each k. So the displacement is a constant vector t, which is the trivial flex of the translation α_x(t′) = x + t′t. ∎

## 5. Seven forbidden four-point patterns

Points q₀, …, q₃ ∈ ℝ³ (coordinates x, y, z) carry a *signed pattern*: a list of entries "pair ab has colour c and orientation s". An entry means s·(q_b^c − q_a^c) > |q_b^j − q_a^j| for both j ≠ c. We write a <_c b for the entry with s = + on the pair (a, b), and use ">" for s = −.

**Lemma 5.1.** None of the following seven patterns is realisable by four points in ℝ³:

| | pattern | reason |
|---|---|---|
| R₀ | 0 >ₓ 1, 0 <ₓ 2, 1 >ₓ 2 | q₂ˣ > q₀ˣ > q₁ˣ > q₂ˣ |
| R₁ | 0 >ₓ 1, 0 <ₓ 2, pair 12 of colour y | transitivity, see below |
| R₂ | 0 >ₓ 1, 0 <ₓ 2, 1 >ₓ 3, 2 <ₓ 3 | q₂ˣ > q₀ˣ > q₁ˣ > q₃ˣ > q₂ˣ |
| R₃ | 0 >ₓ 1, 0 <ₓ 2, 1 >ₓ 3, pair 23 of colour y | transitivity twice |
| R₄ | 0 >ₓ 1, 0 <ₓ 2, 1 >_y 3, 2 <_y 3 | q₂ − q₁ is x-dominant and q₁ − q₂ is y-dominant |
| R₅ | 0 >ₓ 1, 0 >_y 2, 1 <_y 3, 2 <ₓ 3 | alternating four-cycle |
| R₆ | 0 >ₓ 1, 0 >_y 2, 0 >_z 3, 1 >_z 2, 1 <_y 3, 2 >ₓ 3 | three colours on K₄ |

The colour-y entry in each of R₁ and R₃ can have either orientation. We take the negative orientation for each signed representative in §6. Reflection in y gives the other orientation.

*Proofs.*
* *Transitivity* [CDK, Lemma 4.2]. If a − b and b − c both have dominant coordinate x with positive x-component, then so does a − c. Indeed (a − c)ˣ = (a − b)ˣ + (b − c)ˣ > |(a − b)^j| + |(b − c)^j| ≥ |(a − c)^j| for j ≠ x.
* R₁: by transitivity q₂ − q₁ = (q₂ − q₀) + (q₀ − q₁) is x-dominant, contradicting colour y.
* R₃: by transitivity twice, q₂ − q₃ is x-dominant.
* R₄: by transitivity q₂ − q₁ is x-dominant, while q₁ − q₂ = (q₁ − q₃) + (q₃ − q₂) is y-dominant.
* R₅: put D = (q₀ − q₁) + (q₃ − q₂) = (q₀ − q₂) + (q₃ − q₁). The two x-entries give Dˣ > |(q₀ − q₁)^y| + |(q₃ − q₂)^y| ≥ |D^y|, and the two y-entries give D^y > |D^x| in the same way. This is a contradiction.
* R₆: choose one inequality from each entry:
  * q₀ˣ − q₁ˣ > q₀^y − q₁^y,
  * q₀^y − q₂^y > q₀^z − q₂^z,
  * q₀^z − q₃^z > q₀ˣ − q₃ˣ,
  * q₁^z − q₂^z > q₂ˣ − q₁ˣ,
  * q₃^y − q₁^y > q₁^z − q₃^z,
  * q₂ˣ − q₃ˣ > q₃^y − q₂^y.

  Each holds because |t| ≥ ±t. Their differences sum to 0 identically, which gives 0 > 0. ∎

Each pattern can be transformed by a relabelling of the four points, a permutation of the coordinates and independent reflections of coordinates. These are isometries of ℓ∞³, and they preserve colours and transform orientations. Lemma 5.1 therefore forbids every image. The images of R₀–R₆ give 930 labelled patterns on K₄. The independent review derived the same minimal forbidden set from scratch by exhaustive exact LP over all partial signed patterns.

## 6. The propositional instance

Label the vertices of K₈ by 0, …, 7 and number its 28 edges uv (u < v) lexicographically by e(u, v), starting at 0. There are 112 variables:
* c_{uv,k} = 1 + 3e(u,v) + k for k ∈ {0, 1, 2}, meaning "uv has colour k";
* σ_{uv} = 85 + e(u,v), meaning "u < v in the colour of uv".

Every clause is produced by a typed *provenance record*:

| family | records | clause | soundness |
|---|---|---|---|
| ALO | (u, v) | c_{uv,0} ∨ c_{uv,1} ∨ c_{uv,2} | Prop. 4.4(i) |
| AMO | (u, v, a < b) | ¬c_{uv,a} ∨ ¬c_{uv,b} | Dom is unique |
| CUT | (S, k, u, v), 0 < S < 255 a bit mask | ⋁ c_{ab,k} over edges ab ≠ uv crossing S | Prop. 4.4(ii) |
| PAT | (r, f, τ, ε), where r ∈ {0,…,6}, f : {0,1,2,3} → V is injective, τ ∈ S₃ and ε ∈ {±1}³ | one clause, the disjunction of the negations of all colour and orientation literals of the transformed pattern | Lemma 5.1 |
| ANCHOR | j ∈ {0..10} | one unit clause (below) | Lemma 6.2 |

PAT clauses in detail. For an entry (a, b, c, s) of the signed representative R_r, put x = f(a), y = f(b), and uv = {x,y} with u < v. The transformed colour literal is c_{uv,τ(c)}. Set ρ = s·ε_c if x < y and ρ = −s·ε_c if y < x. The transformed orientation literal L is σ_{uv} when ρ = +1 and ¬σ_{uv} when ρ = −1. The entry contributes ¬c_{uv,τ(c)} and ¬L to the single PAT clause.

The generator emits all ALO and AMO records, the CUT records for the 127 cuts with vertex 7 ∉ S and every crossing edge uv, all PAT records, and the ANCHOR records. The Lean predicate `Base` allows all nonempty proper cut masks and any omitted edge. The DIMACS generator uses the indicated subset, which suffices for the refutation. After removing duplicates, its 53,127 distinct clauses comprise 28 ALO, 84 AMO, 5,376 CUT, 47,628 PAT and 11 ANCHOR. Its clause set equals the independently derived CNF of the review.

The anchor literals are:
* c_{01,0}, c_{02,0}, c_{03,0}, c_{04,1}, c_{05,1}, c_{06,2}, c_{07,2};
* σ₀₁, σ₀₂, σ₀₄, σ₀₆.

**Lemma 6.1 (soundness).** Let p ∈ (ℝ³)⁸ satisfy (i) and (ii) of Proposition 4.4 and the anchor conditions:
* Dom(p_w − p₀, 0) for w = 1, 2, 3; Dom(p_w − p₀, 1) for w = 4, 5; Dom(p_w − p₀, 2) for w = 6, 7;
* p₀⁰ < p₁⁰, p₀⁰ < p₂⁰, p₀¹ < p₄¹, p₀² < p₆².

Then the assignment c_{uv,k} := Dom(p_v − p_u, k), σ_{uv} := "p_u^c < p_v^c for the colour c of uv" satisfies every clause of every valid record.

*Proof.* Take the families in turn. ALO and AMO hold by (i) and the uniqueness of the dominant coordinate. CUT is (ii) restated. ANCHOR is the anchor hypothesis.

For PAT, suppose every literal of the clause is false. For each entry, the false negated colour and orientation literals imply that Dom(p_{f(b)} − p_{f(a)}, τ(c)) holds and that s·ε_c·(p^{τ(c)}_{f(b)} − p^{τ(c)}_{f(a)}) > 0. Thus the points q_i^c := ε_c p^{τ(c)}_{f(i)} satisfy s(q_b^c − q_a^c) = |q_b^c − q_a^c| > |q_b^j − q_a^j| for every j ≠ c, since τ is injective. This realises R_r, contradicting Lemma 5.1. ∎

**Lemma 6.2 (symmetry breaking).** If some p ∈ (ℝ³)⁸ satisfies (i) and (ii) of Proposition 4.4, then some p′ satisfies (i), (ii) and the anchor conditions.

*Proof.* For a vertex permutation π, a coordinate permutation τ and signs ε, the placement p′_v^c = ε_c p^{τ(c)}_{π(v)} again satisfies (i) and (ii). Colours are transported by τ, and cuts by π.

Apply (ii) to the cut {0}. First use any edge 0w to obtain one neighbour b₁ of colour k. Then use the edge 0b₁ to obtain a second neighbour b₂ ≠ b₁. So vertex 0 has at least two neighbours of each colour. Its 7 neighbours are partitioned by colour, so some colour k₀ has at least three: a₁, a₂, a₃.

Among a₁, a₂, a₃, two have the same orientation relative to 0 in coordinate k₀; call them x, y and the third z.
* Let τ be the transposition (0 k₀). Pick neighbours b₁, b₂ of colour τ(1) and c₁, c₂ of colour τ(2).
* Choose ε₀ = ±1 so that x and y lie above 0 after reflection, and ε₁, ε₂ so that b₁ and c₁ lie above 0. Orientations are strict because a dominant coordinate difference is nonzero.
* Neighbours of different colours are distinct, so π = (0, x, y, z, b₁, b₂, c₁, c₂) is a permutation.

Then p′ is anchored. ∎

## 7. The unsatisfiability certificate and how it is checked

*Generation (untrusted).* CaDiCaL 1.9.5 (through PySAT) proves the instance unsatisfiable in 0.3 s and emits a DRAT proof of 57,872 lines. drat-trim verifies it in backward mode (`s VERIFIED`) and outputs an LRAT proof:
* 12,876 clause additions, all RUP (no RAT);
* 257,429 unit-propagation hints, at most 65 per addition;
* 2,064 input clauses used: 1,666 PAT, 289 CUT, 77 AMO, 21 ALO and all 11 ANCHOR.

The pipeline reproduced the same bytes with the supplied tools and settings. The file hashes are listed in REPORT.md §4.

*Kernel checking.* The trusted base is Lean 4.34.1 and the pinned upstream Mathlib and dependency build (§11). For the checker, the positive literal for variable v is encoded as 2v and its negation as 2v + 1. The checker `Rup.rupCheck C Hs` is an ordinary Lean function:
* it stores the negations of the literals of C in a bit set (a natural number);
* it processes the hint clauses in order. Each must be *unit* (no literal true, exactly one not false), in which case that literal is added, or *conflicting* (all literals false);
* it succeeds at the first conflict.

The theorem `Rup.rupCheck_sound` proves: if rupCheck C Hs = true and an assignment satisfies every clause of Hs, then it satisfies C. The invariant is that every literal on the trail is true under any assignment that satisfies the hints and falsifies C.

The certificate is compiled into Lean as follows:
* every used input clause becomes a constant i_N together with a theorem
  `si_N : ∀ α, Base α → Sat α i_N`. Here `Base α` says that α satisfies the clause of every valid provenance record. The proof evaluates `Prov.valid π_N` and `Prov.clause π_N = i_N` in the kernel, so no clause of the DIMACS file is trusted;
* every LRAT addition N becomes a constant d_N and a theorem
  `sd_N : ∀ α, Base α → Sat α d_N`. It is proved by applying `rupCheck_sound` to the explicit list of hint constants (the check `rupCheck d_N [h₁, …] = true` is discharged by `decide +kernel`) and to the theorems for the hints;
* the last addition is the empty clause, which gives `K8.Cert.cert_unsat : ∀ α, Base α → False`.

The 8 generated modules hold 91,804 lines. They compile in 236.5 s and kernel-recheck (leanchecker) in 95.4 s on one core. The largest module peaks at 2.0 GiB.

*Independent reproduction.* In a working copy of the packet, regenerate the certificate with PySAT 1.9.dev23 (CaDiCaL 1.9.5) and the 2024 drat-trim binary identified by sha256 `3dd03e25d2ce60b45adecbbd21302658bf5e264b8b7d96739ead551000885455`:

```sh
python3 -I certificate/k8_cnf.py certificate/k8
python3 certificate/k8_solve.py certificate/k8.cnf certificate/k8.drat
drat-trim certificate/k8.cnf certificate/k8.drat -L certificate/k8.lrat
python3 -I certificate/k8_lean_cert.py 2200
```

Compare the regenerated manifest and module hashes with the tracked
`certificate/manifest.json`. The generator rewrites the eight generated
modules in `lean/`. The original replay uses Lean 4.34.1 and the pinned
Mathlib dependencies recorded in the Lean source appendix. A certificate from
another solver can be used by the generator if its converted LRAT trace
contains only RUP additions with positive hint IDs.

## 8. Proof of Theorem 1

Suppose (K₈, p) is edge-redundantly rigid in ℓ∞³.
1. By Proposition 4.4, p satisfies (i) and (ii).
2. By Lemma 6.2 we may assume p is anchored.
3. By Lemma 6.1 the induced assignment satisfies `Base`.
4. By §7 no assignment does.

This contradiction proves the theorem. Conjecture 5.4 with d = 3 and n = 8 asserts the opposite. ∎

## 9. Kₙ for n ≥ 9 (Theorem 2)

*n = 9 (formally verified).* Take the placement

P₉ = (13,5,10), (15,−3,16), (−2,−8,7), (19,−9,12), (−1,−11,8), (7,3,−2), (9,−17,0), (0,0,−5), (−2,−4,−3)

(points 0–8). Every pair has a unique dominant coordinate. The colour classes, with 12 edges each, are:
* x: 02 08 12 14 23 26 34 37 38 46 57 58;
* y: 01 03 04 06 13 24 25 45 56 67 68 78;
* z: 05 07 15 16 17 18 27 28 35 36 47 48.

Each colour class remains connected after deleting any single edge. So (K₉, P₉) is edge-redundantly rigid by Proposition 4.5. In Lean, the dominance facts are checked over the integers and connectivity by a reachability iteration, both by kernel evaluation (`CDK.K9.k9_edgeRedundantlyRigid`).

*n ≥ 10 (paper proof, not formalised).* This follows the source's Remark 5.5. Let (K_m, p) be edge-redundantly rigid with m ≥ 9 and colour classes as in Proposition 4.5. Fix a vertex v* and add a vertex x at a point p_x with two properties:
* p_x is so close to p_{v*} that Dom(p_x − p_w, k) holds whenever Dom(p_{v*} − p_w, k) holds, for every old w ≠ v*. Dom is an open condition, so all points of a small ball qualify;
* For each pair of distinct coordinates i and j, choose p_x outside both hyperplanes (p_x − p_{v*})_i = ±(p_x − p_{v*})_j. Their finite union has empty interior, so this choice is possible inside the small ball. The edge xv* then has a nonzero, uniquely dominant coordinate.

Then x copies the colours of v*, so it has at least two edges of every colour into the old vertices (v* has at least two of each colour; take a singleton cut). Now take a cut of the new vertex set:
* if it separates the old vertices, the old edges already supply two crossing edges of each colour;
* otherwise x is alone on its side, and its ≥ 2 edges of each colour all cross.

So every cut of K_{m+1} is crossed by at least two edges of every colour. Hence every colour class remains connected after deleting any one edge, and (K_{m+1}, p) is edge-redundantly rigid by Proposition 4.5. It again has the cut property, so induction from m = 9 completes the proof. ∎

## 10. Map from the argument to the Lean development

| Step | Declaration | Module |
|---|---|---|
| Definitions of §1 (dual norm, support functional, smoothness, rigid motion, T(X), framework, W(G,X), trivial flex, rigidity matrix, infinitesimal rigidity, edge-redundant rigidity, ℓ∞^d, Kₙ, Conjecture 5.4) | `CDK.dualNorm`, `CDK.IsSupportFunctional`, `CDK.IsSmoothAt`, `CDK.RigidMotion`, `CDK.IsInfRigidMotion`, `CDK.IsFramework`, `CDK.W`, `CDK.IsTrivialFlex`, `CDK.rigidityMatrix`, `CDK.IsInfRigid`, `CDK.IsEdgeRedundantlyRigidFramework`, `CDK.EdgeRedundantlyRigidIn`, `CDK.EdgeRedundantlyRigid`, `CDK.completeGraph`, `CDK.Conjecture` | CdkDefs |
| Lemma 4.1 | `CDK.dom_of_smooth`, `CDK.support_formula`, `CDK.supportFunctional_eq`, `CDK.K9.smooth_of_dom` | LinfBridge, K9Positive |
| Lemma 4.2 | `CDK.infRigidMotion_const`, `CDK.K9.isInfRigidMotion_const` | LinfBridge, K9Positive |
| Lemma 4.3 | `CDK.mulVec_edge` | LinfBridge |
| Proposition 4.4 | `CDK.indicator_in_kernel`, `CDK.good_of_edgeRedundant` (assembled into `K8.Good` in `CDK.not_edgeRedundantlyRigid_K8`) | LinfBridge, K8Comb, K8Main |
| Proposition 4.5 (for K₉) | `CDK.K9.infRigid_of` | K9Positive |
| Lemma 5.1 | `K8.reps`, `K8.rep_infeasible` | K8Cnf, K8Patterns |
| §6 instance | `K8.Prov`, `K8.Prov.clause`, `K8.Prov.valid`, `K8.Base` | K8Cnf |
| Lemma 6.1 | `K8.assign`, `K8.base_of_good` | K8Sound |
| Lemma 6.2 | `K8.transform`, `K8.good_transform`, `K8.exists_anchored` | K8Wlog |
| RUP checker | `Rup.rupCheck`, `Rup.rupCheck_sound` | RupCore |
| §7 certificate | `K8.Cert.cert_unsat` | K8Cert00–K8Cert07 (generated) |
| Theorem 1 | `CDK.k8_no_good`, `CDK.not_edgeRedundantlyRigid_K8`, `CDK.not_conjecture` | K8Main |
| Review endpoint | `Review369595.k8_counterexample`, `Review369595.cdk_source_refuted` | Review369595 |
| Theorem 2, n = 9 | `CDK.K9.k9_edgeRedundantlyRigid` | K9Positive |

`#print axioms` for every endpoint lists only `propext`, `Classical.choice`, `Quot.sound` (`K8.Cert.cert_unsat`: `propext`, `Quot.sound`). No `native_decide`, `bv_decide`, `Lean.ofReduceBool`, `implemented_by`, `sorry` or added axiom is used. A clean rebuild from an empty build directory compiles all 20 modules in 255 s CPU and kernel-rechecks them in 116 s (REPORT.md §5). The hand-written sources are reproduced in LEAN-SOURCE-APPENDIX.md.

## 11. Limits

* **Computer assistance.** Theorem 1 rests on a certificate with 12,876 derived clauses. The certificate is checked by the Lean kernel through a checker whose soundness is a Lean theorem. Each input clause used is re-derived in the kernel from a provenance record whose soundness is also a Lean theorem. The generator, solver, drat-trim and Python scripts are untrusted. The trusted base is the Lean 4.34.1 kernel and the imported Mathlib and dependency build identified in PINS.json. The clean replay re-checks all 20 project modules and accepts the upstream oleans as inputs.
* **Faithfulness of the definitions.** The Lean definitions agree with [CDK, §§2.2, 2.3, 5] on the source domain. The general interfaces take a real normed space and, where needed, a supplied family of vectors. Every endpoint uses the standard basis of ℓ∞^d = (Fin d → ℝ, sup norm). The support functional is selected by choice and agrees with the source at every smooth unit vector. A framework of a graph with no edges imposes no placement condition. In dimension three, p_v = (v,0,0) already gives a well-positioned K₈ placement, and the formal K₉ theorem gives an edge-redundantly rigid placement under the same definitions.
* **Sources read.** Only arXiv:2508.00134v1 was read; arXiv lists no other version. The independent review reports a journal version, Linear Algebra Appl. 739 (2026) 10–42. We have not read it and cannot confirm that Conjecture 5.4 appears there unchanged. The literature search for a prior resolution relied on the review's search and the source; it is bounded by the publicly readable literature.
* **Scope.** Nothing is claimed for d ≥ 4. The extension of Theorem 2 to n ≥ 10 is proved on paper only.

## Acknowledgement

The counterexample was found computationally within the MathDB campaign, and independently reviewed (signed CNF re-derived from scratch, certificates re-checked) before this formalisation.

## References

[CDK] James Cruickshank, Sean Dewar, Derek Kitson. *Algebraic connectivity in normed spaces.* arXiv:2508.00134v1, 31 July 2025. (Journal version reported as Linear Algebra Appl. 739 (2026) 10–42; not read.)

[Dew21] Sean Dewar. *Equivalence of continuous, local and infinitesimal rigidity in normed spaces.* Discrete Comput. Geom. 65 (2021) 655–679.

[Dew25] Sean Dewar. *Uniquely realisable graphs in polyhedral normed spaces.* arXiv:2504.02139 (2025).

[Kit15] Derek Kitson. *Finite and infinitesimal rigidity with polyhedral norms.* Discrete Comput. Geom. 54(2) (2015) 390–411.

[KL20] Derek Kitson, Rupert H. Levene. *Graph rigidity for unitarily invariant matrix norms.* J. Math. Anal. Appl. 491(2) (2020) 124353.

[BFFFFP24] Armin Biere, Tobias Faller, Katalin Fazekas, Mathias Fleury, Nils Froleyks, Florian Pollitt. *CaDiCaL 2.0.* Computer Aided Verification (CAV 2024), LNCS 14681, 133–152.

[IMM18] Alexey Ignatiev, Antonio Morgado, Joao Marques-Silva. *PySAT: A Python toolkit for prototyping with SAT oracles.* Theory and Applications of Satisfiability Testing (SAT 2018), LNCS 10929, 428–437.

[WHH14] Nathan Wetzler, Marijn J. H. Heule, Warren A. Hunt Jr. *DRAT-trim: Efficient checking and trimming using expressive clausal proofs.* SAT 2014, LNCS 8561, 422–429.

[CHHKS17] Luís Cruz-Filipe, Marijn J. H. Heule, Warren A. Hunt Jr., Matt Kaufmann, Peter Schneider-Kamp. *Efficient certified RAT verification.* Automated Deduction (CADE-26, 2017), LNCS 10395, 220–236.

[MU21] Leonardo de Moura, Sebastian Ullrich. *The Lean 4 theorem prover and programming language.* Automated Deduction (CADE-28, 2021), LNCS 12699, 625–635.

[Mathlib20] The mathlib Community. *The Lean mathematical library.* Proc. 9th ACM SIGPLAN Int. Conf. on Certified Programs and Proofs (CPP 2020), 367–381.
