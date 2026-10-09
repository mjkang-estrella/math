# Frontier scout: algebraic and complex geometry

**Parent status: provisional scout, not accepted findings.** Independent reviews of Theorem A/Lemma C and Theorem B/B1 are active, together with a separate attempt to construct the missing Mumford cycles. All uses of “proved” below are the scout's claims awaiting that review. The parent reproduced the exact tensor-closure ranks (5 → 7 → 8, Lefschetz-only 3), which verifies finite algebra only. Neither a locus comparison nor an unclosed conditional reduction fulfills the user's requested significant new theorem.

Research date: 2026-10-08. Upstream: [openai/math at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb). All theorems in that revision are taken as true, as instructed. Withdrawn manuscripts are not. Every new deduction below is checked independently. First-pass findings F001–F010 and the archived proposals are not reused.

## 0. Bottom line

**No landmark or celebrated problem in this domain is resolved here.** The only MathDB *landmark* problem in algebraic geometry is the Hodge conjecture. The only *celebrated* one is the Jacobian conjecture, which MathDB already marks claimed solved. I make no claim on either in general.

The new contributions are two exact frontier theorems with complete proofs, one algebraicity lemma, and a set of attempts on other targets that end at a stated obstruction.

| ID | Statement (short form) | Kind | Novelty status |
|---|---|---|---|
| **A** | For a K3 surface with ρ = 16, the corpus K3 locus and Floccari's published locus are described exactly by the even Clifford algebra C⁺(T). Together they cover exactly the surfaces whose C⁺(T) is unramified at every place above an odd prime. The two loci differ only when 2 splits in K = ℚ(√−det T). The corpus adds new cases precisely when C⁺(T) ≅ M₂((−1,−1)_K). There are explicit ρ = 16 surfaces outside both loci, and for those KS(S) is isogenous to B², with B a simple abelian 8-fold carrying quaternionic multiplication. | Proved theorem (lattice/Brauer computation plus pinned statements), with exact-arithmetic cross-checks | New to this project. I did not find this comparison in the corpus or in Floccari. Not certified new to the literature. |
| **A′** | Rational HC holds on every self-power of every projective K3 surface with ρ ≥ 17, and rational **GHC** also holds there; both transfer to Hilbert schemes and moduli spaces of sheaves. | Corollary of A | HC alone **already follows from published work** (Floccari, G&T 2026, Thm 5.11, plus the Witt-index step in §4). GHC uses the corpus. |
| **C** | Every rational Hodge *similitude* T_{S₁} → T_{S₂} between K3 surfaces on the corpus locus is algebraic. Consequently HC holds for S₁ × S₂ when End_Hdg(T_{S₁}) = ℚ. | Proved lemma | New to this project. It recovers a small, honest piece of the **withdrawn** corpus claim on products of K3 surfaces. |
| **B** | HC on every self-power of every complex abelian variety of dimension ≤ 5 is **equivalent** to one explicit statement: for each Mumford-type fourfold A, the multiplication by the cubic field F = End_Hdg(H²_prim(A,ℚ)) is induced by cycles on A × A. That is two exceptional classes in H⁴(A × A). Every other case holds. | Proved reduction (invariant theory plus an exact closure computation) plus assembly | The assembly half is a direct combination of corpus and Moonen–Zarhin. The reduction to A × A is new to this project. Novelty unverified. |

What remains open is the Hodge conjecture for Mumford fourfolds (on A × A, see §5.4) and for the ρ = 16 quaternionic-8-fold K3 surfaces (§4.4). For both I give the exact missing input and why the corpus does not supply it.

## 1. Sources, pinning and method

- Rules: `openai-proof-research/AGENTS.md`. Revision: `sources/upstream.json`. Catalogue: `sources/CONTENTS.md`. Complete path list: `sources/preprints-tree.json`.
- **Important pin fact:** the preprint tree has 749 directories, while CONTENTS lists 719 manuscripts. The 30 extra directories are earlier dated versions plus **three withdrawal notices**. All three are pinned at this revision (archived manuscript revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`):
  - [The rational Hodge conjecture for products of K3 surfaces (withdrawn Oct 6)](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-rational-Hodge-conjecture-for-products-of-K3-surfaces-October-4-2026/hodge-conjecture-products-k3.pdf)
  - [Algebraicity of Kuga–Satake correspondences for K3 surfaces (withdrawn)](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Algebraicity-of-Kuga-Satake-Correspondences-for-K3-Surfaces-October-3-2026/manuscript.pdf)
  - [Algebraicity of Weil classes on split abelian eightfolds (withdrawn)](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Algebraicity-of-Weil-classes-on-split-abelian-eightfolds-September-18-2026/paper.pdf). This one has a sign error: the signed double-point count is −2m rather than 0, so the Eliashberg–Murphy cancellation hypothesis fails.

  MathDB's Hodge conjecture page (#315851) still lists "products of K3 surfaces" as OpenAI partial progress. **That claim is withdrawn at the pinned revision** and must not be used.
- Pinned manuscripts actually read (raw base `https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/`):
  - `The-rational-Hodge-conjecture-for-CM-abelian-varieties-October-6-2026/paper.pdf`: Thm 1.1, Cor 8.2–8.4.
  - `Weil-classes-and-Hodge-classes-on-abelian-powers-October-6-2026/paper.pdf`: Thms 1.1–1.2, Lemma 2.1, §1.2.
  - `Abelian-covers-Gale-correspondences-and-the-Hodge-conjecture-for-powers-October-6-2026/paper.pdf`: Thms 1.1–1.2, Prop 3.3, §8.
  - `Algebraic-Kuga-Satake-correspondences-and-Hodge-conjectures-on-a-K3-quadratic-locus-September-30-2026/paper.pdf`: Thms 1.1–1.2, Lemma 1.3, Prop 2.1, Lemma 9.3, Prop 9.4, Cor 9.5.
  - `A-Conditional-Reduction-for-Algebraic-Kuga-Satake-Correspondences-September-10-2026/paper.pdf`
  - `Fujitas-freeness-conjecture-September-23-2026/Fujitas-freeness-conjecture-September-23-2026.pdf`: Thm 1.1, Prop 3.2, §6.
  - `Canonical-ampleness-of-compact-hyperbolic-Kahler-manifolds-September-23-2026/canonical-ampleness.pdf`: Thm 1.1, §§3, 7, 9.
  - `Every-complex-K3-surface-is-Oka-September-23-2026/paper.pdf`: Thm 1.1, §§1–2.
  - `Milnes-rationality-…`, `Blochs-Conjecture-…`, Zilber–Pink papers: skimmed for scope only.
- External literature consulted: Moonen–Zarhin, [*Hodge classes on abelian varieties of low dimension*](https://arxiv.org/abs/math/9901113), Math. Ann. 315 (1999), Thms 0.1–0.2. S. Floccari, [*K3 surfaces associated with varieties of generalized Kummer type*](https://msp.org/gt/2026/30-3/gt-v30-n3-p08-p.pdf), Geom. Topol. 30 (2026) 1129–1154, Thms 1.2, 1.3, 5.11, Lemma 5.4. Varesco, [arXiv:2203.09778](https://arxiv.org/abs/2203.09778). Markman, [arXiv:2509.23403](https://arxiv.org/abs/2509.23403), whose dimension ≤ 5 corollary is cited inside the corpus Weil paper as [26, Cor 1.3].
- Catalogue and hashes: `frontier/sources/geo_CATALOGUE.md`. Files are in `frontier/sources/geo_pdf/` (pinned PDFs plus text), `geo_lit/` and `geo_mathdb/` (raw API JSON).
- **MathDB method.** I used the public JSON API: `/api/search/suggestions?q=`, `/api/search?q=`, `/api/posts?importance=<band>&tag=<tag>`, `/api/posts/<uuid>`. Problem pages are `https://mathdb.com/p/<number>`. The server lists the valid importance bands as **landmark, celebrated, erdos, named, corpus**; I invented no scores. The landmark band has 6 items (the Millennium problems). The celebrated band has 40 items, and its only algebraic-geometry entry is the Jacobian conjecture, which is claimed solved. The tag `algebraic-geometry` with band `named` has 636 items, all saved.

## 2. MathDB targets in this domain and their actual status after accepting the corpus

| MathDB # | Title (band) | MathDB status | Status after corpus and literature |
|---|---|---|---|
| [315851](https://mathdb.com/p/315851) | Hodge conjecture (**landmark**) | claimed progress | Open. Corpus proves CM abelian varieties; all powers of abelian varieties of dim ≤ 5 with an imaginary-quadratic action; split Weil sixfolds; Hodge-generic abelian-cover Jacobians; Fermat and diagonal complete intersections; K3 surfaces on V_P. The product-of-K3 claim is withdrawn. |
| [405661](https://mathdb.com/p/405661), [383557](https://mathdb.com/p/383557) | HC for Fermat varieties / Fermat fourfolds (named) | claimed progress | **Resolved inside the corpus**, all degrees, dimensions and self-powers: abelian-covers paper Thm 1.2 with c = 1. Its §8 states that "coordinate scaling identifies each smooth one-equation diagonal hypersurface with a Fermat hypersurface", and no exceptional set is needed for c ≤ 1. Not my result. |
| [397798](https://mathdb.com/p/397798) | HC for 2-cycles on abelian 4-folds (named) | open | Resolved in the literature (Markman; cited in the corpus as [26, Cor 1.3]: HC for every abelian variety of dim ≤ 5). All self-powers are covered only partly; see Theorem B. |
| [400361](https://mathdb.com/p/400361) | Grothendieck's Hodge-type standard conjecture for abelian varieties (named) | open | **Resolved by corpus** CM paper Cor 8.4 (any characteristic, via Milne). Stale. |
| [398007](https://mathdb.com/p/398007) | Kobayashi: hyperbolic ⇒ general type (named) | open | **Resolved by corpus** 051 Thm 1.1: K_X is ample, hence X is of general type. Stale. |
| [405146](https://mathdb.com/p/405146) / [315934](https://mathdb.com/p/315934) | Fujita freeness / Fujita conjecture (named) | claimed solved / open | Freeness is corpus 038. **Very ampleness ([364332](https://mathdb.com/p/364332), [402493](https://mathdb.com/p/402493), k-very ampleness [392785](https://mathdb.com/p/392785)) remains open**; see §6.1. |
| [315943](https://mathdb.com/p/315943), [315944](https://mathdb.com/p/315944) | Standard conjectures; Tate conjecture (named) | open | Open. Corpus gives the abelian-variety cases (Tate over 𝔽_q, Hodge standard). |
| [398508](https://mathdb.com/p/398508) | Integral Tate for cubic fourfolds over 𝔽_q (named) | open | Proved in the literature (Charles–Pirutka, Compositio 2015). Stale. |
| [401295](https://mathdb.com/p/401295) | Tate for quintic F₅(x₀,x₁,x₂)+x₃⁵ (named) | open | The record quotes it as "Theorem 2" of its own source (OWR 2017/45). Likely stale. Not pursued. |

## 3. Corpus ledger in this domain (premises, not my results)

- **Hodge.** CM abelian varieties, all codimensions and products (032 Thm 1.1). GHC for CM varieties; Tate for abelian varieties over 𝔽_q; Hodge standard for abelian varieties in every characteristic (Cor 8.2–8.4). All self-powers of split Weil sixfolds, and of every abelian variety of dim ≤ 5 that admits an imaginary-quadratic action (Weil paper Thms 1.1–1.2). Hodge-generic abelian-cover Jacobians and diagonal complete intersections (abelian-covers paper Thms 1.1–1.2). HC and GHC for all self-powers of K3 surfaces with T_S ↪ V_P, plus their Hilbert schemes and moduli spaces (K3 paper Thm 1.2, Cor 9.5). Also the "one exact Kuga–Satake tensor suffices" criterion (K3 paper Thm 1.1) and the conditional reduction (Sep 10).
- **Positivity, MMP, hyperbolicity.** Fujita freeness (038). Log abundance and minimal models in characteristic 0; Kähler log abundance (033–036). Fourfold termination (056). Nagata and Seshadri constants (039). Kobayashi canonical ampleness (051). Hyperkähler SYZ and base ≅ ℙⁿ (041). K3, Enriques and κ = 0 surfaces are Oka (042). Bloch for p_g = 0 (040). Mukai (063). Campana–Peternell in dimension 6 (067). Counterexamples 046–050, 053, 054, 059.

## 4. Theorem A: the K3 frontier in Picard number 14–17

### 4.1 Notation

- U is the hyperbolic plane. V_P := U_ℚ^{⊕2} ⊥ ⟨−1⟩^{⊕4}, which has signature (2,6) and det 1; this is the corpus K3 paper, §1.2 and Lemma 1.3. W_m := U_ℚ^{⊕3} ⊥ ⟨−m⟩ (m ∈ ℤ_{>0}), which has signature (3,4) and det m; this is Floccari's locus.
- For a diagonal form ⟨a₁,…,a_n⟩, the Hasse invariant is c_p = ∏_{i<j}(a_i,a_j)_p. For dim T = 6 put δ = det T and K = K_T = ℚ(√−δ). The Clifford (Witt) invariant is e₂ ∈ Br₂. For dimension ≡ 6 mod 8 one has e₂ = c·(−1,−1) (Lam, *Introduction to Quadratic Forms over Fields*, Ch. V, Prop. 3.20). Sanity check: U³ has c = (−1,−1) and e₂ = 0.
- For a K3 surface S, T = T_S ⊂ H²(S,ℚ) with its cup form has signature (2, t−2), where t = 22 − ρ(S). The corpus hypothesis is "a rational isometric embedding (T_S, q) ↪ V_P" (K3 paper Thm 1.2). Floccari's hypothesis is "T_S ↪ W_m for some m > 0" (G&T Thm 5.11).

### 4.2 Statement

**Theorem A.** Let T be a nondegenerate rational quadratic space of signature (2, t−2), with 2 ≤ t ≤ 8.

1. If t ≤ 5, then T ↪ V_P, and T ↪ W_m for some m > 0.
2. If t = 6, then δ > 0 and K is imaginary quadratic.
   - (a) T ↪ V_P ⇔ c_p(T) = 1 for every prime p split in K ⇔ e₂(T_p) = (−1,−1)_p for every split p.
   - (b) T ↪ W_m for some m ⇔ e₂(T_p) = 0 for every split p.
   - (c) T lies in at least one of the two loci ⇔ e₂(T_p) = 0 for every **odd** split prime p. The two loci coincide unless 2 splits in K (−δ ≡ 1 mod 8). In that case they are disjoint and are separated by the value of e₂(T₂).
   - Brauer form (standard: [C⁺(T)] = res_{K/ℚ}[C(T)] in Br(K)). Condition (a) is C⁺(T) ≅ M₂((−1,−1)⊗K). Condition (b) is C⁺(T) ≅ M₄(K). Condition (c) says C⁺(T) splits at every place of K above an odd prime.
3. If t = 7, then T ↪ V_P ⇔ c_p(T) = (−1,−1)_p(δ,−1)_p for all primes p, where δ = det T < 0. T never embeds in any W_m, because W_m has only four negative directions.
4. If t = 8, then T ↪ V_P ⇔ T ≅ V_P ⇔ δ ∈ ℚ^{×2} and c_p(T) = (−1,−1)_p for all p.

### 4.3 Proof

T ↪ V holds iff V ≅ T ⊥ N for some N, by Witt cancellation. By Hasse–Minkowski, N must have dimension dim V − dim T, determinant d(V)d(T), signature sig V − sig T, and local Hasse invariants c_p(N) = c_p(V)c_p(T)(d(T),d(N))_p, using c(A⊥B) = c(A)c(B)(dA,dB). These local data automatically satisfy the product formula, because V and T are global. They are realized by a global form whenever they are realized locally (O'Meara 72:1; Serre, *Course in Arithmetic*, IV.3).

Locally, data of dimension ≥ 3 are always realizable. The binary forms of determinant d are the forms ⟨x, xd⟩, whose Hasse invariant is (x, xd) = (x, −d). So a binary form with Hasse invariant −1 exists iff −d is not a square in ℚ_p. Globally, an x with prescribed symbols (x, −d)_v = ε_v exists iff ∏ε_v = 1 and ε_v = 1 wherever −d is a local square (Serre III, Thm 4).

1. *Case t ≤ 5, V_P.* The complement has dimension ≥ 3 and is negative definite. The finite local data are free, and the real data are consistent because V_P,ℝ ≅ T_ℝ ⊥ ⟨−1⟩^{8−t}.
   *Case t ≤ 5, W_m.* T ⊥ N ≅ W_m is equivalent to T ⊥ (N ⊥ ⟨m⟩) ≅ U⁴, by cancelling ⟨−m⟩ ⊥ ⟨m⟩ ≅ U. So it suffices to find M of dimension 8 − t and signature (2, 6−t) with M ∼ −T in the Witt group, and then write M = N ⊥ ⟨m⟩ with m > 0 represented by M.
   - For t = 5, −T has dimension 5 and is indefinite, hence isotropic, so −T ≅ U ⊥ M₀ with M₀ of signature (2,1).
   - For t ≤ 4, take M = −T ⊥ U^{4−t}.
   In each case T ⊥ M is hyperbolic of dimension 8, so it is isometric to U⁴.
2. *Case t = 6.* Here sig T = (2,4), so det T has sign (−1)⁴ and δ > 0.
   - (a) N is binary with d(N) ≡ δ. One needs c_p(N) = η_p := c_p(V_P)c_p(T)(δ,δ)_p. Since V_P ≅ ⟨1,−1,1,−1,−1,−1,−1,−1⟩, c_p(V_P) = (−1,−1)_p, and η_∞ = −1 matches a negative definite N. Realizability requires η_p = 1 exactly at primes where −δ is a square, i.e. the primes split in K. At such p, δ ≡ −1 mod squares, so (δ,δ)_p = (−1,−1)_p and η_p = c_p(T). The e₂ form follows from e₂ = c(−1,−1).
   - (b) N = ⟨x⟩ with x ≡ mδ > 0. One computes c(W_m) = (−1,−1)(−1,−m) = (−1,m). The condition reads c_p(T)(δ, mδ)_p = (−1,m)_p, i.e. (−δ, m)_p = θ_p := c_p(T)(δ,−1)_p. At ∞, θ_∞ = 1, consistent with m > 0. A suitable m exists iff θ_p = 1 at all split p. At a split p, (δ,−1)_p = (−1,−1)_p, so θ_p = e₂(T_p).
   - (c) At the two places of K above a split p, both conditions are local conditions on e₂(T_p) ∈ Br₂(ℚ_p) ≅ ℤ/2. (−1,−1)_p is nontrivial exactly at p = 2 among the finite primes. At odd split p, both (a) and (b) demand e₂(T_p) = 0. At p = 2 (if split), (a) demands e₂ ≠ 0 and (b) demands e₂ = 0, so the union imposes nothing there. For the Brauer form: places of K over non-split primes, and the complex place, kill Br₂ of the base, and Br(K) injects into the sum of its local Brauer groups.
3. *Case t = 7.* N = ⟨x⟩ with x ≡ δ < 0, and the condition is c_p(V_P) = c_p(T)(δ,δ)_p.
4. *Case t = 8.* Immediate. ∎

### 4.4 Consequences for K3 surfaces

**Corollary A′ (ρ ≥ 17).** Let S be a projective complex K3 surface with ρ(S) ≥ 17. Then rational HC and rational GHC hold in every degree of S^m for all m ≥ 1. The same holds for every (S^{[n]})^r, every smooth projective moduli space of (twisted) Gieseker- or Bridgeland-stable objects on S and its self-powers, and every hyperkähler variety birational to such a moduli space.

*Proof.* Here t ≤ 5, so Theorem A(1) gives T_S ↪ V_P. Then apply the corpus K3 paper Thm 1.2 and Cor 9.5. ∎

*Novelty caveat.* For HC alone, Theorem A(1) with W_m plus Floccari's Thm 5.11 already gives the same conclusion from published sources. GHC, and HC/GHC for the moduli spaces, come from the corpus.

**Corollary A″ (ρ = 16: exact known region).** Let S have ρ = 16 and T = T_S.
- HC for all S^m is *available* (corpus or Floccari) iff C⁺(T) is unramified at every place of K above an odd prime.
- The corpus adds surfaces not covered by Floccari **exactly** when 2 splits in K and C⁺(T) ≅ M₂((−1,−1)_K). For these, both HC and GHC come from the corpus alone. On the overlap of the two loci, GHC comes only from the corpus, since Floccari's theorem gives HC.
- *Example (corpus only):* T_ℚ ≅ ⟨3,2,−13,−10,−3,−15⟩, K = ℚ(√−39).
- *Example (Floccari only):* T_ℚ ≅ ⟨19,13,−21,−14,−14,−21⟩, K = ℚ(√−247). Here 2 splits and c₂(T) = −1.

**The genuine ρ = 16 frontier.** Take T_ℚ = ⟨21, 2, −6, −19, −2, −10⟩. Then K = ℚ(√−665); 3 splits in K, and e₂(T₃) ≠ 0.

Realize it as follows. L = 2ℤ⁶ with this diagonal form is an even lattice of signature (2,4) with ℓ(A_L) ≤ 6. Since 6 + 6 < 22, it embeds primitively in Λ_K3 (Nikulin, Cor. 1.12.3). A very general period in L_ℂ gives a projective K3 surface S with ρ = 16, T_S = L, and Hdg(T_S) = SO(T_S).

Then End⁰(KS(S)) = C⁺(T)^{op}, the right multiplications, which form the commutant of the left Spin action. Here C⁺(T) ≅ M₂(D) with D a quaternion *division* algebra over K: by Albert–Brauer–Hasse–Noether, index equals exponent, which is 2. Therefore **KS(S) ~ B² with B a simple abelian 8-fold, End⁰(B) = D^{op}**.

Neither corpus Weil theorem applies to B (they cover dim ≤ 5 and split sixfolds), and the corpus's eightfold attempt is withdrawn. Neither the V_P construction nor Floccari's construction reaches S. Validation: `frontier/experiments/geo_k3locus/floccari_compare.out`.

**What would close it.** By K3 paper Thm 1.1, it suffices to make *one* exact even-Clifford Kuga–Satake tensor algebraic for one such surface per locus. Corpus Lemma 9.3 plus Buskin's theorem then transports along rational Hodge isometries. In equivalent form, one needs a geometric family realizing an orthogonal Shimura variety whose generic C⁺ is ramified above an odd prime, together with a curve-product or semiregular-sheaf seed. I found no such family in the corpus.

### 4.5 Lemma C (algebraicity of Hodge similitudes)

**Lemma C.** Let S₁ and S₂ be projective K3 surfaces with T_{S_i} ↪ V_P, and let φ: T₁ → T₂ be a rational Hodge isomorphism with q₂(φu, φv) = λ·q₁(u, v) for some λ ∈ ℚ^×. Then φ is induced by an algebraic correspondence. Consequently, if End_Hdg(T₁) = ℚ, then rational HC holds on S₁ × S₂.

*Proof.* Hodge maps preserve positive period planes, so λ > 0.

The even Clifford algebra is scale invariant. Define c_φ: C⁺(T₁,q₁) → C⁺(T₂,q₂) by uv ↦ λ^{−1}φ(u)φ(v). This is a well-defined isomorphism of algebras: it is induced by the isometry φ: (T₁,q₁) → (T₂, λ^{−1}q₂), composed with the canonical identification C⁺(T₂, μq) ≅ C⁺(T₂, q) given by uv ↦ μuv.

c_φ takes the period bivector J₁ = e₁e₂ to J₂, because the vectors φ(e_i)/√λ are q₂-orthonormal. So c_φ is a Hodge isomorphism of the weight-one Kuga–Satake structures. It is therefore induced by an isogeny KS₁ ~ KS₂, which is algebraic by Lefschetz (1,1) on the product.

A direct computation gives c_φ(v a w) = λ^{−1} φ(v) c_φ(a) φ(w). Hence c_φ ∘ j^{(1)}_w(v) ∘ c_φ^{−1} = λ^{−1} j^{(2)}_{φ(w)}(φ(v)).

The corpus K3 paper Thm 1.2 makes the tensor ι_{w′,E} algebraic for *every* rational nonisotropic w′ ∈ T₂, in particular w′ = φ(w), which is nonisotropic because q₂(φw) = λq₁(w). Prop. 2.1 (k = 1) of the same paper supplies an algebraic left inverse R. So φ = λ·R ∘ Ad(c_φ) ∘ j^{(1)}_w restricted to T₁ is algebraic.

For HC on the fourfold S₁ × S₂: H² ⊗ H² Hodge classes are NS ⊗ NS plus Hom_Hdg(T₁, T₂). If End_Hdg(T₁) = ℚ, every nonzero Hodge map ψ between these irreducible structures is a similitude: ψ*q₂ = q₁(e·,·) with e ∈ End_Hdg(T₁) = ℚ. Degree 6 is H²⊗H⁴ ⊕ H⁴⊗H², whose Hodge classes are NS⊗[pt] and [pt]⊗NS, so they are algebraic; degrees 2 and 6 hold by Lefschetz (1,1). ∎

*Scope.* The lemma does **not** give HC for S₁^a × S₂^b in general. That would need the Goursat analysis of Hdg(T₁ ⊕ T₂), which has low-rank exceptions (SO(3), SO(4) coincidences, as in Shioda–Inose pairs). It also needs Hodge isomorphisms that are not similitudes when End_Hdg(T) ≠ ℚ.

## 5. Theorem B: abelian varieties of dimension ≤ 5

### 5.1 Assembly: everything except Mumford fourfolds

**Definition.** A *Mumford-type fourfold* is a simple complex abelian fourfold A with End⁰(A) = ℚ and Hg(A) ≠ Sp₈. By Moonen–Zarhin Thm 0.1(iii), Hg(A) is then a ℚ-form of SL₂³, and V := H¹(A,ℚ) satisfies V_ℂ = V₁ ⊗ V₂ ⊗ V₃.

**Theorem B0.** Let X be a complex abelian variety with dim X ≤ 5 and no isogeny factor of Mumford type. Then rational HC holds in every codimension on Xⁿ for every n.

*Proof.* Use the case lists of Moonen–Zarhin Thm 0.1 (dim ≤ 4) and Thm 0.2 (dim 5).
- Cases (a), (b), (c), (e), (g) admit a unital ℚ(√−d) ↪ End⁰(X): in (c), D contains imaginary quadratic subfields. Corpus Weil paper Thm 1.2 applies.
- Case (f): X ~ X₀ × X₁ × X₂. By 0.2(ii), B(Xⁿ) is generated by images of B(X₀ⁿ) and B((X₁×X₂)ⁿ). Here X₁ × X₂ is 4-dimensional with a k-action, so corpus Thm 1.2 applies. Elliptic powers are divisor-generated, or CM (corpus Thm 1.1).
- Case 0.1(iii) with Hg = Sp: B(Xⁿ) = D(Xⁿ).
- Cases 0.1(iv) and 0.2(iv): either B(Xⁿ) = D(Xⁿ), or it is generated by isotypic factors Y_j^{m_j}. Each factor of dimension ≤ 3 is divisor-generated on all powers; a 4-dimensional factor falls under (b), (c) or (d); 5-dimensional simple factors are divisor-generated.
- Divisor classes are algebraic by Lefschetz (1,1), and images under projections are algebraic. ∎

### 5.2 The reduction for Mumford fourfolds

Let A be of Mumford type, G = Hg(A). Since G is the Mumford–Tate group generated by h, the Galois action on the three geometric factors is transitive. (If an orbit missed the factor where h is nontrivial, a smaller ℚ-subgroup would contain h.) Let F be the cubic field cut out by the stabilizer of a factor, with embeddings σ₁, σ₂, σ₃.

Over ℂ, ∧²V = 1 ⊕ ⨁_i (S_j ⊗ S_k), where S_i = Sym²V_i, the trivial summand is ℚθ, and {i,j,k} = {1,2,3}. Let q_i be the G-equivariant projector onto S_j ⊗ S_k. For f ∈ F put

  Q_f := Σ_i σ_i(f) q_i ∈ End(H²(A,ℚ)) ≅ H²(A) ⊗ H²(A) ⊂ H⁴(A × A, ℚ),

using the polarization. Each Q_f is Galois-fixed and G-invariant, hence a **rational Hodge class**. It kills θ and acts on T′ := H²_prim(A) as multiplication by f. Since End_Hdg(T′) = F, the Q_f span all of End_Hdg(H²(A)) except the Lefschetz part. Modulo Lefschetz classes this is a 2-dimensional space, matching Moonen–Zarhin's "exceptional classes in B²(X²)".

**Theorem B1.** For a Mumford-type fourfold A the following are equivalent:
- (i) rational HC holds in every codimension on Aⁿ for every n;
- (ii) Q_f is algebraic for every f ∈ F;
- (iii) rational HC holds on A × A in codimension 2.

The same equivalence holds for X ~ A × E (dimension 5), because Moonen–Zarhin 0.2(iv) makes Hg(X) a product.

**Corollary B.** Rational HC holds on every self-power of every complex abelian variety of dimension ≤ 5 **if and only if**, for every Mumford-type fourfold A, the field F = End_Hdg(H²_prim(A,ℚ)) acts on H²(A) through algebraic correspondences on A × A.

*Proof of B1.* (i)⇒(iii)⇒(ii) is trivial. For (ii)⇒(i):

1. *Reduction to multilinear tensors.* Hodge classes on Aⁿ are G-invariants in ∧^•(V^∨ ⊗ ℚⁿ). Antisymmetrization lifts them to G-invariant multilinear tensors in V^{⊗2p}, and pullback along diagonals and addition maps returns them. The algebraic Künneth and Lefschetz operations on abelian varieties make this algebraic, exactly as in corpus Weil paper §1.2 and §2.3.
2. *First fundamental theorem.* Inv_{SL₂}(V_i^{⊗2p}) is spanned by perfect matchings. Hence Inv_G(V_ℂ^{⊗2p}) is spanned by triples of matchings. Bending legs with the polarization ω = ε⊗ε⊗ε, which is a Lefschetz class, turns each matching μ_i into an element of the Temperley–Lieb algebra TL_p acting on V_i^{⊗p}; crossings are combinations of TL elements because dim V_i = 2. TL_p is generated by the e_j. A triple (μ₁, μ₂, μ₃) is the commuting product μ₁^{(1)}μ₂^{(2)}μ₃^{(3)}. So every invariant is a composition of the operators e_j^{(i)} = id ⊗ e^{(i)} ⊗ id, where e^{(i)} ∈ End(V⊗V) is the cup–cap on the i-th tensor factor of V and the identity on the other two, together with Lefschetz bendings.
3. *Exact closure computation.* Inv_G(V^{⊗4}) has dimension 8, with basis {a,b}^{⊗3}: per factor, a = ε₁₂ε₃₄ and b = ε₁₃ε₂₄, while d = ε₁₄ε₂₃ = b − a. Start from the three Lefschetz classes (aaa, bbb, ddd) and q₁, q₂, q₃, which span 5 dimensions. Close under composition in End(V⊗V) and under the S₄ permutations of the four legs; both operations are algebraic (correspondence composition and permutation of the factors of A⁴). In exact rational arithmetic the span grows 5 → 7 → 8, i.e. it is all of Inv_G(V^{⊗4}), and in particular contains e^{(i)} = abb, bab, bba. The Lefschetz classes alone close at dimension 3. Script: `frontier/experiments/geo_mumford/tl_closure.py`; output in `tl_closure.out`.
4. *Descent.* If the Q_f are algebraic, then q₁, q₂, q₃ lie in the ℂ-span of algebraic classes (the σ_i are linearly independent). That span is closed under composition and permutation, so by steps 2–3 it contains every Hodge class. A rational class in the ℂ-span of rational algebraic classes is a rational combination of them (K3 paper eq. (2.3)). ∎

### 5.3 Attempt on (ii), and where it stops

- At CM points of Mumford's Shimura curve, Q_f is algebraic by corpus 032 Thm 1.1.
- The locus of the base where a flat Hodge class is algebraic is a countable union of closed algebraic subsets (relative Chow varieties). With only countably many CM points, nothing propagates. This is the **variational Hodge conjecture** obstruction.
- Markman's route (and the corpus Weil paper §§4–8) works by deforming a *semiregular* sheaf along a Weil-type period domain. The Mumford family is not of PEL type: G(ℝ) has compact factors, so no weight-one standard representation exists.
  - The Serre tensor A ⊗ O_K is an 8-fold of Weil type, outside the corpus range, and the corpus eightfold attempt is withdrawn.
  - The singles summand T := ⊕_i S_i ⊂ Sym²V ⊂ H²(A × A) is a 9-dimensional K3-type structure with real multiplication by F, and KS(T) ~ A^{32}. So (ii) would also follow from (an algebraic KS correspondence) plus (algebraic real multiplication) for a K3-type realization of T. Both are open.
- **Precise open input:** a semiregular coherent sheaf or cycle on A₀ × A₀, at one point A₀ of a Mumford curve, whose normalized Chern character has nonzero projection to Q_f-space. Then Buchweitz–Flenner deformation, which the Weil paper §7 reconstructs, would spread it along the curve. I could not construct one.

## 6. Other named targets: attempts and obstructions

### 6.1 Fujita very ampleness (MathDB 364332, 402493, 392785; named, open)

**Attempt.** Separating x ≠ y amounts to global generation at π^{−1}(x) of π^*(K_X+(n+2)L) − E = K_Y + (n+2)π^*L − nE on Y = Bl_y X.

To use corpus 038 one must write this as K_Y + (n+1)M with M an ample *integral* line bundle. The natural choice M = π^*L − (n/(n+1))E is not integral, and it leaves a nef remainder π^*L.

So the step needs (i) freeness for **ℚ-twisted and nef-twisted** adjoints K_Y + (n+1)M + N, and (ii) ε(L; y) > n/(n+1). Corpus 038 proves neither. Condition (ii) fails in general: Miranda's examples give arbitrarily small Seshadri constants (Lazarsfeld, *Positivity I*, Ex. 5.2.1).

The corpus proof is intrinsically one-point. Prop. 3.2 counts initial exponents at a single point, the minimizer has point centre x, and §6 lifts one fiber value. A two-point analogue would need a joint version of (3.3) at a strictly larger threshold, which the paper does not contain.

**Status:** no bridge. The obstruction is as stated.

### 6.2 Lang's conjecture, "hyperbolic ⇒ every subvariety is of general type"

MathDB 398007 (projective X) is settled by corpus 051. For a singular subvariety Z of a projective hyperbolic manifold Y, with resolution Z̃:
- Z̃ is not uniruled.
- Hence K_{Z̃} is pseudoeffective, κ ≥ 0 (corpus nonvanishing), and a good minimal model Z′ exists (corpus abundance and minimal models).
- Z′ → Z^ν is a *morphism*, because Z^ν has no rational curves and Z′ is klt (Hacon–McKernan, Duke 2007).
- If κ(Z̃) < dim Z, a general Iitaka fiber F is klt with K_F ∼_ℚ 0 and maps generically finitely into Y. An abelian factor of a quasi-étale cover of F gives a contradiction, as does dim F ≤ 2 (infinitely many rational curves on K3 surfaces, by Chen–Gounelas–Liedtke).

So Lang's implication is reduced to: *no strict klt Calabi–Yau or IHS variety of dimension ≥ 3 admits a generically finite map to a hyperbolic manifold*. Corpus 051 handles only smooth targets without exceptional loci, and its disc estimates (§§3, 7) need a derivative bound with respect to a Kähler metric on the source. A degenerate pulled-back metric breaks the compactness step of Prop. 3.2 there.

**Status:** a conditional reduction, mostly classical in structure. I make no claim.

### 6.3 Hyperkähler Oka property

Corpus 042 is surface-specific: property L uses two transverse complete directions on a surface (Prop. 2.2), Chen–Gounelas genus-one families, and Ratner/Verbitsky period dynamics. For a hyperkähler 2n-fold, SYZ (041) supplies n complete directions from one Lagrangian fibration. One would need n transverse complete directions plus a higher-dimensional property-L theory.

**Status:** no bridge.

### 6.4 Routine corollaries noted and not claimed

- Kimura finite-dimensionality for complex surfaces with p_g = 0: corpus 040 plus Kahn–Murre–Pedrini.
- The Tate conjecture for Fermat varieties over 𝔽_q: corpus Cor 8.3 plus Shioda–Katsura domination plus semisimplicity.
- HC for smooth Delsarte hypersurfaces: Fermat domination plus an induction over toric exceptional strata. Fourfolds are easy because the threefold exceptional divisors only contribute H² classes.

These are transfers of the kind the user rejected.

## 7. Validation and reproducibility

All scripts use the Python standard library and exact `Fraction` arithmetic. Run them with `python3 -I`, from the script's own directory:

- `frontier/experiments/geo_k3locus/vp_embedding.py` implements Hilbert symbols, including p = 2, and Hasse invariants. On 400 random rank-6 forms it checks the Theorem A(2a) criterion against an independent search for a binary complement with T ⊥ N ≅ V_P by local invariants: **400/400 agree**. Output: `vp_embedding.out`.
- `frontier/experiments/geo_k3locus/floccari_compare.py` checks:
  - 60/60 rank-5 forms embed in V_P and in some W_m;
  - on 300 rank-6 forms, the predictions of A(2a), A(2b), A(2c) and "the loci differ only if 2 splits" all hold. The counts are 210 in both loci, 8 corpus-only, 13 Floccari-only and 69 in neither. W_m-membership is checked by brute force over m (up to 2·10⁵ when expected; a negative result is backed by the local obstruction).
  - Output: `floccari_compare.out`, including the frontier example's data (split prime 3).
  - An earlier draft example, ⟨14,1,−21,−5,−7,−14⟩ with K = ℚ(√−15), was **wrongly** labelled uncovered. This check showed it lies in Floccari's locus, and it was replaced.
- `frontier/experiments/geo_mumford/tl_closure.py` checks the Plücker relation, the loop constants, idempotence of q_i, and the closure ranks 5 → 7 → 8 (Lefschetz alone: 3). Output: `tl_closure.out`.

Numerical checks verify finite algebra only. The proofs above are the arguments.

## 8. Novelty limits and open gaps

- **Theorem A′:** HC is implied by published Floccari 2026 plus the elementary Witt step. GHC and the moduli-space extensions rely on the corpus. Neither source states ρ ≥ 17 explicitly.
- **Theorem A(2) and Corollary A″** (the Brauer description of both loci and the frontier criterion): not found in the corpus, in Floccari, or in Varesco. A broader literature search was not done.
- The Brauer reformulation relies on two standard facts used without re-proof: e₂ = c(−1,−1) in dimension ≡ 6 mod 8, and [C⁺] = res[C]. The Hasse form of A(2a)/(2b) is proved directly and checked numerically.
- **Lemma C:** depends on the corpus's "every w" clause in K3 paper Thm 1.2 and its Prop. 2.1. I have not checked whether it appears in the literature (it is related to Buskin and Huybrechts on isogenies).
- **Theorem B1:** I did not find this reduction stated in Moonen–Zarhin, who only note the existence of exceptional classes in B²(X²), or in the corpus. A specialist check is needed. The algebraicity of Q_f for non-CM Mumford fourfolds is the open problem.
- Not attempted: MathDB "corpus"-band items beyond those listed. Assigning significance scores beyond MathDB's own bands was not attempted, by design.
- Files written: this report; `frontier/sources/geo_CATALOGUE.md`, `geo_pdf/`, `geo_lit/`, `geo_mathdb/`; `frontier/experiments/geo_k3locus/`, `geo_mumford/`. Nothing was staged or committed, and no indexes were edited.
