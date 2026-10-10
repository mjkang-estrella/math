# Independent review, round 2: the K3 geometry scout

Date: 2026-10-08. Reviewer scope: Theorem A, A′, A″, Lemma C, and their claimed frontier. This is an independent review; none of the scout's conclusions was treated as accepted. Theorems in `openai/math` at **fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb** are premises, as instructed. Their proofs were not audited. No shared report/index was edited, and nothing was staged or committed.

**Parent integration:** the parent checked the cited Varesco Theorem 5.3 and the accepted companion’s Proposition 6.2, verified all 13 successful PDF hashes, and reproduced `check.out` exactly, including 1,000 independent sign tests and the CM example. The scout and index were corrected. No result here is promoted as a significant novel Hodge advance.

## Verdict

**Do not promote this scout as genuinely new substantive progress on the Hodge conjecture.** Its quadratic-form classification is valid after a convention repair, but classifies two existing sufficient hypotheses. A′ is a routine application. Lemma C is already Varesco's Theorem 5.3 (2023) under the exact KS hypothesis. A″ must not be called the exact known Hodge region. I give an explicit CM K3 counterexample to that reading below.

There are useful corrections and stronger formal consequences:

* Floccari's theorem proves the prescribed KS correspondence, not just HC. Combining it with the accepted corpus criterion gives **GHC on Floccari's whole locus**, too.
* The simple quaternionic eightfold description needs **full orthogonal Hodge group**. Without this hypothesis there is a quaternionic action and an isogeny decomposition, but simplicity and equality of endomorphism algebras need not hold.
* One exact KS tensor at one surface gives that surface's self-powers and transports along **algebraic Hodge comparisons**. One surface in a rational quadratic locus does not cover that locus or its period domain.
* Lemma C's proof works for every rational Hodge similitude on the corpus locus. Its End = Q condition is unnecessary if a similitude already exists, and all mixed powers of such an isomorphic pair follow by algebraic cohomological correspondences.
* Using **another accepted pinned result**, the conditional-reduction paper's Proposition 6.2, one obtains algebraicity of **every Hodge map** between transcendental spaces of two K3 surfaces with algebraic exact KS tensors. Consequently HC holds on their two-factor product without End = Q or a similitude assumption. This stronger consequence is a short assembly of accepted premises, not a new cycle construction.

Theorem A's arithmetic comparison may be useful exposition or project infrastructure. A literature-level novelty claim for that comparison is unverified. No new solved Hodge case, new algebraic KS tensor outside the known constructions, or resolution of the landmark MathDB problem [315851](https://mathdb.com/p/315851) is established by the scout.

## 1. Source contracts and pin verification

I read `AGENTS.md`, `sources/upstream.json`, the manuscript catalogue, the complete preprint path listing, `frontier/scouts/geometry.md`, and `frontier/sources/geo_CATALOGUE.md`. I independently downloaded the relevant pinned PDFs. Full URLs and SHA-256 hashes are in [the review manifest](../sources/geo_k3_review_r2/manifest.json); text extractions and selected rendered pages are in that directory.

**K**, the accepted quadratic-locus paper:
[Algebraic Kuga–Satake correspondences and Hodge conjectures on a K3 quadratic locus](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Algebraic-Kuga-Satake-correspondences-and-Hodge-conjectures-on-a-K3-quadratic-locus-September-30-2026/paper.pdf).

* K Theorem 1.1: for a projective complex K3 surface, algebraicity of **one exact** full even-Clifford tensor, for one rational nonisotropic right vector and one rational weight-one polarization, implies rational HC and GHC in every degree of every self-power.
* K Theorem 1.2: the hypothesis is the **actual cup-product space** `T_S ↪ V_P`, isometrically over Q. The conclusion is the prescribed tensor for **any** full even-Clifford realization, **any** rational nonisotropic `w`, **any** rational weight-one polarization, and transported isogenous models. It also asserts HC/GHC for all self-powers.
* K Proposition 2.1, `k=1`: an algebraic left inverse of that exact embedding exists. It is a statement about algebraic cohomological correspondences, not an unspecified abstract Hodge splitting.
* K Lemma 9.3 requires `T_S ↪ V_P`; it produces an ample P-polarized comparison surface at the **transported period**, with a full rational Hodge isometry algebraic in both directions. It does not start with one preselected seed surface.
* K Corollary 9.5: all self-powers of Hilbert schemes, smooth projective moduli of Gieseker-stable twisted sheaves, smooth projective moduli for a **generic** Bridgeland stability condition, and smooth projective hyperkähler birational models of such hyperkähler moduli spaces. Smoothness, projectivity, and the stated stability assumptions must be retained.

**D**, the accepted companion:
[A Conditional Reduction for Algebraic Kuga–Satake Correspondences](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-Conditional-Reduction-for-Algebraic-Kuga-Satake-Correspondences-September-10-2026/paper.pdf).

D Proposition 6.2 says: on the same rational K3-type Hodge structure `T ⊂ H²(S,Q)`, algebraicity of the full multiplication tensor for a quadratic Hodge polarization `q₀` implies algebraicity for another such polarization `q₁`. It imposes **no full-Hodge-group hypothesis**. Its tensor is `m_q:x↦L_x`, from the even to odd Clifford space. D Proposition 3.1 and Lemma 3.2 identify this with the even-even tensor by algebraic weight-one slot operations. This proposition, unlike D's main specialization theorem, is usable at an individual special point. D Theorem 1.2 requires very-general input throughout a full polarized component; it is not a one-arbitrary-seed theorem.

**F**, external primary literature:
Salvatore Floccari, [K3 surfaces associated with varieties of generalized Kummer type](https://msp.org/gt/2026/30-3/gt-v30-n3-p08-p.pdf), Geometry & Topology 30 (2026), 1129–1154. Theorem 5.11 assumes an isometric embedding `T_S ↪ U_Q³ ⊥ ⟨−m⟩`, for a positive integer `m`. Its conclusions are (i) algebraicity of the KS correspondence and (ii) HC on every self-power. Section 3.1 equation (1) defines that correspondence as `v:a↦vav₀` on the **full even algebra**. Remark 3.4 gives the transcendental-space version. These are exactly the data needed by K Theorem 1.1, after weight-one duality/isogeny choices. Lemma 5.4 explains the rational quadratic hypothesis without an omitted integral embedding requirement.

**Withdrawals verified, not assumed.** The pinned PDFs for the October 3 KS claim, October 4 products-of-K3 claim, and September 18 split-eightfold claim are each a withdrawal notice. They explicitly say their advertised theorem is unproved. They point to archived revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a`; that historical manuscript is not a premise. Their independent hashes begin `8e46fd4f5d330e8b`, `48515a3987802b29`, and `205469761edcdec9`. The notices contain no usable positive theorem. A stale web/catalogue statement cannot reinstate them.

## 2. Theorem A: conventions and independent proof

### 2.1 Fix the invariants before comparing them

Use the Clifford convention `v²=q(v,v)`. For a diagonal rational form `q=⟨a₁,…,a_n⟩`, write

\[
\delta(q)=\prod_i a_i\pmod{\mathbf Q^{\times2}},\qquad
D(q)=(-1)^{n(n-1)/2}\delta(q),\qquad
h(q)=\sum_{i<j}(a_i,a_j)\in\operatorname{Br}(\mathbf Q)[2].
\]

Here quaternion symbols are additive Brauer classes; their local signs are `c_v(q)=∏(a_i,a_j)_v`. Write `H=(−1,−1)`. For even dimension, let `b(q)=[C(q)]`, the class of the **full**, central simple Clifford algebra over Q. For dimension six,

\[
b(q)=h(q)+H. \tag{2.1}
\]

This is valid with **nonsquare determinant**, too. One direct derivation, avoiding an ambiguous use of `e₂`, is

\[
C(\langle a,b,c,d,e,f\rangle)
\simeq (a,b)\otimes(-abc,-abd)\otimes(abcde,abcdf).
\]

Separate the first two generators and use their product to make the remaining generators commute with them; repeat once. Expanding quaternion symbols gives (2.1). There is no extra determinant symbol in dimension six. For comparison, in dimensions `n=2m` the full class is

\[
b(q)=h(q)+\frac{m(m-1)}2 H+(m-1)(-1,\delta(q)).
\]

Do **not** call (2.1) the usual homomorphism `e₂:I²→Br[2]` evaluated on arbitrary `q`. The conventional `e₂` has trivial signed-discriminant domain. For signature `(2,4)`, `D(q)=−δ<0`, so the six-dimensional Q-form is not in that domain. One may call `b(q)` a full Clifford invariant, with the definition explicit.

For this signature the volume element squares to `−δ`, and

\[
K=\mathbf Q(\sqrt{-\delta}),\quad Z(C^+(q))=K,\quad
C(q)\otimes K\simeq M_2(C^+(q)),\quad
[C^+(q)]=\operatorname{res}_{K/\mathbf Q}b(q). \tag{2.2}
\]

The full algebra has degree 8 over Q; the even algebra has degree 4 over K and rational dimension 32. Formula (2.2) follows also from the centralizer of the volume element and scalar extension. Even when **δ is a rational square**, the center is `Q(i)`, not `Q×Q`. The source for the general Clifford structures and sizes is van Geemen, [Kuga–Satake varieties and the Hodge conjecture](https://arxiv.org/abs/math/9903146), §§6–7, especially Theorem 7.7. The displayed symbol derivation is independent.

At a place above a nonsplit rational prime, restriction of a base 2-torsion Brauer class multiplies its local invariant by 2, so it vanishes. At a split prime the two local invariants equal the base invariant. The complex place contributes nothing. Thus the scout's **Brauer conclusions survive**, but its `e₂` terminology should be replaced by `b(q)`.

### 2.2 Complement existence, including the global step

Let `V=T⊥N`, with determinant squareclasses `δ=d(T)` and `d_N=d(V)δ`. Hasse–Minkowski requires the prescribed dimension/signature and

\[
c_v(N)=c_v(V)c_v(T)(\delta,d_N)_v. \tag{2.3}
\]

For a binary complement of determinant `d`, write `N=⟨x,xd⟩`; then

\[
c_v(N)=(x,xd)_v=(x,-d)_v.
\]

Hence the precise local restriction is `c_v(N)=+1` whenever `−d` is a square in Q_v. At other finite places either sign occurs. A negative definite real complement requires `d>0` and `x<0`, giving real sign −1.

The passage from locally admissible data to a global binary form needs finite support and Hilbert reciprocity, in addition to this local restriction. Both hold for (2.3), since `T,V` are global. For a conceptual proof, the prescribed ramification signs define a quaternion class over Q. It restricts to zero over `Q(√−d)` precisely when all split-place signs vanish. The relative Brauer group for this quadratic extension consists of `(x,−d)`. The real symbol imposes the required sign of `x`. Equivalently use the rational-form existence theorem, with the binary exception included. See Peters–Sterk, [Symmetric and Quadratic Forms](https://www-fourier.univ-grenoble-alpes.fr/~peters/Books/QuadraticForms/QuadForms.pdf), §12.4, Theorem 12.4.1 and preceding binary condition. For complement dimension at least three, arbitrary finite local Hasse signs with reciprocity and compatible specified real signature are realizable.

### 2.3 Correct exact classification

Set `V_P=U_Q²⊥⟨−1⟩⁴`, `W_m=U_Q³⊥⟨−m⟩`, with `m>0` integral. For a nondegenerate rational `T` of signature `(2,t−2)`, `2≤t≤8`, the following is proved.

**(i) `t≤5`: both embeddings exist.** For `V_P`, the complement has dimension at least three; (2.3), signature and reciprocity suffice. For `W_m`, find `M` with `T⊥M≅U⁴`, `dim M=8−t`, signature `(2,6−t)`. If `t=5`, Meyer's theorem splits a hyperbolic plane from `−T`; use its remaining ternary form. If `t≤4`, use `M=−T⊥U^{4−t}`. A positive rational value represented by `M` can be multiplied by a square to become a positive integer `m`. Split `M=N⊥⟨m⟩` and cancel to obtain `T⊥N≅W_m`. The use of Meyer needs indefinite rank five; that hypothesis holds.

**(ii) `t=6`:** let `δ>0` represent the determinant and `K=Q(√−δ)`.

\[
\begin{aligned}
T\hookrightarrow V_P
&\iff c_p(T)=+1\quad\text{for every rational prime }p\text{ split in }K\\
&\iff C^+(T)\simeq M_2(H\otimes K),\tag{2.4}\\
T\hookrightarrow W_m\text{ for some }m>0
&\iff b(T)_p=0\quad\text{for every split }p\\
&\iff C^+(T)\simeq M_4(K).\tag{2.5}
\end{aligned}
\]

For (2.4), `d(V_P)=1`, `c_v(V_P)=(−1,−1)_v`; the binary complement data are `η_v=(−1,−1)_v c_v(T)(δ,δ)_v`. At a split prime `δ≡−1` modulo squares and `η_p=c_p(T)`. At infinity `η_∞=−1`, giving the negative definite complement, so the global criterion applies.

For (2.5), the complement is `⟨mδ⟩` and `c_v(W_m)=(−1,m)_v`. The equation becomes

\[
(-\delta,m)_v=c_v(T)(\delta,-1)_v=\theta_v.\tag{2.6}
\]

At a split prime this right side equals the local sign of `b(T)` by (2.1). Its real value is +1, so the global solution of (2.6) has `m>0`; multiplying by a rational square makes it integral. This proves sufficiency as well as necessity.

The union is exactly

\[
T\hookrightarrow V_P\ \text{or}\ T\hookrightarrow W_m\text{ for some }m
\iff C^+(T)\text{ splits above every odd rational prime}.\tag{2.7}
\]

For a **fixed determinant squareclass**, the two embedding loci coincide if 2 does not split in K. If 2 splits, they are disjoint: (2.4) requires `b(T)_2` nonzero and (2.5) requires it zero. The test `−δ≡1 mod 8` means the squareclass has even 2-adic valuation and odd-unit part congruent to 1 modulo 8; it is not a congruence test on an arbitrary unnormalized determinant.

**(iii) `t=7`:** `δ<0`, the `V_P` complement is `⟨δ⟩`, and the exact condition is

\[
c_p(T)=(-1,-1)_p(\delta,-1)_p\quad\text{at every finite prime}.
\]

The real signatures already match. No `W_m` has enough negative directions.

**(iv) `t=8`:** the condition is `T≅V_P`: determinant square and `c_p(T)=(−1,−1)_p` for every finite prime, with the given signature. Again no `W_m` embedding is possible.

**Status:** a proof of an arithmetic classification, not a proof of new Hodge classes. The independent computation below checks the symbol identities and examples; it is not the proof of the universal statement.

## 3. A′ and A″: valid consequences and necessary corrections

### 3.1 A′ is correct with the exact moduli hypotheses

For projective `S` with `ρ≥17`, `dim T≤5`, so K Theorem 1.2 yields HC/GHC for all `S^n`. K Corollary 9.5 gives the Hilbert/moduli/birational consequences in §1. This is an immediate corollary.

Ordinary HC for all these K3 self-powers already follows from the `W_m` embedding and F Theorem 5.11. Ordinary HC for the indicated motivic summands then follows by the existing motivic decompositions, too; it should not be credited as new solely because the corpus restates that transfer. GHC uses the accepted corpus premise. No new cycle construction is involved.

### 3.2 Replace “exact known region” by “union of these two embedding loci”

Equation (2.7) is an iff for membership in the two quadratic loci. It is **not** an iff for HC being known, for algebraicity of KS in all literature, or for a surface remaining an open case after all corpus inputs. The scout acknowledges CM cases elsewhere, so the literal broad reading is internally inconsistent as well.

The correct positive consequence is stronger than the scout states: **every S in either embedding locus has HC and GHC for every self-power**. On `V_P` use K Theorem 1.2. On `W_m` use F Theorem 5.11(i), its exact tensor convention and transcendental reduction, then K Theorem 1.1. The motivic transfers used in K Corollary 9.5 apply to this conclusion as well. Calling the second region “HC only” misses this composition of accepted results.

“Corpus-only” below means only `V_P` versus `W_m`; it does not exclude all other prior constructions or CM results. The condition `C⁺≅M₂(H_K)` with 2 split really does distinguish the two constructions. It does not create a new solved Hodge case beyond K's existing theorem.

### 3.3 Independent exact checks of the scout examples

[check.py](../experiments/geo_k3_review_r2/check.py) imports no scout code. [check.out](../experiments/geo_k3_review_r2/check.out) records exact rational computations, including 1000 six-dimensional forms checked against the full three-quaternion Clifford decomposition. The product formula and union test pass. Positive embeddings have explicit complement witnesses; negative results use a split-place obstruction, never exhaustion of a bounded search.

* `⟨21,2,−6,−19,−2,−10⟩`: determinant squareclass 665. At 3, `−665` is a local square and `c₃=b₃=−1` in sign notation. Neither embedding exists. In K the even Clifford algebra is ramified at the two places over 3; the other base ramification at 7,19 and infinity dies under restriction.
* `⟨3,2,−13,−10,−3,−15⟩`: squareclass 39, with 2 split. The complement `⟨−1,−39⟩` gives `V_P`; `b₂` is nonzero, preventing `W_m`.
* `⟨19,13,−21,−14,−14,−21⟩`: squareclass 247, with 2 split and `c₂=−1`. It does not embed in `V_P`. It **does** embed in `W_6`, with positive complement `⟨1482⟩`.
* The retired alleged uncovered example `⟨14,1,−21,−5,−7,−14⟩` is indeed covered by `W_2`, complement `⟨30⟩`. The scout's correction of that counterexample is valid.

I did not re-label the scout's random trials as independent evidence: its two scripts share the same Hilbert-symbol implementation, and one large-complement branch simply returns true by theory. The review's independent algebra decomposition is a different check of the delicate sign normalization.

### 3.4 An explicit CM counterexample to a global “known region” claim

This is a **review counterexample**, not a newly solved Hodge case. Let

\[
F=\mathbf Q(t),\quad t^3+t^2-2t-1=0,\qquad
\beta=t^2-2t+4=(t-1)^2+3,\qquad E=F(\sqrt{-\beta}).
\]

The cubic is irreducible by the rational-root test and has three real roots, one positive and two negative. Since β is totally positive, E is a CM field of degree six. On E take

\[
q(x,y)=\operatorname{Tr}_{E/\mathbf Q}(t x\bar y).
\]

It has signature `(2,4)`. In the basis `1,t,t²,s,ts,t²s`, `s²=−β`, its Gram matrix is

\[
\begin{pmatrix}
-2&10&-8&0&0&0\\10&-8&26&0&0&0\\-8&26&-32&0&0&0\\
0&0&0&-36&82&-116\\0&0&0&82&-116&244\\0&0&0&-116&244&-394
\end{pmatrix}.
\]

Exact elimination gives diagonal entries

\[
\langle-2,42,-14/3,-36,637/9,-26\rangle,
\]

and hence the isometric diagonal squareclasses

\[
\langle-2,42,-42,-1,13,-26\rangle.\tag{3.1}
\]

The determinant is `5096²`, so `K=Q(i)`. At 13 the only nonunit coefficients in (3.1) are `13,−26`. The unit/nonunit cross-symbols cancel in pairs, and `(13,−26)₁₃=(−2/13)=−1`; thus `c₁₃=−1`. Since 13 splits in `Q(i)`, (3.1) lies outside **both** embedding loci.

To realize this as a genuine transcendental space, put Hodge type `(2,0)` at one complex embedding above the positive real embedding of t, type `(0,2)` at its conjugate, and type `(1,1)` at the other four. Multiplication by E preserves these types. The rational `(1,1)` subspace is E-stable; since E has rank one as an E-module, this subspace must be zero. The displayed integral matrix is an even lattice of signature `(2,4)`. The primitive-embedding argument of §4 applies; period surjectivity then gives a projective K3 with exactly this transcendental lattice and `ρ=16`.

Its Hodge structure is CM: its Hodge action lies in the torus acting by E-multiplication. Equivalently its endomorphism field contains the degree-six field E and therefore equals E. Published HC for all powers applies: Varesco, [The Hodge conjecture for powers of K3 surfaces of Picard number 16](https://arxiv.org/abs/2203.09778), Corollary 2.3 (building on Ramón-Marí and the algebraicity of CM endomorphisms). Thus “HC known iff (2.7)” is explicitly false, even at Picard number 16. This example also illustrates why CM specializations must not inherit the generic endomorphism algebra of KS.

## 4. Lattice realization and the generic quaternionic eightfold

The scout's lattice realization works, with its quantifiers made explicit. For an integral diagonal rational form `diag(a_i)`, the sublattice with basis `2e_i` has Gram matrix `4 diag(a_i)`. It is even and has the **same rational isometry type**. Its discriminant group requires at most six generators. The K3 lattice has signature `(3,19)`; the required complement has signature `(1,15)` and rank 16. The safe sufficient inequality is

\[
\ell(A_L)+2\le8<16=22-6,
\]

with both signature differences positive. Thus a primitive embedding exists. This avoids borderline versions of Nikulin's criterion. The primary Nikulin PDF endpoint returned HTTP 403 in this review; the exact sufficient statement was checked in the author-hosted Huybrechts [Lectures on K3 surfaces](https://www.math.uni-bonn.de/people/huybrech/K3Global.pdf), Chapter 14, Theorem 1.12, which cites Nikulin Theorem 1.14.4. No unverified endpoint was treated as read.

Choose a period in `L_C` outside every rational hyperplane. The resulting K3 has `T_Z=L`, not merely a finite-index abstract copy: primitiveness identifies the saturated perpendicular of NS. Its NS has signature `(1,15)` and contains an integral positive class, hence the surface is projective. Periods avoiding the further proper Hodge loci have `Hg(T)=SO(T)`. Avoiding only rational hyperplanes establishes Picard rank; one must also impose the full-Hodge-group condition for the next conclusion.

For `T₀=⟨21,2,−6,−19,−2,−10⟩`, the nonsplit even Clifford class has exponent two over the number field K. The number-field index/exponent theorem gives

\[
C^+(T_0)\simeq M_2(D)
\]

for a quaternion division algebra D/K. For the **full even** KS realization `A`, `dim A=16`. Right Clifford multiplication always gives

\[
M_2(D^{op})\hookrightarrow\operatorname{End}^0(A).
\]

Its two equivalent matrix idempotents imply `A∼B²` with `dim B=8` and `D^{op}↪End⁰(B)` for every such period. For full orthogonal Hodge group, van Geemen Proposition 6.3 and Lemma 6.5 identify the commutant of the lifted spin action with the right even algebra. Hence, **under this additional hypothesis**,

\[
\operatorname{End}^0(A)=M_2(D^{op}),\qquad
\operatorname{End}^0(B)=D^{op},\qquad B\text{ is simple}.
\]

At special periods the commutant may be larger. In particular a CM KS variety has CM simple factors; a simple such factor cannot have a noncommutative quaternion division algebra as its endomorphism algebra. The scout's detailed “very general period” paragraph is adequate; its summary's unqualified assertion about all outside surfaces is not.

This construction proves the existence of quadratic loci missed by two methods. It does not prove that HC is false there, or that every point there is an unresolved Hodge case, or that no other accepted theorem applies. For the very general `T₀` period the reviewed inputs do not construct the missing tensor. The withdrawn eightfold paper supplies no substitute.

## 5. Lemma C and its exact strengthening

### 5.1 The similitude proof is valid, and already published

Let `φ:T₁→T₂` be a rational Hodge similitude with multiplier λ. Positivity on the period plane gives `λ>0`. On even products define

\[
c_\phi(v_1\cdots v_{2r})=\lambda^{-r}\phi(v_1)\cdots\phi(v_{2r}).
\]

The Clifford relations make this a unital algebra isomorphism. It preserves the period bivector and hence the weight-one Hodge structure. This is a rational Hodge isomorphism; after clearing denominators it is an isogeny (with the usual contravariance on H¹), so its maps on the two tensor slots are algebraic. One should not require the original rational map itself to be an integral isogeny.

The exact identity is

\[
\operatorname{Ad}(c_\phi)j_w^{(1)}(v)
=\lambda^{-1}j_{\phi(w)}^{(2)}(\phi(v)).\tag{5.1}
\]

If `R₂j_{φ(w)}^{(2)}=id`, then `λR₂ Ad(c_φ)j_w^{(1)}=φ`. K Theorem 1.2 really does supply the necessary tensor with that right vector; K Proposition 2.1 supplies `R₂`. Arbitrary weight-one polarization choices are handled by Hodge automorphisms of H¹, which are algebraic. No full Mumford–Tate assumption is needed here, and λ need not be a rational square.

In fact one exact tensor permits every right vector: for nonisotropic `w,w′`, `j_{w′}=R_{w^{-1}w′}∘j_w`, where right multiplication by the even element `w^{-1}w′` is a weight-one Hodge map. Thus the every-w clause is sufficient and exact, but not an additional geometric obstruction once one tensor is known.

The prior art is exact: Mauro Varesco, [Hodge similarities, algebraic classes, and Kuga–Satake varieties](https://doi.org/10.1007/s00209-023-03390-8), Math. Z. 305, 69 (2023), Proposition 3.1, Lemmas 3.2–3.5, and **Theorem 5.3**. The latter states precisely algebraicity of Hodge similarities between K3 surfaces satisfying the KS Hodge conjecture. The normalized right vector there is `φ(w)/λ`, equivalent to (5.1). K Proposition 9.4 itself cites this prior work. Lemma C's claimed novelty therefore fails; it is a specialization of a published theorem.

Buskin, [Every rational Hodge isometry between two K3 surfaces is algebraic](https://arxiv.org/abs/1510.02852), Theorem 1.1, and Huybrechts, [Motives of isogenous K3 surfaces](https://arxiv.org/abs/1705.04063), Theorem 0.1, concern rational **isometries** of full H². A transcendental Hodge isometry extends by Witt to full H² because both rational ambient spaces are the K3 form; this extension is Hodge. A nonsquare multiplier cannot simply be divided out over Q. Varesco is the appropriate prior art for that additional case.

### 5.2 What follows without using D Proposition 6.2

Transcendental K3 Hodge structures are simple. For any two surfaces satisfying the exact KS hypothesis, every Hodge similitude is algebraic by §5.1. If `End_Hdg(T₁)=Q`, any nonzero Hodge map `ψ:T₁→T₂` is an isomorphism and satisfies `ψ†ψ=λ id`, with `λ>0`; it is a similitude. If Hom is zero there is nothing to prove. This validates the scout's End = Q product statement.

If a similitude φ already exists, the End = Q assumption is unnecessary: K Theorem 1.1 gives HC on `S₁²`, so every Hodge endomorphism e of `T₁` is algebraic; every Hodge map `T₁→T₂` is `φe`. More strongly, φ and its inverse, plus algebraic maps on NS and the degree-zero/four Tate pieces, give mutually inverse algebraic cohomological correspondences between the full cohomologies of `S₁,S₂`. Tensoring them transfers HC/GHC from self-powers to **every `S₁^a×S₂^b`**. These are cohomological inverses; no inverse modulo rational equivalence is claimed or needed.

Thus the scout's Goursat warning is inappropriate for a pair already equipped with a similitude. It is relevant to arbitrary unrelated transcendental Hodge structures, not to powers of two algebraically isomorphic cohomological motives.

### 5.3 Stronger pair theorem using the other accepted corpus premise

Define `𝒦` to be the projective complex K3 surfaces admitting an algebraic exact full even-Clifford KS tensor for their transcendental cup form. In particular both embedding loci lie in `𝒦`.

**Corrected theorem C+.** Assuming K Proposition 2.1 and D Proposition 6.2 at the pin, for any `S₁,S₂∈𝒦`, every rational Hodge map `T₁→T₂` is algebraic. Rational HC holds in every degree of `S₁×S₂`. If their transcendental Hodge structures are isomorphic, HC and GHC hold for every mixed power of the pair, with no End or similitude restriction.

**Proof.** A nonzero Hodge map ψ is an isomorphism by simplicity. Put `q′=ψ* q₂` on `T₁`. This is a rational quadratic Hodge polarization, but need not be a rational scalar multiple of `q₁`. Convert the known even-even tensor on `S₁` to `m_{q₁}` by undoing its invertible odd right multiplier. D Proposition 6.2 gives algebraicity of `m_{q′}` on the **same S₁**; convert back to the prescribed even-even tensor. The rational Hodge isometry

\[
\psi:(T_1,q')\longrightarrow(T_2,q_2)
\]

induces a weight-one Clifford isomorphism. Transporting its tensor slots gives an algebraic map `S₁→KS(T₂)²` whose action is `j_{ψ(w)}^{(2)}ψ`. Compose with K Proposition 2.1's algebraic return for `S₂`. The result is ψ. The zero map is trivial.

For HC on the product, the only non-Tate issue in the middle Künneth component is `Hom_Hdg(T₁,T₂)`: the mixed NS/T pieces have no rational Hodge classes. NS products and the degree-zero/four classes are algebraic. In degree six the two summands are `H²⊗H⁴` and `H⁴⊗H²`, and their Hodge classes are divisor times point. This proves all degrees. If `T₁≅T₂`, the algebraic ψ and ψ⁻¹ extend over the equal-rank Tate pieces and transfer all mixed powers exactly as in §5.2. The same argument applies to any finite collection in `𝒦` whose transcendental structures are mutually Hodge-isomorphic. ∎

This stronger conclusion **does not follow from the every-w clause alone**. It uses D Proposition 6.2's explicit change-of-quadratic-polarization contract, an accepted corpus theorem which the scout did not use. Its proof was not re-audited. This is a new-to-this-review formal deduction, not demonstrated new-to-literature substantive mathematics. No statement here proves HC on arbitrary higher products of mutually nonisomorphic members of `𝒦`, or on products of all K3 surfaces. In particular the withdrawn unrestricted product theorem has not been restored.

## 6. What one exact tensor can actually transport

For one surface S, K Theorem 1.1 gives all its self-powers. It also gives the specified motivic transfers once their usual hypotheses hold. It does not give an arbitrary flat tensor on a deformation family.

If another K3 surface R comes with an **algebraic** rational Hodge isometry or similitude `T_R→T_S`, the full KS tensor transports through its source correspondence and the Clifford weight-one maps. Buskin/Huybrechts make rational Hodge isometries algebraic without already knowing KS on R. For a general Hodge similitude, invoking Lemma C to prove its algebraicity already assumes KS on both surfaces; that would be circular if used to establish KS on the new surface.

A rational isometry of underlying quadratic spaces without matching period lines is not a Hodge comparison. The rational isometry orbit of one period is countable and can be dense; it is still not an entire positive-dimensional period domain. A countable union of proper algebraic subsets can contain a dense countable set, so dense orbit points do not force one Chow/Hilbert component to dominate. The corpus's actual argument in §8 has stronger cycle-parameter and avoidance hypotheses. K Lemma 9.3 chooses a comparison surface with the required period in a family **already proved at all relevant periods**; it is not a propagation theorem from one fixed seed.

Accordingly replace “one such surface per locus suffices” by either:

* one tensor for each desired surface or each class reached by an already algebraic Hodge comparison; or
* a geometric argument producing the tensor very generally, with a justified specialization/extension mechanism covering the family.

A bare curve-product seed or unspecified semiregular sheaf is not an equivalent theorem: one must prove its precise tensor component, its deformation locus and unobstructedness, and passage to all requested fibers. For the odd-ramified generic quaternionic eightfolds none of these missing inputs has been constructed here.

## 7. Acceptance ledger and importance

**A:** accept the arithmetic statement after replacing the ambiguous Witt-`e₂` notation by the full Clifford class and spelling out binary global existence. Proof: §2. Computation: 1000 exact sign checks and explicit certificates. Novelty: unverified comparison of standard invariants; no new Hodge classes. Significance: useful diagnostic classification, insufficient for the user's objective.

**A′:** accept with the exact projectivity/stability/birational hypotheses in §1. Proof: immediate application of K and the elementary embedding. Computation: unnecessary. Novelty: ordinary HC already follows from F and standard transfers; GHC is a corpus corollary. Significance: not a new substantive advance.

**A″:** accept only as an exact comparison of the two embedding hypotheses. Reject a global iff for known HC; §3.4 is a fully realized CM counterexample. Add GHC on the F locus by K Theorem 1.1. Novelty: no new solved Hodge case. Significance: does not establish an exhaustive frontier after all inputs.

**Quaternionic KS example:** accept the existence and generic description. Retain the full orthogonal Hodge-group hypothesis for simplicity and equality of End. Computation certifies a local obstruction; period/lattice theory proves existence. It diagnoses the failure of two methods, not universal openness of those surfaces.

**C:** accept algebraicity of every stated similitude. Reject mathematical novelty: it is Varesco 2023, Theorem 5.3. Strengthen its consequences as in §5.2, and separately record C+ using the additional accepted D Proposition 6.2. These are valid reductions/assemblies. They do not manufacture a missing KS correspondence outside the existing constructions.

**Proposed closure of the frontier:** remains conditional, and the “one surface per locus” sufficiency is unjustified. A genuinely substantive result would need a new geometric algebraicity input at previously uncovered, non-CM periods, or a proved propagation mechanism with its full hypotheses. Neither is supplied.

The literature search checked Buskin, Huybrechts, both relevant Varesco papers, Floccari, van Geemen, and the cited lattice/quadratic-form sources. It found an exact predecessor for C, not just a related theorem. It did not certify that the local/Brauer comparison in A is absent from all prior literature. No priority claim is warranted.

## 8. Review artifacts and reproducibility

Only this assigned review and the following assigned directories were written:

* `frontier/sources/geo_k3_review_r2/`: pinned PDFs, primary-literature PDFs, text extractions, rendered contract pages, and `manifest.json` with exact retrieval URLs, hashes and the failed Nikulin retrieval recorded honestly.
* `frontier/experiments/geo_k3_review_r2/check.py` and `check.out`: standard-library-only independent exact calculations. Run from the repository root with `python3 -I openai-proof-research/frontier/experiments/geo_k3_review_r2/check.py`.

The computations prove finite rational identities and provide verifiable examples. Universal embedding criteria, K3 realizations, and Hodge conclusions use the stated proofs and exact source premises, not statistical evidence. The explicit CM construction is a counterexample to overclaiming an exhaustive known region; it is not offered as a new Hodge theorem.
