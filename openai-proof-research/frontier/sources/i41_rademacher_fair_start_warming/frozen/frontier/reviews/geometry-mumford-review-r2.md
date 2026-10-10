# Independent adversarial review: geometry Theorem B/B1, round 2

Date: 2026-10-08. Reviewer scope: `frontier/scouts/geometry.md`, §5, with no inherited acceptance of scout claims. Rules read: `openai-proof-research/AGENTS.md`. Corpus pin: `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Accepted corpus proofs were used as premises, not audited. Only this report and directories with prefix `geo_mumford_review_r2` were written; no agents, staging, or commits.

**Parent integration:** accepted as a corrected, attributed reduction; rejected as a new finding. The parent checked the prior theorem in immutable source and the October 2 Zenodo release record, verified all 15 successful source hashes, and reproduced the independent tensor-audit output exactly. The scout and frontier index now record this disposition.

## Verdict

**B0 is correct under the stated corpus premise. B1 is a correct conditional equivalence after the repairs below. It does not prove any new case of the Hodge conjecture. Its central all-powers reduction has an exact prior-art match, so it must not be presented as a genuinely new substantive theorem.**

The main mathematical repairs are: distinguish Hg from MT and from its simply connected cover; put the Tate twists back; distinguish a degree-four class from a degree-preserving correspondence; explain the algebraic inverse Lefschetz operations; account for Koszul signs; and replace the finite closure calculation by a symbolic identity plus an all-arity proof. These repairs work. I found no counterexample to the repaired B1.

The novelty failure is decisive. Bhattacharjee–Mandal–Bhattacharya, *Density of Algebraic Loci of Weil Classes on Abelian Varieties*, source release v3.2.0, contains the theorem **“Every power of a Mumford fourfold”**, TeX label `thm:mumfordpowers`, with exactly B1's substantive implication. Its preceding `prop:mumfordrm` identifies the cubic multiplication on primitive H² and the two-dimensional exceptional quotient. Its proof also identifies the seven-dimensional initial span and the eighth direction supplied by composition. The release is [archived on Zenodo, October 2, 2026](https://zenodo.org/records/23093099). I checked the [actual theorem and proof at immutable commit `a80abf628c5f05236372e97dbfaa5b316463e9df`](https://github.com/creelie/H8/blob/a80abf628c5f05236372e97dbfaa5b316463e9df/tex/sections/11c_mumford.tex#L543), not just a search snippet. This is public preprint/source prior art; I make no claim of peer review or earliest priority.

## 1. Source contracts and the pin

The local `sources/upstream.json`, `sources/CONTENTS.md`, complete `sources/preprints-tree.json`, and `frontier/sources/geo_CATALOGUE.md` were read. Relevant contracts actually checked in manuscript text:

1. **Corpus Weil paper**, `preprints/Weil-classes-and-Hodge-classes-on-abelian-powers-October-6-2026/paper.pdf`, Theorem 1.2: a complex abelian variety of dimension at most five with a **unital imaginary-quadratic action** satisfies rational HC in every codimension on every self-power. Nonsimplicity, extra endomorphisms, and special periods are explicitly included. No balanced signature, discriminant, genericity, or separately selected compatible polarization is required for this theorem. Theorem 1.1 instead concerns sixfolds with a compatible polarization whose rational Hermitian form is hyperbolic of signature (3,3); it does not cover arbitrary eightfolds.
2. **Corpus CM paper**, `preprints/The-rational-Hodge-conjecture-for-CM-abelian-varieties-October-6-2026/paper.pdf`, Theorem 1.1: all rational Hodge classes on every complex CM abelian variety, and therefore finite products and powers, are algebraic. This supplies a CM-fiber statement, not a deformation theorem.
3. **Moonen–Zarhin**, [*Hodge classes on abelian varieties of low dimension*, arXiv:math/9901113v2](https://arxiv.org/abs/math/9901113), Theorems 0.1–0.2, §§1.2–1.5, 2.5–2.7 and 5: the complete low-dimensional classification and product-group statements used below. Local manuscript text: `../sources/geo_lit/moonen-zarhin-math9901113.txt`. Their V denotes homology; this report uses cohomology consistently instead.
4. **Algebraic Lefschetz inverses**: Kleiman, [*The standard conjectures*](https://mishap.sdf.org/temp/Kleiman_Standard_Conjectures.pdf), Proposition 4-3(2)(c), printed p.16, explicitly gives the Lefschetz standard conjecture for abelian varieties; Theorem 4-1 and its proof identify the inverse-Lefschetz formulation. I inspected the scanned pages, including p.15–16. This is an established theorem, not an additional Hodge-conjecture assumption. The cited older proof is Kleiman's 1968 §2 Appendix, pp.373–378, with Lieberman's contribution acknowledged.

All corpus URLs in this review mean the immutable raw base `https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/`.

**Withdrawal verification:** I independently downloaded the three actual pinned PDFs, extracted their text, and checked the eightfold notice visually. Each PDF is a withdrawal notice, not a surviving theorem manuscript. The eightfold notice gives the corrected signed count −2m rather than zero. The K3-product and general Kuga–Satake notices explicitly leave their claimed algebraicity theorems unproved because they depend on that construction. Their links to revision `adc7f1241b42e322a6451854ab7e4b4c146bf78a` do not turn the archived claims into pinned premises. Exact downloads, URLs and SHA-256 hashes are recorded in `../sources/geo_mumford_review_r2/manifest.json`. Thus there is no usable universal Kuga–Satake, product-of-K3, or split-eightfold theorem from those files.

## 2. B0: complete dimension-at-most-five assembly

Here all conjectures and cycles have rational coefficients; all varieties are complex abelian varieties. Isogeny causes no problem: if u:Y→X is an isogeny, then u_*u^*=(deg u)id, and both operations preserve algebraicity, also on every power.

For dimension at most four, use the exact Moonen–Zarhin cases:

- **(a)**: a CM elliptic curve with CM field k times a simple threefold admitting k. The diagonal k-action is unital on the entire product; apply corpus Theorem 1.2 after transporting along the isogeny.
- **(b)**: the simple fourfold has an imaginary-quadratic subfield in its endomorphism field, with multiplicities (2,2). The same corpus theorem applies.
- **(c)**: the simple fourfold has definite quaternion multiplication over Q. Any noncentral quaternion generates an imaginary-quadratic field: over R the algebra is Hamilton's, so its noncentral quadratic minimal polynomial has negative discriminant. The embedding is unital. Again apply Theorem 1.2.
- **(d)**: End⁰=Q. If Hg=Sp₈, the symplectic first fundamental theorem gives divisor generation on all powers. Otherwise this is precisely the remaining Mumford case.
- Outside (a)–(d), Theorem 0.1(iv) gives divisor generation on all powers. One must use the theorem's explicit conclusion: Hg=Sp_D alone is not a sufficient generic slogan in the presence of type III.

For dimension five:

- **(e)** and **(g)** have a common imaginary-quadratic action on the whole variety, so corpus Theorem 1.2 applies directly.
- **(f)** has Hg(X)=Hg(X₀)×Hg(X₁×X₂), explicitly by 0.2(ii). Powers of X₀ are divisor-generated; X₁×X₂ is a fourfold with k-action. Products of the algebraic classes from these factors span the Hodge classes. An action on the entire fivefold is unnecessary here.
- Outside (e)–(g), 0.2(iv) gives the product of Hodge groups of the isotypic factors. On Xⁿ the factors to use are **Y_j^{m_j n}**, with the n included. Factors of dimension 1, 2, 3, or 5 are covered by the corresponding all-powers results (in particular the simple prime-dimensional case, 2.7). A four-dimensional simple factor has multiplicity one and is accompanied by an elliptic curve; return to the fourfold list above.

This exhausts dimensions ≤5. Under the corpus assumptions, the only remaining isogeny configurations are A and A×E with A a Mumford-type fourfold. **Classification: proved assembly/corollary, correct; novelty: routine combination; significance: an exact frontier description, no new algebraicity.**

## 3. Hg, the cubic field, and the exceptional dimension

Define a Mumford-type fourfold here to mean a simple complex abelian fourfold A with End⁰(A)=Q and Hg(A)≠Sp(H¹(A),ω). This is a condition on its **actual** Hodge group, not merely on membership in a family bearing Mumford's name.

Put V=H¹(A,Q), of weight one. The simply connected cover of G=Hg(A) becomes SL₂³ over an algebraic closure, acting on

    V_Qbar = W₁ ⊗ W₂ ⊗ W₃,     dim W_i=2.

The image has central kernel consisting of triples of signs with product one. Thus “Hg is a Q-form of SL₂³” must be read **up to central isogeny**. Further, Hg is not MT: MT(A)=G_m·Hg(A), almost directly. The group generated over Q by the full h:S→GL(V_R) is MT; Hg is generated by h restricted to the norm-one circle. For weight 2p, G-invariants in H^{2p} become MT-invariant tensors after twist (p).

Here is the missing transitivity argument. On the three standard factors the semisimple part of the Hodge cocharacter has weights ±a_i/2. The tensor product has only two Hodge weights. Two nonzero a_i would already give at least three distinct weights, so precisely one geometric factor carries the nontrivial Hodge circle. An entire Galois orbit missing that factor would give a rational normal factor with trivial Hodge-circle projection, contradicting the defining minimality of Hg. Hence the Galois action on the three labels is transitive. Polarizability gives the real-factor description in Moonen–Zarhin §1.5; the three factors are individually defined over R. Consequently their field of definition is **totally real cubic**, not a split étale algebra Q³ or Q×quadratic. Call it F. Equivalently the cover has the usual restriction-of-scalars description from a quaternion algebra over F, split at one real place and definite at the other two.

As representations of the semisimple cover,

    Λ²V_Qbar = (Λ²W₁⊗Λ²W₂⊗Λ²W₃)
               ⊕ ⨁_{i=1}³ (Λ²W_i⊗Sym²W_j⊗Sym²W_k).

Each determinant factor is trivial for SL₂, but must not be silently erased when discussing Hodge weights. The first summand descends to Qθ≅Q(−1). The three other summands U_i have dimension nine, are pairwise inequivalent, and comprise P²=H²_prim(A), of dimension 27. They are permuted transitively by Galois. Therefore

    End_Hdg(P²)=F,       End_Hdg(H²(A))=Q×F.

Indeed, after scalar extension the commutant is the diagonal algebra Qbar³ on P²; its transitive descent is F. There is no hidden quaternionic commutant. The primitive space here has Hodge numbers (6,15,6); it is **not** the nine-dimensional K3-type space in §5.3. That other space is Lie(G)(−1), embedded through Sym²V in H²(A²).

Write q_i for the projector onto U_i, extended by zero on θ, and f₀=Σσ_i(f)q_i. This defines a rational Hodge endomorphism for f∈F.

The exceptional quotient really has dimension two. In multidegree (2,2) on A² the Hodge space has dimension four, corresponding to Q×F. Its divisor-generated subspace corresponds to Q×Q and has dimension two. The other Künneth pieces of H⁴(A²) have invariant dimensions 1,1,1,1 in bidegrees (4,0),(3,1),(1,3),(0,4), respectively; these are divisor-generated. For the odd pieces, Λ³V contains V with multiplicity one, also represented by multiplication by θ. Thus

    dim Hdg⁴(A²)=8,      dim D²(A²)=6,
    Hdg⁴(A²)/D²(A²) ≅ F/Q.

The three-dimensional Q_f-space contains an algebraic scalar direction f=1. “Two exceptional classes” means a quotient or a choice of complement, for example trace-zero F, not two canonical individually distinguished cycles. At CM fibers these dimension and commutant equalities generally change.

## 4. Degree and Tate-twist repair

Use Q(1) of weight −2. For g=4 and an ample θ∈H²(A,Q(1)), define

    L² : H²(A,Q) → H⁶(A,Q(2)),       u ↦ uθ²,
    B₂(u,v) = ∫_A uvθ² ∈ Q(−2).

Hard Lefschetz says B₂ is nondegenerate. It identifies (H²)∨ with H²(2), so the correct Hodge-structure identification is

    End(H²(A)) ≅ (H²(A)⊗H²(A))(2) ⊂ H⁴(A²,Q(2)).

Let c_f denote the class corresponding to f₀. Thus c_f is the properly twisted version of the scout's Q_f. Untwisted it has type (2,2). The asserted untwisted isomorphism End(H²)≅H²⊗H² is not an isomorphism of Hodge structures: its two sides have weights zero and four.

An actual degree-preserving endomorphism is represented by

    Γ_f = pr₁^*θ² ∪ c_f ∈ H⁸(A²,Q(4)),

where pr₁^* is pullback. Explicitly, if c_f=Σu_s⊗v_s, then

    (Γ_f)_*(x) = Σ (∫_A x u_s θ²) v_s = f₀(x).

Γ_f has codimension **4**. In contrast, a bare codimension-2 cycle on A×A acts by H^k→H^{k−4}; it cannot act on H² as a nonzero degree-preserving map. This is a real type error if the scout's statement is read literally.

The correction is algebraic in both directions:

- An algebraic c_f gives Γ_f by intersection with pr₁^*θ².
- An algebraic degree-preserving cycle inducing f₀ on H² can first be projected to H⁶⊗H² with algebraic Künneth projectors. Apply the algebraic inverse of L² to its first leg to obtain c_f. The inverse is a correspondence in CH²(A×A)_Q, acting H⁶→H² with twist −2. Künneth projectors are polynomials in the action of multiplication-by-m, for m>1, since its eigenvalues m^k are distinct. Thus their algebraicity does not presuppose HC.

For four multilinear legs use

    B₁(v,w)=∫_A vwθ³ : V⊗V → Q(−1).

An algebraic t∈V^{⊗4}(2)⊂H⁴(A⁴,Q(2)) yields, on Y=A², a correspondence

    Γ_t = pr₁^*θ³ pr₂^*θ³ ∪ t ∈ H¹⁶(Y×Y,Q(8)).

Its multidegree is (7,7,1,1), and it induces an endomorphism of V⊗V⊂H²(Y). The correspondence has codimension **8=dim Y**, so ordinary composition preserves this degree. With the usual external-product ordering, the Poincaré pairing on the two odd legs is **−B₁⊗B₁**: regrouping (v₁×v₂)(w₁×w₂) introduces one minus sign. Accordingly, use −Γ_t if identifying its action with the ordinary tensor contraction convention of the code. This is a fixed normalization, not a missing nonalgebraic operation. Applying the algebraic inverse H⁷→H¹ of L³ to the two source legs returns a tensor in H⁴(A⁴,Q(2)). Each inverse is represented by CH¹(A×A)_Q. This is the precise meaning of the tensor “composition” used in the code. Directly composing raw CH²(A⁴) cycles as correspondences on A² would instead have formal codimension 2+2−8=−4 and does not implement that code.

The identification of the initial q_i-tensors also needs one sentence. Pull back c_f along addition in each factor, then apply π₁ on all four legs. On H² this is the antisymmetrizing inclusion Λ²V→V⊗V, up to the explicit nonzero factor 2 on each pair. The form induced by Λ²B₁ and the form B₂ agree up to a nonzero rational scalar on P²: P² is the irreducible primitive Sp₈ representation and both forms are Sp₈-invariant and nondegenerate there. Thus the lifted classes span precisely the q_i-tensors used below, after a common rational normalization. The θ projector and this change of normalization are algebraic. No unproved Hodge correspondence has been smuggled into the lifting step.

## 5. Independent audit of the finite algebra

The scout script was read in full and rerun with output redirected only to the assigned experiment directory. Its reported ranks reproduce. An independent standard-library implementation, `../experiments/geo_mumford_review_r2/independent_tensor_audit.py`, does not import the scout or prior-art code. It calculates the one-factor epsilon contractions from their coordinates, all 24 leg permutations, the projector identities, exact ranks, and the symbolic certificate below.

For one SL₂ factor put a=ε₁₂ε₃₄, b=ε₁₃ε₂₄, d=ε₁₄ε₂₃. With the pairing convention used by the scout,

    d=b−a,       a²=2a,       ab=ba=a,       b²=b.

There is no bad loop sign in the scout's composition. The inverse symplectic matrix differs by a minus sign; two contractions cancel this difference. In the eight-dimensional three-factor algebra set x_i=a_i/2, with identity b in the other slots. Then x_i²=x_i, and

    p=x₁x₂x₃,
    q_i=x_i(1−x_j)(1−x_k),
    total swap=(1−2x₁)(1−2x₂)(1−2x₃).

The q_i are orthogonal rank-nine projectors supported on Λ²V, and p is the rank-one θ projector. Their sum with p is (1−total swap)/2. The scout's comments suggest checking this last support assertion but its assertions only check idempotence; the independent audit checks the support and orthogonality too.

**Permutation correction.** On V^{⊗4} written as a Künneth component of H⁴(A⁴), a geometric permutation acts as its ordinary tensor permutation times its sign, because all four legs have odd degree. The scout implements the ordinary permutation. This does not change any span or algebraicity conclusion: multiplication by −1 is allowed. It is nevertheless necessary to state the convention. In particular a tensor symmetric under ordinary permutations appears with the sign character under geometric factor permutations.

**Symbolic replacement for closure.** Let R be the ordinary transposition of legs 2 and 3; on each factor it exchanges a and b. Geometrically use minus the corresponding pullback. Put r_i=R(q_i). Then

    r_i=2x_jx_k−(x_j+x_k)/2+1/8,
    d_ij := 4(q_i−q_j)/3 − 2(r_i−r_j)/3 = x_i−x_j.

Using x_i²=x_i gives the explicit identity

    s := Σ_{i<j} d_ij² − Σ_i q_i + 3p = x₁+x₂+x₃,
    x_i = (s + Σ_{j≠i} d_ij)/3,      d_ji=−d_ij.

Thus the q_i, the Lefschetz tensor p, leg permutations, and compositions produce every x_i. Since b_i=1, every one of the eight monomials in the a/b tensor basis follows. These are polynomial identities in the algebra Q[x₁,x₂,x₃]/(x_i²−x_i), not an induction guessed from finite experiments.

Exact checks give: initial span 5; S₄-span 7; with composition 8; Lefschetz-only closure 3. The independent script verifies the displayed certificate. **Computation status:** supporting exact finite validation only. **Proof status:** the displayed algebraic identities prove the required finite generation step without relying on program correctness.

## 6. All arities and rational descent

Let W_alg(r) be the rational span of classes of algebraic cycles in the multilinear Hodge component V^{⊗2r}(r) on A^{2r}. All closures discussed here are closures of cohomological cycle classes; no claim about rational equivalence or algebraic Chow idempotents is needed.

If every c_f is algebraic, then after extending coefficients to Qbar the q_i are in that span: for a Q-basis f₁,f₂,f₃ of F, the matrix (σ_i(f_j)) is invertible. This is separability of F (its discriminant is nonzero), not the false assertion that numerical embeddings themselves are rational coefficients. The degree-four symbolic calculation therefore supplies x_i and the partial ordinary swaps s_i=1−2x_i in the Qbar-span of algebraic correspondences.

For any m, insert each partial swap in adjacent positions of V^{⊗m}. This is realized by the exterior product of its codimension-eight correspondence on A² with diagonal correspondences of codimension four on the other factors. The resulting cycle on A^m×A^m has codimension 8+4(m−2)=4m and preserves V^{⊗m}. Compose such cycles to obtain independent permutations of the m copies of each W_i.

For every r, SL₂ invariants in W_i^{⊗2r} are spanned by epsilon perfect matchings, by the first fundamental theorem. Each matching is a permutation of the standard adjacent pairing. Consequently the three-factor invariants are spanned by independent partial permutations of the algebraic polarization tensor

    ω^{⊗r} ∈ V^{⊗2r}(r),      ω=ε₁⊗ε₂⊗ε₃.

This yields every invariant at every arity. Equivalently, Schur–Weyl duality says that the commutants of W_i^{⊗m} are generated by adjacent swaps; the Temperley–Lieb image is generated by 1−s_i. This proves precisely the all-arity step the finite experiment alone cannot establish. Individual W_i or their matchings need not descend to rational motives.

Descent is elementary and finite-dimensional: for a Q-vector space H and subspace W, the kernel of H→(H/W)⊗_Q Qbar is W. Thus a rational class lying in W_alg(r)⊗Qbar belongs to W_alg(r). No averaging of complex cycles and no descent of the individual q_i is asserted. Complex coefficient extension does not enlarge the rational algebraic span.

Finally, the exterior quotient

    V^{⊗2r}⊗(Q^n)^{⊗2r} → Λ^{2r}(V⊗Q^n)=H^{2r}(A^n)

is surjective and G-equivariant. Since G is reductive in characteristic zero, it is surjective on invariants. For an integral tuple of vectors in Q^n the resulting map is pullback along an actual homomorphism A^n→A^{2r}; integral pure tensors span the required coefficient tensor space over Q. Pullbacks preserve algebraicity. This proves rational HC in every codimension on every A^n, with all quantifiers accounted for.

## 7. Repaired theorem and the elliptic factor

**Repaired B1.** Let A be a Mumford-type fourfold in the actual-Hodge-group sense above, let F=End_Hdg(P²) be its totally real cubic field, and define c_f using B₂ as in §4. The following are equivalent:

1. Every rational Hodge class on A^n is algebraic for every integer n≥1.
2. Every c_f∈H⁴(A²,Q(2)), f∈F, is algebraic.
3. Every rational codimension-two Hodge class on A² is algebraic.
4. For every f∈F there is a cycle in CH⁴(A×A)_Q inducing f on P² and zero on Qθ.
5. For **one** f∈F\Q, c_f is algebraic.

Proof: (1)⇒(3)⇒(2) is immediate. Sections 4–6 prove (2)⇒(1) and (2)⇔(4). For (5)⇒(2), convert to a degree-preserving correspondence. The algebraic primitive projector supplies 1∈F; polynomial composition supplies Q[f]=F because [F:Q]=3. Convert back with algebraic inverse Lefschetz. This also explains why “two exceptional dimensions” does not mean two independent geometric seeds are logically necessary. This one-generator observation is a routine field-algebra consequence, not a claimed novel theorem.

For every complex elliptic curve E, Moonen–Zarhin 0.2(iv) gives

    Hg(A×E)=Hg(A)×Hg(E).

Indeed A×E is in none of (e),(f),(g); in particular End⁰(A)=Q rules out (g). This holds for both CM and non-CM E, with no genericity hypothesis on E. A rational Goursat explanation is also available: the Q-simple nine-dimensional Lie algebra of Hg(A) shares no nonzero quotient with sl₂ or a torus. The real noncompact sl₂ factor alone is not a rational quotient and cannot create a hidden diagonal link.

The **MT** group is not generally the product of the two MT groups: the weight/similitude scalar is shared. Up to central isogeny it is Hg(A)×Hg(E)×G_m. The Hg-product statement is exactly what is needed for Hodge classes. Invariants on (A×E)^n are external products of invariants on A^n and E^n; elliptic powers are divisor-generated. Conversely, restriction along A^n×{0} recovers A^n. Thus the analogous all-powers and codimension-two-square assertions for X isogenous to A×E are equivalent to those for A, and the c_f condition is interpreted on the A factor.

Combining this theorem with §2 yields the global Corollary B, with **codimension-four correspondences** in its endomorphism formulation. **Classification: proved conditional reduction/equivalence, not an unconditional algebraicity result.**

## 8. CM points, specialization, and the proposed geometric input

The corpus CM theorem does prove algebraicity of the distinguished generic tensors at CM fibers. It does not prove that they deform as cycles. In a smooth projective family, for a fixed flat rational class (after a suitable level/base change if needed), cycle parameter spaces produce a countable collection of closed algebraic loci where representatives occur. Countably many CM points may lie on countably many distinct zero-dimensional loci. Neither density nor their countability supplies a dominating cycle family. The generic-rank description Q×F also cannot be reused as the full Hodge commutant at a CM point, where it can enlarge.

There is no contradiction with the corpus finite-field specialization statements: specializing an algebraic class, or producing an algebraic representative of its specialization, does not lift that representative back to a prescribed complex fiber.

The last “precise open input” in §5.3 needs more hypotheses to be a precise deformation criterion. A suitable semiregular sheaf could work, but one must verify semiregularity on the **full obstruction space**, show its **entire relevant Chern character remains of Hodge type** along the intended family (not just a nonzero exceptional component), and justify passage from local deformation to the desired global fibers. A cycle with nonzero projection alone has no such deformation guarantee. Once an actual algebraic nonzero exceptional class on the given A² is produced, §7(5) does supply the whole field; the issue is producing/propagating that class.

The observation that this Shimura curve is not PEL is relevant, but “no weight-one standard representation exists” is too broad: V itself is an eight-dimensional weight-one representation. What fails is obtaining the desired rational two-dimensional constituent representations as abelian factors with independent Hodge data. The scalar extension A⊗O_K has dimension eight, so the quoted ≤5 and split-sixfold corpus theorems do not apply; the withdrawn eightfold notice supplies no repair. The auxiliary nine-dimensional K3-type structure and the relation KS~A^{32} have older antecedents (Galluzzi), so they are not new constructions here either.

## 9. Novelty search, significance, and reproducibility

The search covered primary Moonen–Zarhin statements, Galluzzi's institutional article record and Hazama-class article, Zhu's [K3 surfaces associated to abelian fourfolds of Mumford's type](https://arxiv.org/abs/1812.06882), the corpus introduction's prior-art discussion, and the exact H8 source described above. Galluzzi's full Hazama PDF could not be fetched because of server/TLS failures; I do not claim to have excluded the all-powers result from that inaccessible article. This limitation does not weaken the affirmative exact match in H8.

The copied H8 source has SHA-256 `3a5e9ea7f5513981eb9ee70eb6139ea6a0e6e5a680fc95a1b55161fe232de4e5`. The immutable-commit download is byte-identical to the release source. GitHub's commit metadata dates the commit to 2026-10-02, consistent with the independent Zenodo release date. Specific inspected source locations are `prop:mumfordrm` (lines 54–113) and `thm:mumfordpowers` with its proof and following remark (lines 543–664). The source proof's finite step uses computation; the independent symbolic certificate in §5 removes that reliance for this review. No acceptance of the source's other results is required.

The repaired theorem isolates a difficult outstanding case related to the landmark Hodge conjecture (MathDB #315851), but it constructs no exceptional cycles. The low-dimensional assembly is routine under accepted corpus inputs, and the all-powers reduction is already present in public primary source material. It therefore does **not** meet the user's request for genuinely new substantive progress. A claim that the general Mumford-square obstruction has now been solved would be false; a claim of new-to-literature B1 is unsupported and contradicted by the identified prior source.

Validation commands, run successfully:

```sh
python3 -I openai-proof-research/frontier/experiments/geo_mumford_review_r2/independent_tensor_audit.py
python3 -I openai-proof-research/frontier/experiments/geo_mumford/tl_closure.py
```

Outputs are saved only in `../experiments/geo_mumford_review_r2/independent_tensor_audit.out` and `scout_rerun.out`. The former independently verifies the epsilon signs, all leg actions, orthogonality and wedge support, ranks, and polynomial certificate. The latter reproduces the original claimed ranks. Neither is offered as a finite computational proof of infinitely many arities, of geometric realizability, of rational descent, or of algebraicity of any new exceptional class; those distinctions are addressed explicitly above.

**Integration recommendation:** retain B0/B1 only as a corrected, attributed frontier reduction; remove them from the list of candidate genuinely new substantive theorems. The repaired proof can be useful supporting documentation. Do not promote the CM or semiregularity discussion to an unconditional result.
