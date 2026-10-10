# I104 — Modular representation theory and tensor categories: discovery report

**Disposition: no substantial finding nominated.** Four exact targets were screened. The selected target is the blockwise Galois Alperin weight conjecture, with coefficient-Galois equivariance only. Two routes were developed: a twisted cocenter/tuple route and a descent route retaining the Frobenius action on simple modules. The report proves a trace identity, an equivariant subsection bridge, an all-length calculation and uniform estimate for a specific generating-tuple problem, a family of connected symmetric algebra forms, and a finite rank-profile reconstruction. These are **author-proved technical results**, subject to the parent's separate review. They do not prove the selected conjecture or qualify as one of the ten substantial findings. No independent mathematical audit, worldwide-priority claim, human review, or formal certification is claimed.

All theorems and lower operations in `openai/math` at **fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb** are accepted. Nothing here audits or disputes an upstream assertion, or uses a contradiction to manufacture a conclusion. No child agents, shared edits, staging, commits, or publishing were used.

## 1. Scope, sources, and the four screens

The four current ledgers were snapshotted before discovery: `README.md`, `frontier/README.md`, `frontier/TEN-FINDINGS.md`, and `frontier/iterations/README.md`. Their current status and relevant summaries were read; the first combined terminal dump of historical material was truncated, so this is not a claim of reading every historical word. Eight findings remain accepted. Signed Saxl and elementary chromatic positivity are parked; I100/I102 have technical bridges but unresolved main targets; Q90/Q91/C80 are technical consequences. I101/I103 working outputs were neither read as dependencies nor bound into this package.

Use the following pinned manuscript abbreviations. Every path, original blob hash, representation hash, and local location is in `../sources/i104_modular_representation_discovery/selected-inventory.json`. `passages.json` records the precise ranges used below, their hashes, and line conventions. The raw URL of each source is `https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/` followed by its `preprints/...` path.

| Key | Pinned manuscript | Statements and complete operations particularly used |
|---|---|---|
| D | Donovans-Conjecture-over-Algebraic-Closures-of-Prime-Fields-September-24-2026 | `00_introduction.tex`; `07_extensions.tex` based Sylow descent and large-kernel removal, lines 350–740; `08_periodicity.tex` exact component comparisons, return of Levi blocks, assembly and scalar extension, lines 1–930 |
| ID | Integral-Donovan-Finiteness-over-Witt-Vectors-September-25-2026 | `03_rigidity.tex`, `04_comparison.tex`, `05_sylow.tex`, `07_assembly.tex`, all through their endings |
| A | The-Blockwise-Alperin-Weight-Conjecture-September-23-2026 | `intro.tex`; complete `group.tex` 1–839; `valuations.tex` 495–771, including the marked-cover proof through its ending; complete `specialization.tex` 1–730; complete `consequences.tex` 1–171 |
| V | Fiber-functors-for-finite-symmetric-tensor-categories-in-positive-characteristic-September-24-2026 | Introduction, projectivity, support, descent, restricted-tilting construction, and consequences, each through its ending |
| S | Tensor-Saturation-for-Even-Spin-Groups-September-24-2026 | `01-introduction.tex`; complete column realization `05-columns.tex`; complete preprojective criterion/zero-tail/completion `06-zero-tail-completion.tex` |

This is selective complete proof reading of the operations used, **not** semantic reading of the whole repository or all proofs of D/V/S. In particular, the rank-support/descent argument in V and the column/completion argument in S were not inferred from titles. The full 10,373-position lexical search and its limitations are recorded in §8.

**B104: splendid abelian-defect Broué.** For every prime p, finite group G, block b with abelian defect P, and complete discrete valuation ring R of mixed characteristic (0,p) with algebraically closed residue field k and fraction field splitting G and N_G(P), construct a bounded splendid Rickard complex between RGb and RN_G(P)c, where c is the Brauer correspondent. Precisely, its terms should be finite p-permutation bimodules, projective on each side, relatively projective for the diagonal subgroups ΔQ, Q≤P (and their G×N_G(P) conjugates), and its dual should give the two homotopy inverse tensor identities. No bound on the amplitude is included. This is a complex/equivalence target, not equality of invariants. ID already gives integral Morita finiteness over W(k), and then for each fixed complete coefficient DVR; it does not construct a complex to the correspondent. W(k)'s fraction field must not be treated as splitting p-power roots. The ramification index of a splitting R is not assumed bounded. The accepted lower construction preserves actual crossed factors; that is stronger than mere numerical finiteness, but its endpoints are Frobenius-related identity blocks, not the Broué pair. Kessar–Linckelmann's accepted manuscript has splendid descent and the cyclic-defect construction; these do not cover all abelian P. This screen was not selected: no mechanism for differentials or inverse identities emerged.

**G104: blockwise Galois Alperin weights (selected).** For every prime p, finite G, k=F̄_p, and block idempotent b∈kG, put F=F_p[b]=F_q (the field generated by its coefficients) and Γ_b=Gal(k/F). Seek a Γ_b-equivariant bijection

    S(kGb) ≅ ⨿_[Q≤G, Q a p-subgroup] S_proj(k[N_G(Q)/Q] · overline(Br_Q(b))).        (G104)

Here the bar is quotient by Q after viewing the Brauer image in kN_G(Q); S_proj denotes isomorphism classes of modules that are both simple and projective; subgroups are taken up to G-conjugacy, with the usual conjugation identification of pairs. Q=1 is included. Γ_b acts only on coefficients and the module label, not on Q. There is no assertion of Aut(G)-equivariance, character-triple compatibility, Morita equivalence, or a complex. A proves equality of the two cardinalities, including the block assignment. The problem asks to recover the finite cyclic permutation action forgotten by that equality.

This is the named **blockwise Galois Alperin weight conjecture** of Huang–Yılmaz, Conjecture 1.2; its significance here is evidenced by their chain and functorial reformulations and the separate current H-triple reduction of Feng–Fu–Zhou. No ranking is asserted. The MathDB search did not yield a usable specific problem page; the primary conjecture statements are the significance references.

**V104: finitely tensor-generated moderate-growth BEO.** For every algebraically closed k of characteristic p>0 and every pre-Tannakian symmetric k-linear category C (abelian, rigid, Hom-finite, finite-length objects, simple unit with End(1)=k), generated by one object under finite direct sums, tensor products, duals, subquotients, and with length(X^⊗d)≤C_X^d for all d≥1 and each X, seek an exact faithful k-linear strong symmetric monoidal functor to some Ver_{p^n}(k), n≥1 depending on C. No enough-projectives or finite-simple-set hypothesis is imposed. A functor to the tower union would have image in a single level in this finitely generated setting, since the generator's image lies in a level and the levels are full tensor subcategories closed under subquotients. This is a finitely generated case of the full Benson–Etingof–Ostrik problem, not the finite-category theorem already supplied by V. V already proves full restricted tilting for every E_r-module, exact higher Frobenius selection for a finite category, finite-simple dimension descent, the incompressible classification and internal affine-group reconstruction. The least-r argument uses a projective generator and the descent uses a finite directed graph. Merely applying the finite theorem to subcategories generated by objects does not supply those hypotheses. Coulembier–Flake's published September 23, 2026 version was checked for the higher-Frobenius interface. No compatible replacement for those two finiteness inputs was constructed; this screen was not selected.

**S104: all tensor arities in type D.** For every n≥2, m≥3, dominant integral weights λ_1,…,λ_m of Spin(2n,C), with Σλ_i∈Q(D_n), and N≥1, seek the implication

    (⊗_i V(Nλ_i))^G ≠ 0  ⇒  (⊗_i V(λ_i))^G ≠ 0.

This asks for semigroup membership at factor one, uniformly in rank and arity, not preservation of multiplicity or a tensor exponent. S explicitly supplies all ranks, all half-spin weights, and arity three at factor one. Its column construction composes coefficients into the Cartan summand of the *second factor*; a list of fundamental columns there is not an arbitrary m-factor tensor product. An associativity triangulation at scale N has internal dominant labels not necessarily divisible by N. I did not prove integral compatible internal labels or exclude a stronger existing polygon reduction, so this is a screened possibility, not a certified remaining literature gap. Kumar's primary survey §10 was also checked: the Levi-branching transfer is already a standard saturation-factor consequence and cannot be nominated. No fixed-rank computation or factor-two/four assertion was substituted for S104.

## 2. Stronger companions and versions checked

The following sources are frozen in `external/`, with retrieval status, URLs, hashes and extraction commands in the retrieval manifests. Published HTML, PDF and arXiv versions are kept distinct.

* [Huang–Yılmaz author manuscript](https://yilmazdeniz.bilkent.edu.tr/papers/awc-galois-functorial.pdf), 15-page author PDF, read in full, plus [arXiv:2512.07369v1](https://arxiv.org/pdf/2512.07369v1). The arXiv record exposed only v1 (December 8, 2025); an attempted v2 HTML lookup failed and is retained in the web record. The article is [Journal of Algebra 701 (September 1, 2026), 312–327](https://www.sciencedirect.com/science/article/pii/S0021869326002243). The author PDF is identified by URL and hash, not assigned an invented revision date. Theorem 1.4 is a **universal** chain reformulation; its remark does not grant an individual-block equivalence from one chain equality. Theorems 1.7/1.9 and Corollary 1.8 require distinguishing functorial equivalence over the minimal field from one over algebraically closed coefficients. Their complete relevant proofs were read. A's functorial consequence is a Grothendieck-group identity over algebraically closed coefficient fields; it does not supply the minimal-field equivalence required here.
* [Feng–Fu–Zhou, arXiv:2512.15243v2](https://arxiv.org/pdf/2512.15243v2), April 24, 2026; v1 retained as superseded evidence. The exact introduction, reduction theorem, and final induction/construction were read through the conclusion. The hypothesis is an **inductive** blockwise Galois condition for universal p′-covers of nonabelian composition factors, including compatible H-triples; numerical AWC does not discharge it. The full stronger statement also has automorphism equivariance. The defining-characteristic verification is not an all-group proof. Earlier imported character-triple theorems are attributed to the authors, not independently audited here.
* [Huang, arXiv:2604.06166v3](https://arxiv.org/pdf/2604.06166v3), May 7, 2026, checked against the live metadata; the initially retrieved April 7 v1 is retained. The final metadata inspection exposed v3, so its expanded constructions in §§2–6 were then read through the final proof. General finite category GAWC reduces to the group version; blockwise extension is for EI-categories. Twisted versions require an F_p^×-valued cocycle extending to the orbit category. The added Theorem 1.20 transports an (H×Aut(G_e))-equivariant family for the maximal subgroups to the category; its hypothesis remains equivariant group correspondences, not numeric counts. Theorem 5.10 also relates twisted EI-category algebras to explicit central extensions. Consequently neither a category reformulation nor this stronger automorphism version supplies a missing group comparison.
* [Kessar–Linckelmann accepted manuscript](https://openaccess.city.ac.uk/id/eprint/21525/1/characterrationality14Feb18.pdf), exact downloaded 2018 version. Theorem 3.4, Theorem 6.5 and the cyclic-block descent proof through Theorem 1.12 were inspected. In Theorem 6.5 the finite residue extension and minimal fields of the **geometric blocks** are part of the hypotheses. Summing their distinct conjugates descends an equivalence of orbit-sum blocks; this does not manufacture an equivariant equivalence between two already geometrically connected blocks over their common field. The unramified assumption in the character-equivariance statement is retained.
* [Du–Huang published theorem](https://link.springer.com/article/10.1007/s00209-025-03803-w), June 18, 2025, explicitly covers symmetric and alternating groups. The accessible publisher theorem/abstract and the citations in the two full papers establish the scope; its subscription proof was not independently read or used as a proof input. The A5 calculation below is thus a diagnostic of the *tuple mechanism*, not a new group-family case of G104.
* [Coulembier–Flake published version](https://link.springer.com/article/10.1007/s00029-026-01204-3), September 23, 2026; [Kumar's primary saturation survey](https://www.math.ucdavis.edu/~kapovich/EPR/eigensurvey2.pdf), §10. These are interface/scope checks, not substitutes for V's complete finite-category constructions or S's complete realization/completion proofs.

## 3. Route I: retain Frobenius in the cocenter

### 3.1 Exact power and coefficient conventions

Let H be finite, p prime, k=F̄_p, and a≥1. Write σ_a for the coefficient automorphism z↦z^{p^a}. Let e=e_p e_{p′} be the exponent of H, with e_p a p-power and (e_{p′},p)=1. Choose t modulo e by

    t ≡ 1 (mod e_p),       t ≡ p^a (mod e_{p′}).                         (1)

Thus t is a unit modulo e. Work, for traces, over a complete splitting mixed-characteristic DVR O containing the roots needed for H, with residue k and fraction field K. One can take W(k) adjoined a primitive e_p-th root; extending Witt σ_a by fixing that root realizes the cyclotomic automorphism γ_t. There is no assertion that W(k) itself is splitting or that this choice has a group-independent ramification bound.

For any coefficient ring R, V(RH)=RH/[RH,RH] has the conjugacy-class basis. Define the **R-linear** operator L_t([g])=[g^t]. It has finite order. It is not asserted to be an algebra map. Over K, the coordinate χ([g])=χ(g) identifies V(KH) with one trace-coordinate line per ordinary irreducible character. The equality χ(g^t)=γ_t(χ(g)) shows that L_t permutes these coordinates by χ↦χ^{γ_t}, up to the harmless inverse convention on basis vectors.

### 3.2 Equivariant subsection bridge (technical consequence)

If E∈Z(kH) is an idempotent fixed by σ_a, let Ẽ be its unique central idempotent lift. Then

    |Irr(H,Ẽ)^{γ_t}| = Σ_[u a p-element of H]
                       |S(kC_H(u) Br_<u>(E))^{σ_a}|.                 (2)

**Proof.** Multiplication by Ẽ commutes with L_t: in the K trace coordinates it is diagonal with entries 0/1, and γ_t preserves exactly its selected set, because σ_a(E)=E. The commuting equality therefore holds on the O-lattice as well. For C=C_H(u), the stable image of the cocenter p-power operation is the p-regular class span. Its map to V(kC/rad(kC)) is an isomorphism by A, `group.tex` 271–315, including compatibility with central idempotents. In matrix-trace coordinates the k-linear L_t on this span permutes the simple labels according to σ_a: on a p-regular g, Tr(ρ(g^t))=Tr(ρ(g))^{p^a}, which is the trace of the coefficient-twisted representation. This identity on the class basis proves equivariance on the whole span.

A's subsection isomorphism [v]↦[uv] identifies this span in C with the u-section in V(kH), and intertwines multiplication by Br_<u>(E) with multiplication by E (`group.tex` 340–361). Since t≡1 modulo the order of u, (uv)^t=uv^t. Hence the section isomorphism also intertwines L_t. The reduction of V(OH)Ẽ, as a module for the finite cyclic group generated by L_t, is therefore isomorphic to the permutation module on the disjoint union of the simple-label sets on the right of (2).

We must lift this assertion before taking an integer trace: a trace congruence modulo p would not suffice. The lattice V(OH)Ẽ is a direct summand, with commuting idempotent, of the permutation lattice on all H-classes. The other lattice is the permutation lattice on that disjoint union. For any two permutation lattices over O, reduction of equivariant Hom onto the corresponding Hom over k is surjective: its matrices have entries constant on each diagonal orbit of the two bases, and these entries can be lifted independently. The same surjectivity holds for direct summands, by composing a lift with the two idempotent projections. Lift the above k-isomorphism. Its source and target are free O-modules of the same finite rank, and its determinant is nonzero modulo the maximal ideal; it is consequently an O-isomorphism. Its trace of L_t over K equals the integer number of fixed basis elements of the right-hand permutation lattice. On the left, the trace-coordinate description gives the number of fixed ordinary irreducibles selected by Ẽ. This proves (2), including when E is a sum of blocks or zero. ∎

This proof deliberately handles possible p-torsion in the cyclic action; no averaging by its order occurs. It is a refinement of accepted cocenter/subsection operations and classical permutation-lattice lifting, not a substantial nomination.

### 3.3 A paid twisted trace identity

For arbitrary central w=Σ_g α_g g∈KH, n≥1, and any t coprime to exp(H),

    Tr(M_{w^n} L_t | V(KH))
      = (1/|H|) Σ_{x,y,u_1,…,u_n∈H; u_1…u_n y^t=x y x^{-1}} ∏_i α_{u_i}.       (3)

No Frobenius condition on t is needed for (3). In trace coordinates its left side is also

    Σ_{χ∈Irr(H), χ^{γ_t}=χ} λ_χ(w)^n,                               (4)

where w acts as the scalar λ_χ(w) on the simple module χ.

**Proof.** Write β_z for the coefficient of z in w^n. The diagonal coefficient of [y] in M_{w^n}L_t([y]) is Σ_{z∼y} β_{z y^{-t}}. The map x↦xyx^{-1} has fibers of size |C_H(y)|. Thus the sum over class representatives is Σ_[y] |C_H(y)|^{-1} Σ_x β_{xyx^{-1}y^{-t}}. The inner sum is conjugacy-invariant in y, so replacing class representatives by all y gives |H|^{-1}Σ_{x,y}β_{xyx^{-1}y^{-t}}. Expanding β as convolution gives (3). In trace coordinates multiplication by w^n is diagonal with entries λ_χ(w)^n and L_t is a permutation. Only its fixed coordinates contribute to the diagonal, proving (4). Neither assertion requires M_w to commute with L_t. ∎

### 3.4 What the complete group reduction now requires

For a finite J with O_p(J)=1, h≥1, a≥1 and t satisfying (1), let N^t_{J,s}(M) be the number of **simultaneous J-conjugacy orbits of ordered generating tuples** (x,y,u_1,…,u_{p^s}) such that

    u_1…u_{p^s} y^t = x y x^{-1},

all u_i are p-singular, and their J-class multiset is exactly M. There is no quotient by permutations of the positions. A sufficient new input would be

    ∀J,p,a,h ∃s_0(J,p,a,h) ∀s≥s_0 ∀such multisets M:
                         p^h divides N^t_{J,s}(M).                  (TD)

It is enough that the threshold depend on J,p,a,h; it must not depend on M. This is presently an **unproved conditional input**, not a theorem.

Here is the full reduction of this input to G104, to delimit rather than conceal the gap. For any σ_a-stable central idempotent E of kG, take A's detecting element v=E(1-c_G), where c_G is the sum of the p-elements, and a central integral lift w supported on p-singular classes. A's detector gives residues 0 or 1 for all the central-character scalars of its restrictions to normal-chain stabilizers, including the removal of semisimple blocks at the trivial chain. In (4), λ^{p^s} tends in the valuation topology to its residue 0 or 1: for residue 0, valuations multiply by p^s; for λ=1+z, the binomial expansion gives valuation growth at least min(pv(z),v(z)+v(p)), hence eventual divergence to infinity. This works for every fixed finite ramification index. Thus twisted traces converge to the corresponding **fixed-ordinary-character counts**, rather than all ordinary counts.

Sum these traces with the source chain signs. A's nonnormal-chain toggle depends only on chain groups and commutes with the coefficient action, so one may use all strict chains. For an actual tuple let J be its generated subgroup, and let a_G(J) be the signed number of strict p-subgroup chains normalized by J. Equation (3) and the orbit size |G|/|H_chain| give exactly

    Φ_{p^s,t} = (1/|G|) Σ_{J≤G, O_p(J)=1} a_G(J) |J|/|Z(J)|
                         · Σ_M α(M) N^t_{J,s}(M).                  (5)

Indeed the admissible chains for a tuple are exactly those normalized by J; A's p-core insertion/removal involution cancels the other J. The simultaneous stabilizer of a generating tuple is Z(J), giving the displayed orbit factor; α(M) is constant on its multiset, since w has class-constant coefficients. These are precisely the lower operations of `group.tex` 742–839 with relation (3), not a newly assumed counting identity.

(TD) makes the numerator in (5) tend to zero: for each fixed h take the maximum threshold over the finitely many J≤G. Every coefficient α(M) is integral; a finite sum of arbitrarily many elements of p^h O is still in p^h O. The fixed denominator |G| has fixed valuation. Hence the limit is zero. Equation (2) and A's subsection-chain toggle convert the alternating fixed-ordinary counts to alternating fixed-simple counts. To check equivariance of this toggle, note that it inserts/removes a subgroup generated by p-elements; σ_a changes only the coefficient/module label, leaves those subgroups and conjugators unchanged, and commutes with restriction and Brauer projection. The paired labeled terms therefore have equal fixed-label counts. Finally A's finite chain inversion uses only conjugation, subgroup insertion, and quotient inflation; each commutes with coefficient twisting. Applied universally to all pairs and subquotients, it gives equality of the fixed-simple and fixed-weight counts for σ_a.

For a block defined over F_{p^f}, apply this argument to every a divisible by f. Both finite sets are acted on by the procyclic Γ_b through finite cyclic quotients. Equality of the fixed counts of every positive power of its generator implies the two finite permutation sets are isomorphic: if c_m is the number of m-cycles, fixed counts F(d)=Σ_{m|d}m c_m recover m c_m by ordinary divisor Möbius inversion. Pair cycles of equal length to obtain the required bijection. This proves the **conditional implication** (TD)⇒G104, not (TD).

The accepted source proves t=1 tuple divisibility using actual marked covers of a punctured genus-one curve. The full marked-cover classification, small-orbit descent, and no-small-cover specialization proof were read through their endings. Their geometric equation is the ordinary commutator relation, and their chosen field automorphisms fix the roots of unity used there. The equation y↦y^t in (3), with t coming from coefficient Frobenius, is an additional arithmetic condition on a handle generator. I did not construct a marked-cover object or degeneration carrying this condition, nor reduce it to the source's accepted covering operation while preserving generation and the exact multiset. Calling it a “twist” does not perform that construction.

A direct semidirect-product reduction also needs more than a power permutation of classes. Even for the admissible case H=S_3,p=2,a=1,t=5, the map g↦g^t is not an automorphism: for a transposition r=(12) and s=(23), (rs)^5=sr≠rs=r^5s^5. Thus it cannot serve as the acting automorphism in H⋊C_d. This disproves that specific proposed construction; it does not rule out a subtler group or cover encoding. A replacement must also keep all puncture entries p-singular, the prescribed multiset, the generating condition, and the growing length p^s required by the accepted estimate.

### 3.5 Counterexample attempt and a uniform positive estimate

There is a useful exact obstruction to the **overbroad** proposal “(TD) for every unit t,” and a different answer for the admissible Frobenius t. Let J=A_5, p=2, n=2^s with s≥1, and let every u_i be an involution (the only 2-singular class). Denote the number of generating simultaneous-conjugacy orbits satisfying (3)'s equation by N^t(n). Then

    N^7(n)  = 15^n − 4·3^n − 2·5^n + 3,
    N^17(n) = 15^n − 2·3^n − 2·5^n + 3,
    N^1(n)  = 15^n − 4·3^n + 3.                                   (6)

In particular,

    v_2(N^7(2^s)) = 1;
    v_2(N^17(2^s)) ≥ s+3;
    v_2(N^1(2^s)) ≥ s+4.                                           (7)

These hold for all s≥1, not only the checked range. The second estimate pays a concrete uniform bound s_0=max(1,h−3) for this J,p, all its admissible multisets, and a=1. More generally a odd has the same character action as t=17 in this calculation, and a even the same as t=1, so the weaker bound s+3 holds for **all a≥1**.

**Proof of (6).** Let T_t(H,n) count all tuples with entries in H, without the generation condition, and with u_i involutions. By (3), T_t(H,n)/|H| is the twisted trace of the nth power of the central involution sum of H. Möbius inversion on the subgroup lattice of A_5 gives the generating tuple count Σ_{H≤A5} μ(H,A5)T_t(H,n); its simultaneous-conjugacy action is free, since a generating tuple has stabilizer Z(A_5)=1. Divide by 60.

Here is enough detail to verify all subgroup and character input. The proper subgroups of A_5 are A_4 (five point stabilizers), D_10 (six normalizers of Sylow 5-subgroups), S_3 (ten normalizers of Sylow 3-subgroups), V_4 (five), C_5 (six), C_3 (ten), C_2 (fifteen), and 1. For completeness, an intransitive subgroup either fixes a letter, hence lies in an A_4, or preserves an orbit decomposition 3+2, hence lies in (S_3×S_2)∩A_5≅S_3. A transitive subgroup has order divisible by 5. Its Sylow-5 count is 1 or 6; the first puts it in D_10, and the second forces order 30 or 60. Order 30 would give an index-two subgroup, impossible because A_5 is generated by 3-cycles and every homomorphism from it to C_2 kills them. This proves exhaustiveness; the subgroups of the three listed maximal types give the remaining entries. Each V_4 lies in one A_4; each C_5 in one D_10; each C_3 in two A_4 and one S_3; each C_2 in one A_4, one V_4, two D_10 and two S_3, by counting incidences. The recursion μ(H,A5)=−Σ_{H<K≤A5}μ(K,A5) gives respectively −1,−1,−1,0,0,2,4,−60 for these proper types. Odd-order subgroups have T_t=0 because n>0 and they contain no involutions. Thus only A_5, A_4, D_10, S_3, C_2 contribute, with normalized coefficients 1,−1,−1,−1,+2 multiplying their traces.

The involution-sum eigenvalues, in irreducible-character order, are

| H | Eigenvalues |
|---|---|
| A_5 | 15, −5, −5, 0, 3 (degrees 1,3,3,4,5) |
| A_4 | 3,3,3,−1 (degrees 1,1,1,3) |
| D_10 | 5,−5,0,0 (degrees 1,1,2,2) |
| S_3 | 3,−3,0 (degrees 1,1,2) |
| C_2 | 1,−1 |

These values need no unverified character table. For A_5 the class sizes are 1,15,20,12,12. The permutation representation on five letters minus the trivial character has values (4,0,1,−1,−1) and norm one. The permutation representation on its six Sylow 5-subgroups minus the trivial character has values (5,1,−1,0,0), also norm one: an involution normalizes two Sylow 5-subgroups, a 3-cycle none, and a 5-cycle exactly one. There are five conjugacy classes, so the remaining two character degrees have squares summing to 18 and are both 3. Column orthogonality at an involution gives their two real values sum −2 and squares sum 2, hence both −1. At a 5-element, the two real values have sum 1 and squares sum 3, hence are (1±√5)/2. The two 5-classes are interchanged by nonsquare powering modulo 5; both t=7 and t=17 do this, so they exchange the degree-three characters. All the displayed eigenvalues follow from |class|χ(g)/χ(1). For A_4, its three linear characters factor through C_3, and its remaining degree-three character is the four-letter permutation character minus one. Thus t=7 fixes all its linear characters and t=17 exchanges the two nontrivial ones. The dihedral/S_3 values follow from the two linear characters and the two-dimensional characters induced from nontrivial inverse pairs of characters of the cyclic rotation subgroup; the latter vanish on reflections. The C_2 values are immediate. This supplies both the scalar and power-permutation data.

For even n, the five traces for t=7 are 15^n+3^n, 3·3^n+1, 2·5^n, 2·3^n, 2. For t=17 replace the A_4 trace by 3^n+1. For t=1 replace the A_5 trace by 15^n+2·5^n+3^n, keeping the t=7 A_4 trace. Taking the five signed coefficients proves (6).

**Proof of (7) and the Frobenius assertion.** For s≥1 every odd integer raised to 2^s is 1 modulo 8. The first expression in (6) is therefore 6 modulo 8, giving valuation exactly one. The factorization z^{2^{s+1}}−1=(z^{2^s}−1)(z^{2^s}+1), with the second factor of valuation one for s≥1, gives

    v_2(3^{2^s}−1)=s+2,
    v_2(5^{2^s}−1)=s+2,
    v_2(15^{2^s}−1)=s+4,

starting from s=1 directly. Rewrite the second expression in (6) as (15^n−1)−2(3^n−1)−2(5^n−1), and the third as (15^n−1)−4(3^n−1). The stated lower bounds follow. For q=2^a, the action on the 5-classes is nonsquare precisely for a odd, and the action on the C_3 linear characters is nontrivial precisely for a odd. All remaining characters contributing a nonzero eigenvalue are fixed. This proves the final assertion. ∎

**Retained failed idea.** The first exploratory reading treated t=7 as a q=2 lift because 7≡2 modulo 5. That is wrong: 7≡1 modulo 3, whereas 2≡2 modulo 3. No power of 2 has residues (2 mod 5,1 mod 3). The correct lift with t odd is 17 modulo 30. The initial diagnostic file and the corrected file are both retained. The t=7 counterexample falsifies only the unrestricted-power proposal. It neither refutes G104 nor audits the t=1 source theorem. The admissible A5 estimate is a small, completely paid bridge; it provides no bound for arbitrary J.

## 4. Route II: retain the field-of-definition action

### 4.1 What the integral comparison supplies

D and ID are substantially stronger than an unspecified finite list. They construct an integral (σ^m B_0,B_0)-Morita bimodule, with m bounded in terms of p and the defect-order bound M, and covariance maps for a pure p-subgroup S retaining the actual inner factors a_{s,t}. ID proves that the scalar discrepancy belongs to the Teichmüller roots of unity of order prime to p, before removing it using H^2(S,T)=0. The source's comparison exponent is not a coefficient-field or ramification-uniform algorithmic stopping certificate.

These operations return a block to a Frobenius twist of itself; they do not connect that block to the algebra of its weights. A Galois-compatible equivalence between prescribed endpoints would have to supply that correspondence first, together with a compatible semilinear descent operator and its cocycle identities. The finite-p-group Teichmüller normalization does not itself provide such an endpoint correspondence or a cyclic Frobenius descent datum. This is a statement about the supplied construction's contract, not a proof that no reduction could exist.

The following family tests the tempting general assertion that a geometric Morita class, Cartan data and a short geometric Frobenius period determine the needed arithmetic action.

### 4.2 Connected symmetric forms with different Frobenius cycles

For every finite field F=F_q and integer m≥2, let Q be the oriented cycle with m vertices and let

    A = FQ / (all paths of length m+1).

Let L=F_{q^m}, τ(a)=a^q, and define the associative skew truncated polynomial algebra

    B = L[x;τ]/(x^{m+1}),          xa=τ(a)x.                         (8)

Then A and B are finite-dimensional **symmetric** F-algebras, each of dimension m(m+1), and A⊗_F k≅B⊗_F k for k=F̄_q. Their common geometric algebra is connected, has Loewy length m+1 and Cartan entries 2 on the diagonal and 1 off it. Yet the q-Frobenius action on its m geometric simple modules is trivial for A and a single m-cycle for B. Consequently A and B are not F-linearly Morita equivalent.

**Proof.** The path basis of A consists of the m paths of each length 0,…,m. The elements a_j x^j, 0≤j≤m, give B as ⊕_{j=0}^m Lx^j; associativity follows from the automorphism τ, and (x^{m+1}) is a two-sided ideal. Thus both dimensions are m(m+1). Their arrow/x ideals are nilpotent with semisimple quotients F^m and L respectively, so equal their Jacobson radicals. After extension to k, the separable algebra L⊗_F k has primitive idempotents indexed by the m embeddings L→k. τ cyclically permutes them. The relation with x gives one arrow between consecutive vertices, with products giving one path of each length through m and zero at length m+1. Mapping these idempotents and arrow components to the path generators (choosing the cycle orientation accordingly) gives an isomorphism B⊗k≅A⊗k: the map respects all relations and is surjective between vector spaces of equal dimension.

For A define t_A to sum the coefficients of the m closed paths of length m. A product of two basis paths contributes exactly when their concatenation is a closed length-m path; reversing the factors then gives the corresponding closed path with the same coefficient. In all other cases both traces are zero. Hence t_A(uv)=t_A(vu). Each length-r path pairs nontrivially with its unique complementary length-(m−r) path, and these pairings separate the path basis, so t_A(uv) is nondegenerate.

For B set t_B(Σa_jx^j)=Tr_{L/F}(a_m). For monomials whose degrees r,s sum to m,

    t_B((a x^r)(b x^s)) = Tr(a τ^r(b))
                        = Tr(b τ^{m−r}(a))
                        = t_B((b x^s)(a x^r)).

Trace invariance under τ gives the middle equality. For all other sums of degrees both traces are zero, including products killed by the truncation. If u≠0 has lowest nonzero coefficient a_r, multiply on the right by b x^{m−r}; all higher coefficients disappear, and choose b with Tr(a_r τ^r(b))≠0. Such b exists because the finite separable field trace pairing is nondegenerate: the distinct embeddings are linearly independent, so the functional Tr is nonzero and multiplication by nonzero a_r and τ^r are bijective. Thus t_B is a symmetrizing form.

For geometric connectedness, the image of any central idempotent modulo the radical is a 0/1 scalar at each vertex. Commutation with the arrows, modulo radical squared, forces equal scalars at adjacent vertices, hence at all vertices. An idempotent in the nilpotent radical is zero; applying this also to 1−e shows the only central idempotents are 0 and 1. There is a nonzero path of length m and no path of length m+1, proving the Loewy assertion. In each indecomposable projective the m+1 successive path lengths visit its own vertex twice and each other vertex once, proving the Cartan entries.

For A all simple quotient factors are F, so Frobenius fixes each geometric vertex. For B the embeddings of L are one q-Frobenius cycle. Already over F the numbers of simple modules are m for A and 1 for B, so an F-linear Morita equivalence is impossible: an equivalence of module categories takes simples bijectively to simples. The common geometric algebra has an F_p path presentation, hence geometric coefficient-Frobenius period one up to isomorphism; that period does not distinguish the two forms. ∎

This is a construction for every m, including m divisible by p. It is **not** claimed to realize a pair of group blocks, a counterexample to G104, or a counterexample to D/ID. It rules out only the general-algebra inference from the listed geometric invariants. Additional group-block structure could still force compatible forms.

### 4.3 A finite rank profile that preserves the lost data

Let π permute L≥1 basis vectors over any field, with c_m cycles of length m. Put

    K(d)=dim ker(π^d−I),                 1≤d≤L.

Then define

    a_d = (1/φ(d)) Σ_{e|d} μ(d/e) K(e),
    c_m = Σ_{1≤j≤L/m} μ(j) a_{mj}.                                    (9)

Thus the ranks of I−π^d for d≤L determine the permutation action up to isomorphism. This statement includes characteristic p dividing cycle lengths.

**Proof.** On an m-cycle, π^d has gcd(m,d) orbits; a fixed vector has one arbitrary constant per orbit over every field. Therefore K(d)=Σ_m c_m gcd(m,d). The elementary identity gcd(m,d)=Σ_{r|m,r|d}φ(r) gives K(d)=Σ_{r|d}φ(r)Σ_{m:r|m}c_m. To verify the identity, classify the integers 1,…,gcd(m,d) by the order of their class in its cyclic group; there are φ(r) of order r. Divisor Möbius inversion gives a_d=Σ_{m:d|m}c_m. Substituting this into the second formula gives Σ_{ℓ≤L/m}c_{mℓ}Σ_{j|ℓ}μ(j)=c_m, since the inner sum is 1 for ℓ=1 and 0 otherwise. The latter Möbius identity follows by expanding ∏_{r prime|ℓ}(1−1). This proves both reconstruction and integrality of all the displayed quotients. ∎

For a finite-dimensional F_q-algebra with semisimple quotient presented as ∏_i M_{n_i}(F_{q^{m_i}}), its geometric simple-module Frobenius cycles have lengths m_i. Its number of simple modules after scalar extension to F_{q^d} is Σ_i gcd(m_i,d)=K(d). Indeed a finite field tensor product splits as gcd(m_i,d) copies of F_{q^{lcm(m_i,d)}}; this follows by grouping the m_i embeddings into orbits under q^d-powering. The radical extends under this separable scalar extension: its extension is nilpotent and the quotient just described is semisimple, which gives both inclusions. Matrix sizes do not change the number of simple modules. This proves the asserted interpretation, given the displayed standard semisimple decomposition.

Applying (9) to the two finite simple-label sets in G104 gives a concrete finite test once their Frobenius operators are supplied. A gives their common size L. Their coefficient-Frobenius actions are defined over the same F_q, including on the weight side because Brauer projection and the choice of projective simple constituents commute with σ. Equality of the two K(d) for d≤L would imply G104. The source finiteness theorem may bound L for fixed p and defect-order bound, but it does **not** construct equality of these profiles or an effective enumeration with a certified stopping point.

Integer kernel dimensions, not traces in k, are essential. On p symbols, the identity permutation and a single p-cycle have the same characteristic polynomial (T−1)^p and the same traces of every power in characteristic p: a p-cycle has trace 0 unless p divides the power, when its trace is p=0, and the identity always has trace p=0. Their K(1) are p and 1. This direct computation isolates exactly why residue-field trace identities alone cannot prove the equivariant statement.

## 5. What remains unpaid

Route I requires (TD) for arbitrary p-core-free J and the **admissible** coefficient powers (1), or a replacement cancellation estimate strong enough for (5), uniformly over the exact class multisets. The accepted genus-one-cover proof handles the untwisted relation. No compatible covering construction, uniform valuation estimate, or full reduction for the new relation has been proved here. The A5 bound has no dependence on rank/group complexity to extrapolate from; the p=3 and p=5 computations are evidence only.

Route II requires a comparison over the minimal field between the global and weight permutation data. A genuine minimal-field functorial equivalence would already discharge the relevant case by the strongest companion theorem. No such equivalence, descent datum, or equality of the rank profiles in (9) has been constructed. The symmetric forms show why forgetting that datum is not justified even for a geometrically connected symmetric algebra with fixed Cartan matrix and geometric Frobenius period one. They do not show that the group-block target is false.

The Feng–Fu–Zhou reduction is another exact stopping point: proving all its inductive H-triple hypotheses would solve a stronger problem, but the accepted numeric theorem is not the specified input. No numerical local–global identity has been promoted to a Broué complex, stable equivalence, derived equivalence, or Morita equivalence.

## 6. Full-scope reduction and contribution status

Before nomination, the actual positive scope was compared to the strongest accepted lower operations.

| Result here | Proof status | Full-scope reduction / novelty limit |
|---|---|---|
| Equivariant subsection bridge (2) | Author proof above | Accepted cocenter/subsection isomorphisms plus classical lifting of Hom between permutation summands; technical refinement |
| Twisted trace identity (3), conditional implication (TD)⇒G104 | Author proof above | Class-basis trace expansion plus accepted detector, chain toggles and inversion; the universal input remains missing |
| A5 formula and all-s estimate (6)–(7) | Author proof above | Explicit finite subgroup/character data plus a universal elementary valuation argument; no new GAWC group-family result, already covered by Du–Huang |
| Connected symmetric forms (8) | Author proof above | Skew polynomial/path-algebra construction and finite-field descent; obstruction to a broad inference, not a group-block counterexample |
| Rank-profile reconstruction (9) | Author proof above | Two Möbius inversions on a cyclic permutation; effective extraction without a new global comparison mechanism |
| G104 | Conjectural target | Unresolved and unrefuted here |
| Unrestricted-unit version of (TD) | Falsified proposal | A5,p=2,t=7 has valuation exactly 1 for every s≥1 |
| Small tuple/rank computations | Finite evidence | Cannot establish the universal statements; independent analytic proofs above carry the positive claims |

Classical tools were not by themselves grounds for rejection. The reason for **no nomination** is that the paid results do not construct the missing arbitrary-group arithmetic comparison, and their complete proved scope reduces to technical operations/explicit examples. A novel formulation or a conditional bridge does not satisfy the requested substantiality standard. Parent review remains necessary for any use of these proofs; no acceptance count is changed by this report.

## 7. Reproducible finite diagnostics and retained failures

`diagnostics.py` enumerates the subgroup lattices of S_3 and A_5 from permutations, performs exact modular convolution, removes all proper generated subgroups by recursion, and divides by |J|/|Z(J)|. Counts are computed modulo |J|p^8 before orbit division. It records s=0,…,10 for S_3,p=2,t=5 and A_5 at (p,t)=(2,7),(2,17),(3,13),(5,11). It also checks (9) on the 683 integer partitions of sizes 1,…,15. These are reproducibility checks, not proofs. The verifier replays them without writing.

The initial diagnostic record lacking the corrected t=17 case is retained as `diagnostics-initial.json`; the final record adds that case. The false identification t=7 with coefficient Frobenius was corrected before the mathematical conclusions and is explicitly recorded in §3.5. An initial shell read from the wrong working directory and one attempted external text read omitting `.pdf` from the filename failed; both were corrected without changing source bytes. Some large exploratory terminal reads were truncated and followed by bounded range reads for the proofs relied on. An attempted nonexistent arXiv v2 HTML lookup failed. These were discovery/read failures, not passing verification runs. No failed theorem was silently relabeled evidence for G104.

The first preseal verifier run failed its domain-multiset comparison because Python `Counter` had been given the tree dictionary (interpreted as a mapping of counts) instead of its keys. The failing JSON is retained as `validation-attempt-1.json`; the checker was corrected to compare the two actual path multisets. No corpus bytes or expected search results were changed to repair this checker bug. Later validation records retain their own outcomes.

## 8. Evidence boundary, inventory, and replay

The complete `sources/preprints-tree.json` has **13,223 entries, 749 manuscript families and 10,373 original blob positions**. `sources/tree.json` was not used as a complete domain. I104 reuses I88's augmented mapping: 9,340 I14 corpus originals, 257 other byte representations, and 776 PDF text representations tied to their original PDF blobs. Originals were not recursively copied or re-downloaded. The five selected manuscript inventories reference these immutable originals.

Three exact case-insensitive regex searches were run over every mapped representation. `queries.json` retains the expressions verbatim, and each `search-*.jsonl` retains the complete sorted multiset of occurrences (path, line, half-open character span, matched substring, full line). Counts are 297 companion occurrences in 25 families, 54 mechanism occurrences in 23 families, and 2,352 screen occurrences in 181 families. The title screen retains its complete matching-title list among all 749 families. This is a **full-domain lexical search**, not full semantic reading, a novelty certificate, or proof that no differently worded reduction exists.

All mathematical passage numbers use decoded UTF-8 `str.splitlines()`, one-based, unless explicitly noted otherwise. PDF form feeds create additional splitlines, so these numbers must not be replayed as `sed`/LF-only line numbers. `passages.json` retains both LF-only and splitlines counts, the full representation hash, exact range, and SHA-256 of the selected lines joined by LF with a final LF. Original bytes remain authoritative. Only the eight newly retrieved research PDFs are re-extracted by the final verifier, using `pdftotext -layout INPUT -` into captured stdout. It does not re-extract all 776 inherited PDF representations; it checks those representations and originals by hash.

Immutable live references are limited to AGENTS.md, the pin/catalogue/complete tree, the I88 mapping and its explicitly listed original/representation files. The four designated shared ledgers may drift; their frozen snapshots are checked instead. There is no binding to I101 or I103 working outputs. External HTTP responses, obsolete PDFs, metadata, exact retrieval manifests and the source snapshots are all included in the owned inventory.

Replay from the repository root:

    python -B frontier/experiments/i104_modular_representation_discovery/verify.py

The final verifier is offline and read-only: no network imports, downloads, writes, bytecode, repair or resealing. It checks the exact owned file inventory and each sealed file hash, immutable references, original SHA-256 and Git blob SHA-1 against the complete tree, complete regex occurrence multisets, selected passage hashes, selective external PDF extraction and the finite diagnostics. Its preseal mode is also read-only and has no seal-writing operation. Preparation scripts are separately named and are never imported or executed by the verifier. Validation is performed before the one final seal; the validation record is then frozen. The final replay reports its checks on stdout only. A passing replay means evidence integrity and reproducibility within these boundaries, **not universal proof or contribution certification**.
