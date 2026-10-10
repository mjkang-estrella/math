# I108 — Original-proof audit and Galois-compatible tuple divisibility

**Disposition: original mathematical claims PASS without repairs; G104 and admissible TD remain unproved and unrefuted here. No substantial finding is nominated.** The accepted count remains eight. The new paid bridge is an exact finite Teichmüller-moment criterion equivalent to the uniform, all-multiset TD assertion for a fixed group and power, with a uniform valuation threshold when the criterion vanishes. A second concrete result identifies the index cost of adding the proposed auxiliary puncture to the actual source curve. Neither constructs the missing arbitrary-group cancellation.

This is an independent agent-level audit, not human review, formal certification, or a worldwide-priority assertion. All theorems **and lower operations** of `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are accepted as premises. No upstream truth audit, inconsistency argument, or ex-falso deduction is used. No child agents, shared-index edits, staging, commits, or publication were used. Only the three assigned I108 paths were written. I106/I107 working files are not dependencies.

## 1. Frozen question and exact scope

The original I104 brief, report, and finalized parent response are frozen in `../sources/i108_galois_tuple_divisibility/`. The complete supplied I108 message and the two paginated T3 response envelopes are retained. The extracted prompt text has one documented terminal LF added; the response envelopes retain the exact emitted text. The report snapshot has the original parent-reported SHA-256 `3268c0b8765ad8962b07db8cef768ba06e04aef0785e35f76d822784e7bebf54`. The parent response is evidence of an evidence replay, explicitly **not** an earlier original-proof pass. My verdicts below concern the original mathematical text, before the new constructions in §§4–5. No alteration of I104 is made.

Write A for the pinned *The Blockwise Alperin Weight Conjecture*, D for the field Donovan manuscript, and ID for its integral Witt-vector companion. Their full original paths, Git blob hashes, representations, and the exact reading ranges are recorded in `passages.json` and `immutable-references.json`. Mathematical line ranges use UTF-8 `str.splitlines()`, one-based; passage hashes join selected lines with LF and append a final LF. LF-only line counts are also recorded. These conventions matter for inherited PDF text with form feeds.

G104 has exactly the I104 meaning. For every finite group G, prime p, block b of kG, k=F̄_p, F=F_p[b]=F_q, and Γ_b=Gal(k/F), seek a Γ_b-set bijection

\[
 S(kGb)\;\simeq\;\coprod_{[Q]\subseteq G}\ S_{\rm proj}\bigl(k[N_G(Q)/Q]\,\overline{\operatorname{Br}_Q(b)}\bigr).
\]

Here Q ranges over G-conjugacy classes of p-subgroups, including 1, with the source block assignment. Only coefficients are twisted; Q is fixed. There is no Aut(G)-equivariance or H-triple assertion. A's cardinality equality is accepted, but equality of cardinalities is not the requested permutation-set comparison.

For a fixed J,p,a, let t be the unit modulo exp(J) satisfying t≡1 modulo exp(J)_p and t≡p^a modulo exp(J)_{p′}. TD says that for every h≥1 there is s₀(J,p,a,h), independent of the multiset M, such that p^h divides the number of simultaneous J-conjugacy orbits of **ordered generating** tuples

\[
 (x,y,u_1,\ldots,u_{p^s}),\qquad
 u_1\cdots u_{p^s}y^t=xyx^{-1},
\]

with all u_i p-singular and prescribed J-class multiset M, for all s≥s₀, whenever O_p(J)=1. Prescribing M never quotients out position permutations.

## 2. ORIGINAL verdicts, before any new construction

| Original assertion | Verdict | Reason and precise boundary |
|---|---|---|
| Equivariant subsection identity (2) | **ORIGINAL PASS, no repairs** | The stable-image/semisimple-cocenter comparison intertwines the linear class-power operator, and the integral lift below recovers integer fixed counts. |
| Mixed-characteristic permutation-summand lift, including p-torsion action | **ORIGINAL PASS, no repairs** | Equivariant Hom matrices lift orbit by orbit; no division by the cyclic order is used. |
| Twisted trace identities (3)/(4) | **ORIGINAL PASS, no repairs** | Direct class-basis diagonal calculation gives exactly one denominator |H|, and trace coordinates give the fixed-character sum without a commutation hypothesis on w. |
| Conditional universal TD⇒G104, including (5) | **ORIGINAL PASS, no repairs** | All chain operations retain their idempotents and commute with coefficient twisting; inversion is used universally, including subquotients, not for just one block. |
| A5 formulas (6), all-s valuation bounds (7), and all-a assertion | **ORIGINAL PASS, no repairs** | Subgroup Möbius coefficients and the power actions give the displayed expressions; elementary doubling proves the bounds for every s≥1. |
| Connected symmetric forms (8), every m≥2 including p∣m | **ORIGINAL PASS, no repairs** | Separability, not nonvanishing of Tr(1)=m, gives the trace pairing. The skew algebra and the path algebra are geometric forms with distinct arithmetic simple sets. |
| Rank reconstruction (9), including p-divisible cycle lengths | **ORIGINAL PASS, no repairs** | Kernel dimensions count cycles of π^d over every characteristic; both Möbius inversions are integer identities. |
| Finite-field interpretation of the rank profile | **ORIGINAL PASS, no repairs** | The field tensor-product decomposition and extension of the radical give exactly Σ gcd(m_i,d) simple factors. |
| Scoped counterexamples: unrestricted t, power-map automorphism, geometric-invariant inference, modular traces | **ORIGINAL PASS at the stated scopes** | None is a counterexample to G104 or to admissible TD. |

### 2.1 Subsections and the integral action

Fix σ_a(z)=z^{p^a} and a σ_a-stable central idempotent E. One may use W(k) with the necessary p-power roots adjoined, and extend Witt Frobenius by fixing those roots. This realizes γ_t on character values. It does not assert that W(k) is splitting, nor impose a group-independent ramification bound.

On V(KH), the map L_t[g]=[g^t] is **K-linear**, and the coordinates χ([g])=χ(g) give
χ(L_t[g])=χ^{γ_t}(g). Thus L_t permutes the trace-coordinate lines. Multiplication by Ẽ commutes with it because the selected character set is γ_t-stable. Since both operators preserve the free class lattice, their equality over K is an equality on that lattice.

A, `group.tex` 271–315, identifies the p-regular class span of V(kC) with V(kC/rad(kC)) and respects central idempotents. On a class representative g of p′-order, the matrix eigenvalues show
Tr(ρ(g^t))=Tr(ρ(g))^{p^a}=Tr(ρ^{σ_a}(g)). This is checked on the class basis and then extended **linearly**, not semilinearly, to arbitrary coefficients. A, 340–361, identifies the u-section with that span for C=C_H(u), intertwining E and Br_〈u〉E. Since u^t=u, it also intertwines L_t. This proves an isomorphism of kC_d-modules, where C_d is the finite cyclic group generated by L_t, with the permutation module on the subsection simple labels.

For permutation O-lattices O[X], O[Y], an equivariant map is precisely a matrix constant on each diagonal C_d-orbit in Y×X. Every such residue matrix lifts, regardless of whether p divides d. For direct summands with commuting projections e,f, extend a map by the projections, lift on the ambient permutation lattices, and compose the lift with e,f. This proves surjectivity on Hom for those summands too. Apply it to the just obtained residue isomorphism. Both lattices have the same rank; a lift has unit determinant and is an equivariant O-isomorphism. Consequently its characteristic-zero trace is the **integer** number of fixed permutation labels. This establishes original (2), also for E=0 and sums of blocks. A congruence of k-traces alone would not establish it.

### 2.2 Twisted trace and the exact chain implication

For β_z the coefficient of z in w^n, the diagonal coefficient at the class [y] of M_{w^n}L_t is Σ_{z∼y}β_{zy^{-t}}. The conjugation map x↦xyx^{-1} has fiber size |C_H(y)|. Summing over y-classes, and then over all y, therefore gives |H|^{-1}Σ_{x,y}β_{xyx^{-1}y^{-t}}. Convolution expands this into (3). A diagonal matrix times a permutation matrix has trace equal to the sum of its diagonal entries at the fixed coordinates, proving (4). Centrality of w suffices; w need not be fixed by γ_t. γ_t acts on ordinary character values in a cyclotomic splitting field; it is not being applied to arbitrary coefficients of w.

Here is the source-operation audit of the original conditional proof, retaining every quantifier.

1. **Block assignment and quotient:** A, 81–158, proves π_Qs_H=π_QBr_Q on the specified normalizers. These maps have prime-field coefficient formulas. They commute with σ_a and select exactly the assigned quotient defect-zero blocks. The unique ordinary character and unique projective simple of each defect-zero block correspond equivariantly because both are selected by that same block idempotent.
2. **Detector and trace limit:** A, 608–698, supplies v=E(1−c_G), its p-singular support, and the 0/1 residues of all restricted central scalars. Choose one integral class-sum lift with this support. The lift need not itself be σ_a-fixed. In the fixed-character trace, each relevant scalar tends to its residue under p^s powering. The binomial lower bound used in I104 applies at every fixed finite ramification index. Nonnormal-chain cancellation is legal before taking this limit because its operator depends only on H_C.
3. **Actual chains and generated subgroups:** Replace a chain orbit by its |G|/|H_C| actual chains. Its trace denominator |H_C| becomes exactly |G|. For each tuple, the remaining signed coefficient is a_G(〈x,y,u_i〉). The source p-core toggle Q_i↔Q_iO_p(J), including terminal insertion, cancels all O_p(J)≠1. It uses no property of the tuple relation beyond its generated subgroup.
4. **Exact multiset and orbit multiplicity:** Group tuples in J by their J-class multiset. Class sums restricted from G are constant on every J-class. Their product α(M) is independent of the order of its factors. The stabilizer of a generating tuple is exactly Z(J), so the number of actual tuples is |J|/|Z(J)| times the orbit count. This yields original (5), over actual subgroups J≤G, with no extra normalizer quotient.
5. **Uniform limit:** Given h, take a maximum of the TD thresholds for the finitely many J≤G. Every term of every inner finite sum lies in p^hO, even though the number of multisets grows. The fixed denominator |G| only subtracts its fixed valuation. Thus Φ_{p^s,t}→0.
6. **Subsection toggle:** Expand each ordinary fixed count by (2). For u≠1 the source toggle inserts or deletes Q_i〈u〉 after the last group not containing u. Both H_C∩C_G(u) and Q_r〈u〉 remain unchanged. The idempotent is Br_{Q_r〈u〉}E before and after. Coefficient twisting fixes u and all subgroup/conjugation data, and respects this common idempotent, so the paired **fixed-label** counts agree. This checks more than just numeric cancellation.
7. **Universal inversion:** For fixed p,a define l_a,z_a on every σ_a-stable pair (X,E). A, 160–255, identifies T^rl_a with normal chains, including quotient idempotents by the explicit coset coefficient sums. Inflation of simples through a normal p-subgroup is a coefficient-equivariant bijection. T decreases the p-part of the group order and is evaluation-wise nilpotent. The relation z_a=(1+T)^{-1}l_a must hold on **all pairs and all subquotients**; universal TD supplies that. Only then conclude l_a=(1+T)z_a. The t chosen for an ambient group restricts to the required congruences on every subquotient exponent.
8. **All coefficient powers:** If F_p[b]=F_{p^f}, apply the argument to every a divisible by f. The two finite Γ_b-sets factor through finite cyclic groups. Equality of fixed counts of every positive power determines the number of cycles of each length by divisor Möbius inversion. It determines p-divisible lengths too, because these are integer fixed counts in characteristic zero. Pair equal-length cycles to get G104.

This proves the original conditional implication as written. It does not prove TD. It agrees with the **universal** formulation of Huang–Yılmaz Theorem 1.4 and its warning in Remark 1.5 about an individual block.

### 2.3 A5, forms, profiles, and counterexample scopes

For A5, the subgroup Möbius values for A4,D10,S3,V4,C5,C3,C2,1 are respectively −1,−1,−1,0,0,2,4,−60. The source-independent subgroup proof in I104 is sufficient: an intransitive subgroup fixes a point or preserves a 3+2 decomposition; a transitive proper subgroup has a normal Sylow 5-subgroup, since otherwise its order is 30 or 60 and order 30 is excluded by the 3-cycle generation argument. The listed incidence counts give the Möbius recursion. Dividing actual generating tuples by 60 gives signed trace coefficients 1,−1,−1,−1,+2 for A5,A4,D10,S3,C2. Odd-order subgroups have no puncture choices.

I independently recomputed the involution-sum eigenvalues and power actions from the permutation characters and orthogonality argument in the original. In particular inverse elements belong to the same A5 classes, justifying the real values used there. For even n the result is precisely

\[
N^7=15^n-4\,3^n-2\,5^n+3,\quad
N^{17}=15^n-2\,3^n-2\,5^n+3,\quad
N^1=15^n-4\,3^n+3.
\]

For n=2^s, s≥1, the first is 6 modulo 8. The base values at s=1 and z^{2^{s+1}}−1=(z^{2^s}−1)(z^{2^s}+1) give v₂(3^n−1)=v₂(5^n−1)=s+2 and v₂(15^n−1)=s+4. Substitution proves all the original lower bounds. There is only one 2-singular A5 class, so the all-multiset claim at p=2 is literal. The four admissible a-residues give t=17,19,23,1 modulo 30; their contributing character actions depend only on a's parity. Thus the all-a bound is also proved, not extrapolated. The original erroneous exploratory identification of t=7 is already disclosed and corrected in I104; its original final mathematical claim is scoped correctly. No power of 2 has residues (2 mod 5,1 mod 3).

For the symmetric forms, the original monomial pairing on A and the field-trace pairing on B=L[x;τ]/(x^{m+1}) are nondegenerate. If p∣m, Tr(1)=0 can occur, but the polynomial T+T^q+⋯+T^{q^{m−1}} is a nonzero polynomial of degree less than |L|, so the trace functional is not identically zero. Multiplication by a nonzero coefficient and τ^r are bijections; hence the original complementary-degree argument still separates every nonzero element. The radical quotients F^m and L, their geometric vertex decomposition, the arrow commutation test for central idempotents, and the Cartan/Loewy calculations are all valid for every m≥2. The different numbers of F-simple modules prohibit F-linear Morita equivalence. These are arbitrary symmetric algebra forms, not asserted group-block realizations.

On a cycle of length m, ker(π^d−1) has dimension gcd(m,d) over every field: a vector has one constant value on each orbit of π^d. Therefore K(d)=Σ_m c_m gcd(m,d); gcd(m,d)=Σ_{r∣m,r∣d}φ(r) gives the first inversion, and the inversion over multiples gives the second in (9). No eigenvalue diagonalization is used. For ∏M_{n_i}(F_{q^{m_i}}), extension to F_{q^d} gives gcd(m_i,d) simple factors in the i-th component. The extended radical is nilpotent and the quotient is semisimple, so it is the radical. This proves the stated finite-field interpretation, retaining all p-divisible cycle lengths.

The p fixed points versus one p-cycle example has identical traces of all powers over k, but K(1)=p versus 1. The S3 admissible map g↦g^5 fails multiplicativity on two transpositions. The A5 t=7 example refutes unrestricted-unit TD only. The form example refutes only inference from the listed geometric invariants. All four scoped counterexamples pass. No one of them refutes G104, admissible TD, or an accepted source statement.

## 3. Current stronger companions and reading boundary

Live primary metadata on 2026-10-10 still identifies Huang–Yılmaz as [arXiv:2512.07369v1](https://arxiv.org/abs/2512.07369), Feng–Fu–Zhou as [2512.15243v2](https://arxiv.org/abs/2512.15243), and Huang's category paper as [2604.06166v3](https://arxiv.org/abs/2604.06166). Raw HTML responses and headers are retained; existing I104 primary PDFs are referenced by hash rather than redownloaded. The 15-page [Huang–Yılmaz author PDF](https://yilmazdeniz.bilkent.edu.tr/papers/awc-galois-functorial.pdf) is kept distinct from the arXiv version and from the September 2026 journal bibliographic record.

I read the complete relevant operations through their endings, not just introductions: all A group, twist, differential, valuation, specialization, and consequence sections; the exact ID comparison, rigidity, Sylow extension and assembly; D's component-return comparison; the entire Huang–Yılmaz author text; the current FFZ induction and final construction; and Huang v3's category, Brauer, central-extension and equivariant assembly operations. Imported external results in those papers remain attributed to their authors. This is selective complete-proof reading of the operations used, not a claim to have independently audited every external theorem or semantically read the entire repository.

An additional stronger companion was checked directly: [Boltje–Bouc–Yılmaz, arXiv:2507.20314v1](https://arxiv.org/abs/2507.20314), downloaded once and read through the proof ending. Its Theorem 3.5 cancels the nontrivial-p-group simple-functor components by an explicit local-point chain involution. The residual component is n_{G,b}[S_{1,1,F}], whose coefficient is the numerical chain count. Its stable quotient kills that component. This is exactly why its stronger-looking functorial conclusion, and A's use of it, do not compute the coefficient-Galois fixed projective-label subfunctors of Huang–Yılmaz §3.

Huang–Yılmaz Theorem 1.7 starts with inverse functorial morphisms **over the common minimal field**. Its proof extends those morphisms to a finite splitting field and obtains an isomorphism of characteristic-zero cyclic permutation modules on simples. That hypothesis supplies the integer fixed counts; it is not obtained by applying their Theorem 1.9 to a geometric block and its own Galois conjugate. FFZ v2 requires compatible H-triple isomorphisms for universal p′-covers of the involved nonabelian simple groups; its final induction uses them at the minimal-normal-subgroup step and preserves them through Clifford/DGN constructions. Numeric AWC is not that input. Huang v3 Theorem 1.20 assembles an (H×Aut(G_e))-equivariant **family already supplied on maximal subgroups**. Theorem 5.10 uses explicit central extensions for twisted EI-category algebras. These constructions do not manufacture that family from cardinalities.

The named significance reference remains Huang–Yılmaz's blockwise Galois Alperin weight conjecture, Conjecture 1.2. These primary reformulations and reductions establish observed research interest, not a ranking or priority claim. No new group-family case is nominated; in particular the A5 G104 case is already within Du–Huang's symmetric/alternating-group result.

## 4. Route 1 — an actual auxiliary-puncture correspondence and its arithmetic cost

### 4.1 Exact topological correspondence

Set A=y, B=x, U=u_1⋯u_n and v=A^{t−1}. Then the original relation is equivalent to

\[
[A,B]\,U\,v=1,\qquad v=A^{t-1}. \tag{10}
\]

Indeed Uy^{t−1}=[x,y], and [A,B]=[y,x]=[x,y]^{-1}. Thus adjoining this **constrained** final puncture is a bijection of tuple sets. Its inverse forgets v and swaps the handles back. It preserves the ordered u_i, their exact multiset, generation, and simultaneous inner conjugacy. Because v is a word in A, adjoining it adds no generator and changes no stabilizer; generating orbit size remains |J|/|Z(J)|. By Riemann existence this gives a subset of marked covers of a complex genus-one curve with n+1 punctures after a chosen marking. It does not quotient out puncture permutations or replace J by a semidirect product.

For admissible t, v is p-regular: if A=A_pA_{p′} is its commuting primary decomposition, A_p^{t−1}=1. Thus v can be nontrivial but cannot be the required extra p-singular puncture. This is a precise change of geometric contract, not a renamed automorphism.

The constraint is also marking-sensitive. On the punctured torus, the Nielsen/Dehn-twist change A↦AB, B↦B fixes [A,B] and can fix all peripheral generators. It need not preserve v=A^{t−1}. For J=S3,p=2,t=5, take A of order 3, B a transposition, u₁=u₂=B, v=A. Then [A,B]v=1 and the tuple generates J. But AB is a transposition, so (AB)^4=1≠v. This is an explicit failure of invariance under that handle-marking change. It does **not** assert that this particular mapping class belongs to the Galois image of A's auxiliary field. Rather, it proves that Galois invariance of the constrained locus must be separately established; the local tangent-character argument that only preserves puncture conjugacy classes cannot establish it.

### 4.2 The large-index obstruction is already present before ramification estimates

The actual source curve E/F₀ has index n=p^s. After F/F₀ with [F:F₀]_p≤p^h, every divisor degree on E_F is divisible by p^{s−h} (A, `twist.tex`, index-base-change). This includes full inseparable residue degrees.

The same divisibility obstructs a small auxiliary branch divisor on the characteristic-zero curve X_L used in descent. To check this from the complete operations, take a closed point z of X_L, with residue field M/L. Properness of the smooth model extends its M-point to the valuation ring of M. By the spherical-base degree equality, [res(M):F]=[M:L]. Its reduction gives an res(M)-point of E_F. Push that point down to E_F, including the residue-field multiplicity; the resulting effective zero-cycle has degree [M:L]=deg_L(z). Consequently p^{s−h} divides deg_L(z), and hence divides the degree of every effective divisor on X_L. The argument sums over points and uses only the source properness, residue-degree equality, and index operation.

**Paid obstruction.** Over a field of the small p-part degree required by the source descent, there is no nonzero auxiliary effective divisor of degree r with 0<r<p^{s−h}. In particular a single distinct auxiliary puncture cannot be defined there once s>h. Defining one after a further extension forces at least the corresponding p-part degree cost; over K_s itself an individual point requires p-part at least p^s. Choosing the full Galois orbit instead introduces a growing number of extra punctures and does not preserve (10) or its orbit count.

This also explains a limited positive statement: a J-cover over such an L with the original branch divisor and at most a fixed r additional **distinct geometric branch points**, whose additional branch locus is defined over L, has no additional branch locus when p^{s−h}>r. The reduced branch divisor is finite étale in characteristic zero and has that degree. The original no-small-cover operation then applies. This bounded-exception observation is a technical consequence of the actual source index. It does not put the constrained complex-cover subset into a Galois-stable finite set, nor construct the needed point without paying its field degree.

### 4.3 Why merely bounding exceptional ramification does not complete the source degeneration

The source proof is more precise than a genus inequality. It needs **equality** of Euler characteristics to identify all high-degree reduced section spaces and obtain a model with disjoint residue curves. Its final connectedness argument then forces one valuation and a nontrivial normal p-subgroup.

If a hypothetical auxiliary configuration supplied r extra branch points, and one used only the original n independent labels in the inseparable-genus estimate, the generic normalized Hurwitz sum acquires

\[
R_{\rm extra}=\sum_{j=1}^{r}(1-1/e'_j)\le r.
\]

Keeping the original-label vanishing comparison yields only

\[
\sum_{i=1}^{n}\left(|q_i-b_i|+\delta_iq_i\right)\le R_{\rm extra},
\quad q_i=(r_i a_i)^{-1},\ b_i=e_i^{-1},\ \delta_i=\mathbf1_{p\mid a_i}.
\tag{11}
\]

This follows by subtracting the modified generic Hurwitz formula from exactly the source's two lower bounds; no new specialization theorem is assumed. All denominators r_i a_i and e_i divide |J|, so a nonzero label summand is at least 1/|J|. Thus at most r|J| original labels can be bad. This is a genuine bounded-loss conclusion, but (11) does not force the Euler-characteristic equality required at `specialization.tex` 487–605. Adding tame terms without proving their residue comparison does not repair this. If the additional divisor is defined over the small field with bounded degree, §4.2 already eliminates it; if it is not, the Galois action and descent have not been supplied.

The source marked-cover operation fixes all |J|-th roots of unity. Its class preservation is algebraic local tangent data. It neither supplies a Frobenius power on a handle nor establishes the constraint v=A^{t−1}. Applying a coefficient automorphism to J-class data is also not an Aut(J) action. In particular the S3 power map cannot define an acting automorphism in J⋊C_d.

**Route-1 stopping point:** (10) is an exact marked topological correspondence; the valuation and specialization operations have been tested on it rather than assumed to apply. Missing are a Galois-stable arithmetic incarnation of its constraint with bounded p-part descent cost, and the exact residue comparison needed if additional ramification remains. No such incarnation is constructed here.

## 5. Route 2 — a finite central-algebra criterion for uniform TD

This route does not use covers, arbitrary algebra forms, or rank profiles. It attempts the actual valuation problem through subgroup Möbius inversion, mixed central moments, and Teichmüller limits. Its finite equalities remain unproved universally, but the equivalence and uniform threshold below are completely proved.

### 5.1 Mixed central moment formula

Fix any finite J, prime p, and any unit t modulo exp(J); the next result does not require O_p(J)=1 or Frobenius admissibility. Let C₁,…,C_r be **all** p-singular J-classes. If r=0 every tuple set is empty and TD is vacuous. Assume r≥1. For H≤J put

\[
 W_{H,i}=\sum_{g\in H\cap C_i}g\in Z(\mathbf ZH),\qquad
 \lambda_{H,\chi,i}=\lambda_\chi(W_{H,i}).
\]

Let μ(H,J) be the Möbius function of the lattice of actual subgroups, and D_J=|J|/|Z(J)|. For nonnegative m_i with n=Σm_i>0, put M(m)=n!/∏m_i!. Let N_t(m) be the generating orbit count with these multiplicities. Then

\[
 N_t(m)=M(m)F_t(m),\qquad
 F_t(m)=\frac1{D_J}\sum_{H\le J}\mu(H,J)|H|
 \sum_{\substack{\chi\in\operatorname{Irr}(H)\\\chi^{\gamma_t}=\chi}}
 \prod_{i:m_i>0}\lambda_{H,\chi,i}^{m_i}. \tag{12}
\]

**Proof.** Each W_{H,i} is central because H∩C_i is H-conjugation invariant. For a fixed assignment of class labels to the n ordered positions, the product of class sums counts the puncture products. These products commute, so every one of the M(m) different label assignments gives the same count. The class-basis proof of original (3)/(4) applies to the central product ∏W_{H,i}^{m_i}, not just to a single nth power. Thus the all-tuples count inside H is M(m)|H| times its fixed-character mixed moment. Every tuple generates a unique subgroup; subgroup-lattice Möbius inversion extracts those generating J. Divide by D_J, since their simultaneous stabilizer is Z(J). This proves (12), including empty class intersections and zero multiplicities. In particular F_t(m) is an integral sum divided by D_J in every local coefficient ring. ∎

Choose one embedding of the finite field of all λ-values into Q̄_p, and a finite extension K/Q_p containing them. Enlarge K unramified if necessary so all residues lie in its residue field F_Q, Q=p^f. Let O be its valuation ring, π a uniformizer, and e=v_π(p). All λ-values are integral because they are scalars of integral central elements. Write ω_{H,χ,i}=[overline{λ_{H,χ,i}}] for their Teichmüller lifts, with [0]=0. These lifts are already in O. We do not identify them with the original λ-values.

For a nonempty I⊆{1,…,r} and residues ρ_i∈Z/(Q−1), define

\[
 \Theta_t(I,\rho)=\frac1{D_J}\sum_{H\le J}\mu(H,J)|H|
 \sum_{\chi^{\gamma_t}=\chi}\ \prod_{i\in I}\omega_{H,\chi,i}^{\langle\rho_i\rangle}. \tag{13}
\]

Here each exponent ⟨ρ_i⟩ is a **positive** representative, e.g. in {1,…,Q−1}. Thus a zero ω contributes zero even for ρ_i=0; inactive coordinates are omitted. Nonzero ω has order dividing Q−1, so the value is independent of the positive representative. For Q=2 the residue ring Z/(Q−1) has one element and the representative is 1.

Call (I,ρ) accessible if Σ_{i∈I}ρ_i≡p^b modulo Q−1 for some b≥0. There are finitely many such pairs, and the condition requires checking only b modulo f.

### 5.2 Finite-moment theorem and uniform bound

**Theorem T108.** For the fixed J,p,t above, the following are equivalent:

* For every h≥1, there is s₀ independent of m such that p^h∣N_t(m) whenever Σm_i=p^s and s≥s₀.
* Every accessible moment Θ_t(I,ρ) in (13) is exactly zero in characteristic zero.

If the finite zero condition holds and d=v_p(D_J), one may take

\[
 s_0=\max\{0,\ e(h+d)-1\}. \tag{14}
\]

This is an all-multiset statement, not a test limited to pure class powers. It applies to admissible TD when O_p(J)=1 and t is admissible, but the theorem by itself does not assert its finite zero condition for those inputs.

**Proof of sufficiency.** For α∈O and its Teichmüller lift ω, if α is a unit then α/ω=1+z with v_π(z)≥1. The binomial estimate gives

\[
v_\pi((1+z)^p-1)\ge\min\{e+v_\pi(z),pv_\pi(z)\}\ge v_\pi(z)+1.
\]

Thus v_π(α^{p^k}−ω^{p^k})≥k+1. If α is not a unit, ω=0 and v_π(α^{p^k})≥p^k≥k+1. Factoring A^u−B^u then shows for every positive m divisible by p^k,

\[
v_\pi(\alpha^m-\omega^m)\ge k+1. \tag{15}
\]

For I={i:m_i>0}, let k=min_{i∈I}v_p(m_i). Telescoping products in (12) and using (15), then subtracting the denominator valuation, gives

\[
v_p\bigl(F_t(m)-\Theta_t(I,m\bmod(Q-1))\bigr)
 \ge (k+1)/e-d. \tag{16}
\]

The tuple of residues is accessible because Σm_i=p^s. Hence Θ=0 by hypothesis. Put c=v_p(M(m)). Independently of (16), integrality of the numerator of (12) gives v_p(F_t(m))≥−d. Also for every i∈I,

\[
m_i M(m)=p^s\frac{(p^s-1)!}{(m_i-1)!\prod_{j\ne i}m_j!},
\]

whose fraction is an integer. Therefore c+v_p(m_i)≥s, and k≥s−c. If c≥h+d the elementary bound already gives v_p(N_t(m))≥h. Otherwise (16) gives

\[
v_p(N_t(m))\ge c+(k+1)/e-d
\ge(s+1)/e-d+c(1-1/e)\ge(s+1)/e-d.
\]

Condition (14) makes this at least h. Since N_t(m) is an integer, this proves p^h divisibility uniformly. No bound depends on the number or distribution of multisets. ∎

**Proof of necessity.** Fix an accessible (I,ρ). Choose b in the appropriate residue class modulo f, sufficiently large that p^b is at least the sum of the positive representatives ⟨ρ_i⟩. Their sum has the same residue as p^b modulo Q−1. Add the nonnegative difference, a multiple of Q−1, to one coordinate. This gives positive integers m_i on I, zero elsewhere, with Σm_i=p^b and the prescribed residues. For Q=2 the same construction uses modulus one.

Consider m^{(k)}=p^k m with k tending to infinity through multiples of f. Its total is p^{b+k}. Legendre's factorial valuation formula, or cancellation of base-p digit sums, gives

\[
v_p\bigl(M(p^k m)\bigr)=v_p(M(m)) \tag{17}
\]

for every k. By (15), F_t(p^k m) tends to Θ_t(I,ρ), since ω^{p^k}=ω for k divisible by f. The asserted uniform divisibility, applied just to this sequence, says that v_p(N_t(p^k m)) tends to infinity. Equation (12) and the constant valuation (17) imply F_t(p^k m)→0. Therefore Θ_t(I,ρ)=0. This proves necessity for every accessible pair. ∎

### 5.3 Exactness, a stopping bound, and what the criterion buys

These are finite **exact algebraic equalities**, not high-precision numerical conjectures. They have a finite stopping certificate if computed p-adically with certified arithmetic. Put

\[
B=\max\left(1,\sum_{H\le J}|\mu(H,J)|\,|H|\,k(H)\right),\quad M=Q-1.
\]

The numerator A=D_JΘ is an algebraic integer in Q(ζ_M), of degree at most φ(M), and every complex conjugate has absolute value at most B, since each nonzero summand is a root of unity. Here φ(1)=1. If A≠0, its field norm is a nonzero rational integer of absolute value at most B^{φ(M)}. At every p-adic embedding A is integral. Thus v_p(A)≥R at one embedding, for an integer R with p^R>B^{φ(M)}, is impossible unless A=0: the norm would be divisible by p^R but too small. This proves an exact cutoff. It does not claim that the computations here evaluated every moment for arbitrary groups.

The source theorem for t=1, whose commutator convention is matched by swapping the handles, implies all its finite moments vanish by necessity. Conversely these moments imply its uniform count by sufficiency. Thus this gives a concrete central-algebra reduction of the **complete** untwisted count scope. The same equivalence exposes exactly what the admissible extension still needs. Since t depends on a modulo ord_{exp(J)_{p′}}(p), all a for one fixed J,p require only finitely many t. There remains no uniform proof of (13) over all finite J with O_p(J)=1.

For the A5 involution calculation, all nonzero eigenvalue residues are 1 at p=2, so its active Teichmüller moment is respectively

\[
1-4-2+3=-2\quad(t=7),\qquad
1-2-2+3=0\quad(t=17),\qquad
1-4+3=0\quad(t=1).
\]

This recovers the persistent unrestricted-power obstruction and the paid admissible case in one exact finite calculation. It does not use the t=7 example as evidence against admissible TD.

### 5.4 Why the accepted untwisted moments do not yet give the twisted ones

The new attempted transfer was to recover the fixed-character terms of (13) from the accepted t=1 equalities using their central eigenvalue residues. Its exact limitation is visible inside the A5 subgroup calculation. On A4 at p=2, the involution-sum eigenvalues are 3,3,3,−1, all with residue 1 and Teichmüller value 1. The t=1 limiting trace counts four ordinary labels; the admissible restriction t≡5 modulo 6 fixes only two. Central powers of this detector do not separate those labels. Averaging an action yields an invariant-space dimension/orbit count, whereas the required trace is the number of fixed labels; with p-torsion, reducing traces is even less informative.

A formal characteristic-zero projector onto γ_t-fixed ordinary coordinates does exist. Treating it as an **integral central idempotent** is unjustified: central integral idempotents select whole blocks, not arbitrary γ_t-fixed subsets of ordinary characters. The source detector precisely uses whole-block 0/1 residues. No additional integral projector or identity that selects the required labels has been constructed here. The remaining statement can therefore be given finitely and exactly as the accessible moment vanishing (13), or more weakly as cancellation of the detector-weighted numerator in original (5); neither is proved for arbitrary groups.

The other attempted endpoint comparison also stops concretely. ID constructs
σ^m(U)⊗T_λ⊗U^∨, a (σ^mB₀,B₀)-Morita bimodule. It retains the actual inner factors, shows their discrepancies lie in Teichmüller p′-roots, descends central kernels, then kills a scalar H²(S,T) class for a **pure p-subgroup S with trivial scalar action**. Tensoring extends this to Frobenius returns of actual crossed extension blocks. None of these displayed endpoints is the weight algebra for b. A Frobenius return and a bound on its period do not supply a comparison to that different endpoint or a descent cocycle for a cyclic coefficient action. Huang–Yılmaz's minimal-field inverse morphisms would supply what is missing, but they have not been constructed from these return bimodules. The original connected symmetric forms and rank-profile calculations correctly diagnose that loss of arithmetic data; they do not replace the construction.

## 6. Admissible counterexample search and independent finite checks

`tuple_search.py` enumerates actual subgroup lattices, computes their Möbius functions, and performs exact group-algebra convolution of each **J-class intersection** inside each H. It retains every multiset row and every admissible a modulo the p′ exponent period. Counts are computed modulo D_Jp^8 before exact orbit division, rather than dividing residue-field traces. The following finite domains were checked:

| Group | p | s range | p-singular J-classes |
|---|---:|---:|---:|
| S3 | 2 | 0–10 | 1 |
| A5 | 2 | 0–10 | 1 |
| A5 | 3 | 0–5 | 1 |
| A5 | 5 | 0–4 | 2 |
| S4 | 3 | 0–5 | 1 |
| D14 | 2 | 0–9 | 1 |
| C7⋊C3 | 3 | 0–5 | 2 |
| C13⋊C3 | 3 | 0–4 | 2 |
| S3×C3 | 2 | 0–5 | 3 |

The affine actions in the two Frobenius groups are explicitly constructed from elements of order 3 in the corresponding prime fields. The script checks trivial p-core from the actual normal subgroups. The A5,p=5 run includes **all 626 multisets** at n=625, not just the sum over all singular classes; the product-group run includes all 561 multisets at n=32. All admissible a-residue classes are retained. Minimum valuations increase on these ranges, capped at 8; no admissible counterexample is found. Zero modulo p^8 means valuation **at least** 8, not an exact zero count or infinite valuation.

`checks.py` separately enumerates actual tuples and tests generation directly in three small cases, including A5,p=2,t=17,n=2 and mixed class data in S3×C3. It checks the constrained-puncture marking failure, elementary multinomial valuation/dilation identities on a finite domain, and the A5 analytic expressions through s=15. These are finite reproducibility checks. The universal proofs are the original audited arguments and the proofs in §§4–5, not the finite runs.

## 7. Complete reduction and technical disposition

Each positive result is classified by its actual proved scope, not by absence of a printed duplicate.

* Original (2) reduces in full to A's stable-image and subsection maps, followed by orbit-constant equivariant Hom lifting and Nakayama/determinant lifting. The argument handles all cyclic action orders; it is a technical refinement.
* Original (3)/(4), (5), and TD⇒G104 reduce to the class-basis trace expansion, A's detector and exact chain operations, and finite cyclic inversion. They remain conditional at TD; no missing step is counted as a finding.
* The original A5 formulas reduce to its finite subgroup lattice, explicit permutation characters, orthogonality, and repeated squaring. The forms reduce to skew-polynomial/path-algebra multiplication, separable trace, and finite-field descent. The rank profile is two explicit integer Möbius inversions. These are technical at their full stated scopes.
* The auxiliary correspondence (10) is a word identity plus the **actual** Riemann-existence classification; its index obstruction is the source full-residue-degree operation followed by specialization of points and divisor pushforward. The bounded-loss inequality (11) is the source's generic Hurwitz, differential estimate, and selected-vanishing comparison with the extra term retained. All are technical source-operation reductions; they do not solve the arithmetic constraint.
* The entire new theorem T108 reduces to the mixed version of the same trace expansion, ordinary subgroup Möbius inversion, finite-field Teichmüller lifting, the explicit binomial estimate (15), and the multinomial identity used to prove k≥s−c. Necessity is a positive-residue realization plus Legendre's formula. The exact cutoff is the elementary cyclotomic norm bound. This is a complete reduction for its **equivalence and conditional quantitative bound**, not a proof of the finite zero condition. It is useful technical progress toward the actual missing estimate, not a substantial nomination.

Classical tools alone are not grounds for rejecting a contribution. Here the decisive facts are the complete reductions just given and the absence of a proof of the arbitrary admissible moment cancellation or a minimal-field global/weight construction. Neither numerical AWC, geometric functorial equivalence, stable cancellation, Frobenius-return finiteness, nor categorical reformulation has been promoted to an unavailable arithmetic comparison.

## 8. Evidence, failures, and offline replay

The complete frozen tree has 13,223 entries, 749 manuscript families, and 10,373 original blob positions. The I88 augmented mapping reuses 9,340 I14 originals, 257 outside byte representations, and 776 PDF text representations. No recursive copying or whole-corpus download was performed. Two new case-insensitive regex searches preserve their exact occurrence multisets, with paths, one-based splitlines, half-open character spans, matched strings and full lines: 245 companion occurrences in 23 families, and 353 bridge occurrences in 60 families. This is a **full-domain lexical search**, not semantic reading, a novelty certificate, or a proof that a differently worded reduction cannot exist.

Only README.md, frontier/README.md, frontier/TEN-FINDINGS.md, and frontier/iterations/README.md may drift; their frozen snapshots are checked instead of their live bytes. The original report, original task evidence, original source references, inherited primary response bytes, new HTTP metadata, and selected new primary PDF bytes are immutable. No I106/I107 active output is bound. The old I104 failed diagnostic and verifier-attempt records are retained as immutable references, not deleted or relabeled as successes.

Retained I108 work failures: an initial catalogue/ancestor inventory read produced truncated output, as did some combined literature/report dumps; bounded rereads covered the relied-on passages. The ancestor command listed filenames outside the project but did not open those files or make them dependencies. A T3 message read requested an unsupported 100,000-character page; the error was preserved and corrected to two pages of at most 50,000 characters. One source read misspelled `twist.tex` as `twists.tex` and failed; the actual file was then read through its ending. A later schema probe tried a nonexistent I88 mapping path and then used the actual path already recorded by I104. These are reading/retrieval failures, not mathematical counterexamples or passing verifier runs.

The first preseal replay failed at `Original brief mismatch`: the checker stripped the already-retained separator newline before adding its terminal LF. The original frozen brief and response bytes were unchanged; the checker was corrected to reproduce the documented extraction convention. `validation-attempt-1.json` preserves that failure. Later validation records retain their own outcomes.

Replay from the repository root:

```text
python3 -B frontier/experiments/i108_galois_tuple_divisibility/verify.py
```

The final verifier is offline and read-only: no downloads, writes, bytecode, repair, or resealing. It checks the exact owned inventory and hashes, original-reference hashes, complete tree and original Git blobs, exact lexical occurrence multisets, line conventions and passages, selective PDF text extraction, original-parent evidence consistency, the admissible tuple computations, and independent small checks. Preparation and the single seal writer are separate and are not executed by it. Validation precedes the one final seal; final replay writes only to stdout. A pass certifies evidence integrity and these finite replays, **not universal truth, contribution acceptance, or priority**.
