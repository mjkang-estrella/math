# I31: a primitive canonical-weight construction of a nonconical no-MCM germ

**Author candidate, not an independent proof PASS or an accepted finding.** This report constructs a proposed complete local normal complex domain with no nonzero finite maximal Cohen–Macaulay module and proves a stronger nonconicality assertion: it cannot be the vertex completion of any finitely generated positively graded complex algebra with degree-zero part C. The construction is by compatible formal gluing, followed by an explicit finite filtered algebra and algebraization of its exceptional neighborhood. No analytic convergence or finite-type-over-C algebraization is asserted. Those are unnecessary for the complete-local target.

The additional bridge is the integration of a primitive class at the canonical weight, preservation of **every** section-ring degree despite depth two at the vertex, and an obstruction to lifting the normal Euler field on the intrinsic normalized blowup. The primitive-cohomology/first-order-deformation relation itself is classical. The I28 persistence argument, source divisor lemmas, the numerical specialization, and variants within this construction are not separate findings. Acceptance and any count change require the parent's separate proof and significance reviews; the accepted count remains five.

## 1. Scope and exact candidate

All pinned OpenAI proofs are accepted at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Their truth is not audited. Source C is [the complete-local no-MCM manuscript](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/A-Complete-Local-Domain-Without-a-Small-Cohen-Macaulay-Module-September-23-2026), including all of `build/paper.tex` and `build/surface.tex`, read in full. The original task, interruption checkpoint, frozen initial inputs, resumed inputs, and exact read contracts accompany the report. Initial checkpoint bytes and all I28 bytes are preserved separately from new artifacts and live shared-ledger drift. No agents, index changes, staging, commits, or pushes are part of this task.

**Proposed general realization theorem.** Let X be a smooth connected projective complex surface, L an ample globally generated line bundle, and fix an isomorphism K_X ≅ L^a with an integer a≥1. Suppose there is a divisor C on X such that

    C·L=0,                 C²≠0.

There exists a complete Noetherian local C-domain (R,m), with residue field C, together with descending ideals F_d, such that F_0=R, F_1=m, the filtration is multiplicative, separated, complete and cofinal with the m-adic filtration, and

    gr_F R ≅ ⊕_{d≥0} H⁰(X,L^d)

as the full graded algebra. The ring has dimension three, is normal, and is regular off m. It is not isomorphic as a complete local C-algebra to the vertex completion of any finitely generated positively graded C-algebra B with B_0=C. If K_X²−2c₂(X)>6L², it has no nonzero finite MCM module.

More precisely, fix the Čech construction in §5 with first class ξ mapping to c₁(C) under T_X⊗K_X≅Ω¹_X. It constructs R_λ for every scalar λ∈C. R_0 is the completed section ring. **Every λ≠0**, including the specified λ=1, satisfies the assertions above. No pairwise nonisomorphism of the nonzero fibers, moduli dimension, or extra finding count is claimed.

**Application to the actual obstructed surface.** For C's prime-seven complete-quadrangle cover π:X→B, use precisely its polarization H=3J−E and L=O_X(H), without a Veronese. Take C=π*(e₁−e₂). The proof below gives

    K_X≅L⁵, H²=1715, c₂=14749, K²=42875,
    Δ=13377>10290=6H², C·H=0, C²=−33614.

This is the candidate requested in I31, rather than I28's unobstructed-numerics hypersurface test. Sections 2–7 supply the proof; the later provenance and comparison sections specify its review limits.

## 2. Independent audit of I28 Steps A1–A5

I28 is read as a conditional technical proposition with the **exact full-section-ring** hypothesis. I find no actual mathematical gap in A1–A5 under its stated hypotheses. The expanded checks below are supplied independently; neither the parent's integrity check of I28 nor this author's check is a separate full-theorem acceptance audit.

### A1: strict finite normalization

Choose three degree-one sections s_i of L with no common zero. The associated finite f:X→P² satisfies f*O(1)=L. The full ring T is finite over S=C[s₀,s₁,s₂], even without generation in degree one: use f_*O_X and Serre vanishing. Choose homogeneous S-module generators b̄_j of degrees d_j and lifts x_i∈F₁, b_j∈F_{d_j}. Include 1 among the generators. Continuity defines A=C[[x₀,x₁,x₂]]→R. Its injectivity follows from the lowest nonzero homogeneous term and algebraic independence of the s_i. Successive initial-term subtraction, separately collecting the coefficient of each b_j, gives

    F_q = Σ_j n^{max(q−d_j,0)} b_j,        n=(x₀,x₁,x₂)⊂A.       (2.1)

The coefficient increments have strictly increasing n-order; the residual has strictly increasing F-order. Completeness and separatedness justify the equality, not merely density of its right side. Each F_q is closed because it is an ideal in an m-adically complete Noetherian ring. In the construction below completeness is instead built into the F-topology, and the same argument establishes Noetherianness afterwards, avoiding a circular assumption. Since gr_F R is a domain, orders of nonzero products add, so R is a domain. Finiteness over the injective A gives dimension three. With D=max d_j, (2.1) gives n^qR⊂F_q and F_{q+D}⊂n^qR. Thus nR is m-primary and the topologies agree.

### A2: the Rees algebra really is finite

Set B_A=⊕_{q≥0}n^q u^q and C_F=⊕_{q≥0}F_q u^q. The finite list

    b_j u^k,                 0≤k≤d_j,

generates C_F over B_A. In degree q choose k=min(q,d_j) and use (2.1). In particular it would be wrong to retain only b_j u^{d_j}, which misses lower shifts. Finite graded generation implies √(B_{A,+}C_F)=√(C_{F,+}); for a homogeneous positive-degree c, high powers lie in degrees greater than all module generators and therefore in B_{A,+}C_F. Hence the x_i u charts cover W=Proj C_F, and W→V=Proj B_A is finite. C_F is a finitely generated graded R-algebra, so p:W→Spec R is projective. Off m, every F_q becomes the unit ideal because it contains an m-primary n^qR. Thus p is an isomorphism on that puncture.

### A3: the actual exceptional divisor, without changing H

The degree-q kernel of C_F→gr_F R is F_{q+1}u^q. On D_+(x_i u), each such element divided by (x_i u)^q is divisible by x_i, because its quotient by x_i is represented at degree q+1. The converse uses x_iF_q⊂F_{q+1}. The quotient is (T[s_i^{-1}])_0, exactly the affine open X_i⊂X. The charts are domains, so x_i is a nonzerodivisor. They give an effective Cartier divisor X with

    J=O_W(−X)=mO_W=nO_W=g*I,     J|_X=L,     I|_{P²}=O(1).       (2.2)

For mO_W⊂(x_i), apply the same division to every r∈F₁ in degree zero; the reverse inclusion holds because x_i∈m. The transition x_j/x_i reduces to s_j/s_i, giving L, not an unspecified ample power of it. The finite map on X is the original f. The use of degree-one *sections covering X* is distinct from generation of T in degree one.

### A4: regularity and normality

At a point of X a regular Cartier equation has regular quotient O_X, so the dimension/embedding-dimension criterion makes O_W regular. Every point of the projective W specializes to a point of its closed fiber: its closure has nonempty closed image in the local Spec R. Regularity is preserved by localization, so W is regular everywhere. The integral charts establish integrality directly. Therefore R is regular away from m.

For S₂ at m, T is normal: it is the full section ring of an invertible sheaf on a smooth integral variety, equivalently the global functions on its normal line-bundle total space. Choose s₀,s₁∈T₁ to be a T-regular sequence. To justify the choice, T is S₂, so T/(s₀) is S₁; its associated primes have height one and none contains all T₁, since √(T₁T)=T_+ has height three. Avoid these finitely many primes over C, then choose s₂ to complete the finite projection. Regular initial forms lift to a regular sequence x₀,x₁ in R. Explicitly, order additivity for x₀ identifies gr(R/x₀R) with T/(s₀); successive division converges, since R is complete. Apply the same argument to s₁. Thus depth R≥2. Regularity off m supplies all other S₂ points and R₁. Serre's criterion proves normality. This argument does not assume Γ(W,O_W)=R before normality is known.

### A5: all finite MCM modules, restriction, and pushforward

For a nonzero finite MCM R-module M, the x_i are a system of parameters and hence an M-regular sequence. M is finite and depth three over A, so Auslander–Buchsbaum gives M≅A^N, N>0. The algebra R⊗_AFrac(A) is a field. Multiplication by any nonzero r∈R has zero kernel on M after that localization; such a kernel would be A-torsion inside A^N, so it is zero. Thus M is torsion-free of positive R-rank and full support. The depth-localization inequality gives depth M_q≥3−dim(R/q)≥dim R_q. On the regular puncture, Auslander–Buchsbaum gives local freeness.

On W let E=(p*M̃)**. A coherent dual over a regular local domain has depth at least min(2,dim): dualize a presentation and apply the depth lemma to its torsion-free image. Hence at every nongeneric point of X, E/x_iE has depth at least one; at the generic point E is free over a DVR. Therefore P=E|_X is torsion-free of positive rank, without requiring E locally free everywhere on the threefold. Source C's `lem:balance` applies to this precise pair and preserves these properties.

The finite map g is dominant between integral schemes, so g_*E is torsion-free; on V−P² it is the bundle A^N, hence trivial. Multiplication by the local Cartier equation is injective on E. Apply exact finite pushforward to

    0→E⊗J→E→i_*P→0.

Equation (2.2) and the projection formula identify its first map with multiplication by I on g_*E. Thus

    (g_*E)|_{P²}=f_*P                                              (2.3)

as ordinary coherent sheaves. No flatness of E, of g, or of f is required for this quotient identity. C's `lem:lattice`, `lem:factor`, and `eq:mixture` now give, with h=L²,

    0≤v(f_*P)≤1/2−(K²−2c₂)/(12h).

For Δ>6h this is impossible. This is the full conditional persistence conclusion for arbitrary ranks and arbitrary finite nongraded modules. It remains a technical transfer; realization is the next issue.

## 3. Exact geometry and an explicit primitive class

Use C's notation J_a=R_a+F_i+F_j∼J and E=ΣF_i. Each exceptional F_i occurs in three J_a, so

    Σ_aR_a+Σ_iF_i ∼ 6J−2E=2H.

Also π*K_B∼−3nJ+nE=−nH. The local ramification-coordinate proof in C gives the integral canonical-divisor formula

    K_X∼π*K_B+(n−1)(ΣR_a+ΣF_i)∼(n−2)H.                          (3.1)

This upgrades the numerical proportionality to an actual line-bundle isomorphism using the source's constructed root divisors. It is not a deduction from numerical equivalence alone.

For C=π*(e₁−e₂), projection of intersections gives

    H·C=n⁴(−K_B)·(e₁−e₂)=0,     C²=n⁵(e₁−e₂)²=−2n⁵.            (3.2)

The class α=c₁(O_X(C))∈H¹(X,Ω¹_X) is nonzero: its cup square has trace C²≠0 (with the standard algebraic Chern-class normalization). It is primitive with respect to H. This explicit class avoids any assumption about the entire eigensheaf decomposition of π_*T_X or a finite vanishing table.

At n=7, Noether's formula gives χ(O_X)=4802. Riemann–Roch for Ω¹ gives χ(Ω¹)=2χ(O_X)−c₂=−5145. By Hodge symmetry and Serre duality, if q=h¹(O_X), then h^{1,1}=5145+2q. The primitive space has dimension 5144+2q≥5144. No value of q is needed or inferred. The choice (3.2) alone is sufficient.

## 4. Approach I: the actual positive-weight cone deformation space

Put T=⊕H⁰(X,L^d), U=Spec T−{T_+}, and π_U:U→X. Since L is globally generated, U is the punctured total space of L^{-1}. Let A_L be the Atiyah extension in the convention determined by derivations of its function algebra:

    0→O_X→A_L→T_X→0,        extension class ±c₁(L).              (4.1)

The harmless sign depends on the transition convention and does not affect any kernel or nonvanishing assertion below. More intrinsically, homogeneous derivations raising function degree by k form D_k=A_L⊗L^k. On a local trivialization with fiber function t, such a derivation has the form

    t^k v + b t^{k+1}∂_t.

Changing t by g t changes b by a derivative of log g, yielding (4.1). Consequently

    0→L^k→D_k→T_X⊗L^k→0.                                     (4.2)

This is an extension of rank three, not just the tangent bundle. Positive k means that an equation of degree e acquires terms of degree e+k; in an equivariant first-order family the parameter has weight −k. These are the degree-raising, associated-graded-preserving directions. Weight zero deforms the polarized surface and produces cones; it is not our construction.

Choose any finite homogeneous algebra generators of T, of degrees w_i≥1, with P=C[z_i]→T and kernel I. On U the tangent-normal sequence is

    0→Θ_U→⊕_i O_U(w_i)→N_U→0.

Normality extends both derivations and Hom(I/I²,T) across the codimension-three vertex: a homomorphism extends coefficientwise by Hartogs and retains its relations. Thus its degree-k long exact sequence gives the **kernel formula**

    T¹_T(k)=ker[H¹(X,D_k)→⊕_i H¹(X,L^{k+w_i})].                 (4.3)

Here T¹ is the first cotangent deformation module, coker(Der(P,T)→Hom(I/I²,T)); no lci presentation is assumed. Formula (4.3) includes all syzygies through I/I². It is not the generally false identification T¹(k)=H¹(T_X⊗L^k).

At k=a, each a+w_i>a and Kodaira vanishing gives H¹(L^{a+w_i})=0. Therefore

    T¹_T(a)≅H¹(D_a).                                          (4.4)

No assertion H¹(L^j)=0 for *all* j is used: indeed such an assertion would be inappropriate for the obstructed cone. At this one weight (4.4) follows for **every generator degree**, regardless of how large it is. Tensoring (4.1) by L^a=K_X and using T_X⊗K_X≅Ω¹_X shows that the connecting map

    H¹(Ω¹_X)→H²(K_X)≅C

is cup product with c₁(L), equivalently intersection with L. Hence α in (3.2) lifts to a nonzero ξ∈H¹(D_a). Hard Lefschetz also makes H⁰(Ω¹_X)→H¹(K_X) an isomorphism; thus H¹(D_a) is precisely the primitive H^{1,1}. The lower bound in §3 is consequently a lower bound for the **actual** T¹_T(5), not merely for a tangent-sheaf cohomology group.

This first-order identification is in the classical Pinkham–Wahl framework. Di Natale–Fatighenti–Fiorenza explicitly identify primitive cohomology at the subcanonical weight (Theorems 2.4–2.5). Their globally imposed depth/vanishing hypothesis is not available here; (4.3) and weightwise Kodaira vanishing provide the needed replacement at k=a. We claim neither their Hodge-theoretic relation nor the Atiyah sequence as new. The remaining obligations are compatibility to all orders, exact full section-ring preservation, and nonconicality of λ=1. They are addressed next, rather than inferred from (4.4).

## 5. Approach II: integrate the negative Cartier neighborhood and reconstruct its contraction

### 5.1 Vanishing in precisely the groups used

For every integer k>a,

    H¹(X,L^k)=0,     H²(X,L^k)=0,     H²(X,T_X⊗L^k)=0,
    and therefore H²(X,D_k)=0.                                (5.1)

The first is Kodaira vanishing, L^k=K_X⊗L^{k−a}. The second is Serre dual to H⁰(L^{a−k})=0. The third is Serre dual to H⁰(Ω¹_X⊗L^{a−k}), which vanishes by the negative-line-bundle Kodaira–Akizuki–Nakano theorem, p+q=1<2. Exactness of (4.2) proves the last assertion. The same negative Nakano theorem with k=a gives H⁰(T_X)=H⁰(Ω¹_X⊗L^{-a})=0. No claim that H¹(D_k) vanishes for k>a is needed or made.

### 5.2 A compatible formal germ at a specified nonzero scalar

Let Ŝ=∏_{d≥0}L^d, the completed function sheaf of the split total space along X. Use a finite affine cover trivializing L; all multiple intersections are affine, so Čech cohomology computes the coherent groups in (4.2). Fix a 1-cocycle d_{ij} in D_a representing ξ. The derivations increasing degree at least a form a complete pronilpotent Lie algebra sheaf, with

    [D_r,D_s]⊂D_{r+s}.

Exponential and logarithm are valid in its degree topology over C. Glue local copies of Ŝ by exp(λd_{ij}), measured relative to the split transition functions. Their triple products are the identity in degree a because δd=0; discrepancies begin in degree 2a.

Inductively suppose the gluing has been corrected through degree (j−1)a. The degree-ja discrepancy on triple intersections is a Čech 2-cocycle in D_{ja}: associativity of fourfold products gives its cocycle identity, and lower-degree conjugations act trivially on the leading discrepancy. For j≥2, H²(D_{ja})=0 by (5.1). Choose a 1-cochain with this coboundary and compose the transitions with its exponential, with the sign canceling the discrepancy. This leaves all previous degrees intact. Since all brackets add degrees, only multiples of a occur. Choosing the correction at step j to carry λ^j gives compatible transitions for every scalar λ; at any fixed fiber order only finitely many λ-powers occur. Thus substitution λ=1 is legitimate. It is **not** evaluation at 1 of an arbitrary power series convergent only λ-adically.

Choose reverse transition maps to be inverses at every stage; the transported Čech products are taken in one local chart. The limit glues a Noetherian formal scheme 𝔚_λ with underlying X, locally Spf O_{X_i}[[t_i]], and invertible defining ideal J. Its associated graded sheaf is ⊕L^d and J/J²=L. It agrees with the split gluing in all degree shifts <a and has first degree-a cocycle λξ. X remains the same smooth surface, rather than moving in a family of polarized surfaces. Each local chart is formally smooth along X. This establishes formal compatibility, not yet a ring with the desired associated graded; that step follows separately.

### 5.3 Lift every section, including the low degrees

Set R_λ=Γ(𝔚_λ,O), F_d=Γ(𝔚_λ,J^d)⊂R_λ. A section s∈H⁰(X,L^d) with d≥1 defines compatible local homogeneous functions of degree d for the split gluing. For the perturbed gluing their first discrepancy has degree d+a. Correct it by a Čech 0-cochain in L^{d+a}; the obstruction lies in H¹(L^{d+a})=0. At each later stage the obstruction lies in H¹(L^{d+ja})=0 (j≥1); its degree is strictly greater than a, even for d=1. The cocycle identity follows from the gluing identity already constructed. The corrections converge in J. Therefore the symbol map

    F_d→H⁰(X,L^d)

is surjective for every d≥1. Degree zero needs its own check: H⁰(O_X)=C and constants lift exactly. It would be an error to invoke H¹(L^a)=0 at d=0; it is not asserted. The kernel at degree d is exactly F_{d+1}. Products induce ordinary products of the leading sections. Hence

    gr_F R_λ = T(X,L)                                         (5.2)

as graded algebras, in **all** degrees. This proves preservation of the full initial ideal, not just of displayed equations. No assumption about arbitrary good filtrations on MCM modules occurs.

By definition of the formal sheaf, R_λ=lim Γ(O/J^q). The lift argument also gives surjectivity R_λ→Γ(O/J^q): subtract lifts of successive leading sections, for finitely many degrees <q. Its kernel is F_q. Thus R_λ≅lim R_λ/F_q, and ∩F_q=0. Multiplicativity is immediate from J^iJ^j⊂J^{i+j}. R_λ/F₁=C; any element with nonzero residue is invertible by the convergent geometric series. Consequently R_λ is local with maximal ideal F₁.

There is also an actual flat parameter algebra behind these fibers, so the integration is compatible with Approach I. Perform the same construction over C[λ], completed in the Cartier direction only. Coherent cohomology on X tensored with C[λ] has the same vanishing, so the section-lifting argument gives symbols T_d⊗C[λ] in every degree. Choose C[λ]-linear lifts of a basis in each finite-dimensional T_d. Successive subtraction identifies the resulting complete filtered module Q with ∏_{d≥0}(T_d⊗C[λ]). This identification is a module identification, not an assertion that multiplication is the graded product. Q is torsion-free over the PID C[λ], hence flat. Componentwise polynomial division gives Q/(λ−c)≅R_c for every c∈C; equivalently the evaluation map is surjective with kernel (λ−c)Q. Its reduction modulo λ² has transition cocycle λξ, and hence class (4.4). All defining relations and their syzygies are therefore compatible in this actual flat formal-neighborhood family. No finite-type-over-C[λ] assertion is needed.

### 5.4 Finiteness is proved, not assumed from formal gluing

Apply the subtraction proof of (2.1) to (5.2), initially using F-completeness only. It gives an injective A=C[[x₀,x₁,x₂]]→R_λ and the exact formula (2.1). Thus R_λ is finite over the Noetherian A. In particular it is Noetherian. Its maximal ideal is F₁, and its quotient by nR_λ is a finite-dimensional local C-algebra; therefore a power of m lies in nR_λ. Together with (2.1) this proves F-, n-, and m-adic cofinality and completeness. The domain assertion follows from the domain T and leading products. We can now apply the independently checked I28 construction and obtain the regular projective W_λ=Proj C_F, finite over V, with closed Cartier surface X and conormal L. Normality of R_λ follows from §2.

### 5.5 Algebraization of the constructed formal neighborhood

This step identifies the *original* 𝔚_λ with the formal completion of that actual projective scheme W_λ; merely finding some regular model would not suffice for the nonconicality proof.

On X_i={s_i≠0}, the chosen global x_i∈F₁ has leading coefficient s_i, a unit in a trivialization of L. Therefore x_i generates J on 𝔚_λ|_{X_i}. For every r∈F_q, the quotient r/x_i^q is a regular formal function there. These quotients define the homomorphism from the Rees-chart algebra (C_F[(x_i u)^{-1}])_0 into Γ(𝔚_λ|_{X_i},O). On reduction modulo x_i this is exactly

    (T[s_i^{-1}])_0 ≅ Γ(X_i,O_X).

The induced maps on successive powers of x_i are also isomorphisms: on both sides x_i is a regular generator of the Cartier ideal and its conormal has the same transition s_j/s_i. Induction on the Cartier quotients followed by inverse limit makes the completed chart map an isomorphism. The maps agree on overlaps because they are given by the same fractions r/x_i^q. Thus

    𝔚_λ ≅ completion_X(W_λ).                                  (5.3)

This is an algebraizable contraction **over the complete local ring R_λ**, with W_λ finite type and projective over R_λ. No claim that the formal gluing converges analytically, or that R_λ is already the completion of a presented finite-type C-algebra, is used. The inspected free-tangent-sheaf manuscript's analytic-input algebraization proposition cannot supply such an assertion without its hypotheses, and is not invoked here.

## 6. A complete-local invariant excluding every positive grading

### 6.1 The model is intrinsic

On W_λ, mO_W=J by (2.2), so the universal property gives a morphism h:W_λ→Bl_m Spec R_λ. The line bundle J is relatively ample over Spec R_λ: it is the finite pullback of the relatively ample O_V(1); ampleness over the finite affine base Spec A also implies relative ampleness over Spec R_λ. It is also h*O_{Bl}(1). A positive-dimensional proper fiber of h would contain a curve on which this line bundle is simultaneously trivial and ample, which is impossible. Thus h is proper and quasi-finite, hence finite. It is birational, and W_λ is normal. Therefore W_λ is **the normalization of the m-blowup**, a construction preserved by every complete-local ring isomorphism. F_d is intrinsically the order-at-least-d filtration along its unique exceptional divisor X, by (5.3) and the definition of F_d. This is why forgetting the original filtration does not lose the obstruction.

### 6.2 The Euler obstruction is an all-order nonisomorphism test

Let E₀=t∂_t on each split local formal chart. Suppose 𝔚_λ admitted a continuous derivation E restricting to zero on X and inducing a nonzero scalar w on J/J². In the local coordinates used in §5,

    E_i = wE₀ + Σ_{k≥1} e_{i,k},         e_{i,k}∈D_k.

The split transitions preserve E₀. Perturbed transitions start at degree a. Up to degree a, conjugating E_i by exp(λd_{ij}) adds [λd_{ij},wE₀]=−waλd_{ij}; brackets with e_{i,k}, k>0, have degree >a. Consequently compatibility of E forces

    δ(e_{i,a}) = ±waλ d_{ij}.                                (6.1)

In H¹(D_a), this says waλξ=0. For λ≠0, a≥1 and w≠0 it contradicts ξ≠0. This argument allows arbitrary lower-degree local correction terms e_{i,k}; it is not an assumption that a putative isomorphism respects a previously chosen splitting. Pairing the horizontal image of the obstruction with C detects the nonzero number

    waλ C² = −2waλ n⁵;

for n=7, a=5, λ=w=1 it is −168070. Choice of canonical-bundle trivialization or sign changes this detector by a nonzero scalar, never to zero.

### 6.3 Any positive grading would supply the forbidden Euler field

Suppose R_λ were isomorphic to the completion at B_+ of a finitely generated nonnegative graded C-algebra B with B₀=C, generated in strictly positive degrees. Its grading gives a rational G_m action on every finite local quotient, with strictly positive weights on the maximal ideal, and hence a continuous action on R_λ. The normalized m-blowup is functorial, so the action lifts to W_λ and to (5.3).

Its induced action on X is trivial: its infinitesimal generator is a global section of T_X, and H⁰(T_X)=0 by §5.1; over C a connected torus with zero differential acts trivially. An automorphism of the line bundle J/J² over the identity of connected projective X is scalar, so its G_m action there is a character of weight w. It cannot have w=0: the intrinsic quotient m/F₂≅H⁰(X,L) is nonzero and has this same weight, while every weight on such a quotient of the maximal ideal of a positive grading is strictly positive. Thus w>0. Differentiation supplies exactly the E prohibited by (6.1). This contradiction excludes **every** positive grading, and in particular every isomorphism to the original cone after forgetting F. It applies to the fixed λ=1 ring, not merely to a first-order family.

## 7. Finish the no-MCM example and a separate cover attempt

For n=7 and λ=1, §§3–6 establish every hypothesis of the filtered-persistence proposition, so §2 proves that R_1 has no nonzero finite MCM module. Its normality, dimension, residue field, and punctured regularity have also been constructed. No module is replaced by an associated graded module. No upstream theorem is tested for truth.

For a genuinely different geometric attempt, try to thicken the cover π:X→B as a finite map between smooth Cartier neighborhoods whose normal direction is unramified. If the base divisor B has conormal M and the pullback of its ideal is exactly J, restriction forces π*M=L. This is impossible for this polarization. Intersect with π*e₁:

    n⁵(M·e₁)=L·π*e₁=n⁴,     so M·e₁=1/n,

contrary to integrality. This is an exact obstruction to this **unramified-normal, base-B, pulled-ideal** construction, not to arbitrary finite models (the successful I28 finite model has base P²).

Allowing ramification n in the normal direction replaces the condition by π*M=L^n; M=−K_B then works. The split model has a local normal equation z=t^n. Deforming branch equations as power series in z while retaining the radial μ_n action only permits derivation weights divisible by n: conjugating t^kv+b t^{k+1}∂_t by t↦ζt multiplies it by ζ^k. It therefore cannot realize the selected weight a=n−2 class for n≥3. For n=7 the obstruction is the explicit residue 5 mod 7. This excludes that symmetry-preserving branch recipe as a realization of **this class**; it does not prove vanishing of all T¹(kn), impossibility of symmetry-breaking branch deformations, or rigidity of the family. Solving a different branch construction is unnecessary once the formal-neighborhood construction succeeds, and no alternate surface is asserted on unsupported evidence.

## 8. Primary prior art, source contracts, and significance limits

The comparisons below use retained primary bytes and explicit passages; search-result summaries are not substituted for theorem statements. Version histories were checked against the retained arXiv pages on 2026-10-09. Literature retrieval times and SHA-256 hashes appear in the initial and resumed manifests. The original Wahl paper's publisher metadata is retained, but its attempted JSTOR full text returned HTTP 420; no claim of reading that full paper is made. The relevant normal-sequence machinery is read directly in Pinkham and in Coughlan–Sano's primary paper, which explicitly attributes its Theorem 3.7 input to Wahl. The argument in §4 also derives the precise weightwise formula it needs.

| Primary work and checked version | Exact scope inspected | Consequence for this candidate |
|---|---|---|
| [Pinkham, Astérisque 20 (1974)](https://www.numdam.org/item/AST_1974__20__1_0/) | Propositions 2.2–2.3; Section 3 normal-module comparison; Definition 4.1/Theorem 4.2; Proposition 11.2 | Graded tangent spaces, syzygy lifting and positive-weight rigidity tests are classical. The negative-grading hypothesis is unavailable here because T¹(5)≠0. |
| [Wahl, Annals 104 (1976), 325–356](https://annals.math.princeton.edu/1976/104-2/p05) | Metadata directly; normal-sequence statement through the explicitly read Coughlan–Sano passage | No unexamined all-order theorem from Wahl is imported. The formal gluing is written in §5. |
| [Coughlan–Sano, arXiv:1601.02381v3](https://arxiv.org/abs/1601.02381v3), 2018-12-13 | §3.3, §5 and Proposition 5.2, including the weighted full-section-ring formulation | The Atiyah bundle and weighted generator shifts are necessary. Conical-rigidity hypotheses concern every nonzero degree, not abstract surface rigidity. Their K3 results do not apply to the general-type surface here. |
| [Di Natale–Fatighenti–Fiorenza, arXiv:1512.00835v4](https://arxiv.org/abs/1512.00835v4), 2017-08-24 | Lemma 2.2, Theorems 2.4–2.5, Remark 2.7 | Primitive Hodge cohomology at the canonical weight is already known. The depth-three/global-vanishing hypothesis of their cone identification cannot be assumed for T. Section 4 replaces it by the exact degreewise kernel and proves its target zero at a. |
| [Bauer–Catanese, arXiv:1609.08128v1](https://arxiv.org/abs/1609.08128v1), 2016-09-26 | Theorem 1.2 | Their rigidity of the abstract complete-quadrangle surface for n≥4 does not imply positive-weight cone rigidity. We do not reprove or count that theorem. |
| [Bauer–Catanese, arXiv:1803.02984v2](https://arxiv.org/abs/1803.02984v2), 2018-05-02 | Theorems 0.1, 0.3–0.5; displayed Hilbert–Burch matrices and syzygies | Explicit equations in products of Fermat curves concern different ambient multigradings. They cannot simply be perturbed as a presentation of T(X,H). Our construction does not make that unsupported identification. |
| [Anghel, arXiv:2609.15589v1](https://arxiv.org/abs/2609.15589v1), 2026-09-14 | Theorem 1.1 and full-section-ring/graded-module distinction | The stronger Δ>3H² criterion is graded. It is not used to replace arbitrary local modules with graded ones. |
| [Chen, arXiv:2609.24142v1](https://arxiv.org/abs/2609.24142v1), 2026-09-21 | Main claim 1.1, Consequence 1.2, geometric-extension setup | This proposed quantitative bound is for completed cones with K numerically 4H. It is compared, not added to the accepted axioms or applied to K=5H. |
| [Chen–Sun, arXiv:1808.02172v1](https://arxiv.org/abs/1808.02172v1), 2018-08-07 | Theorem 1.4 and Remark 1.5 | Optimal extensions across negative divisors are prior art. The existence of our nonsplit base germ is a different obligation from modifying a sheaf on a supplied germ. |
| [Demailly, *Vanishing theorems for tensor powers of a positive vector bundle*](https://www-fourier.univ-grenoble-alpes.fr/~demailly/manuscripts/vanishing_anal.pdf), unnumbered author-hosted version retrieved 2026-10-09 | Section 1, equations (1.4)–(1.5) | Supplies the exact positive/negative Nakano ranges in §5.1. No stronger vector-bundle vanishing is assumed. |
| [Artin, *Lectures on Deformations of Singularities* (1976)](https://mathweb.tifr.res.in/Documents/Publications/Lectures/tifr54.pdf) | Introductory distinction between formal deformation and effectivity | No automatic analytical or finite-type algebraization is inferred from a formal gluing. Section 5.5 proves the complete-base algebraization needed here directly. |

The strongest complete *new-to-this-project* assertion proposed is the genuinely nongradable no-MCM ring, not its first-order deformation space. The candidate is stronger than saying that a marked filtered deformation is nontrivial: §6 excludes any positive grading of the completed local ring. Its realization proof uses a class on the actual obstructed surface, solves all higher compatibility equations by a uniform vanishing range, lifts every section, and identifies the model intrinsically. These are the items a significance reviewer should assess together.

There is a serious prior-art limit: much of this construction uses classical formal-neighborhood deformation theory and vanishing. The primitive-class identification is explicitly duplicated in the cited literature. A separate reviewer may judge the assembled realization theorem an application rather than a substantial discovery; no new-to-literature or worldwide-priority claim is made. The bounded current searches found no directly matching nongradable no-MCM theorem, but absence from those searches is not a novelty proof. The corpus scan is lexical and in place, over the complete 9,340-text cache belonging to all 749 manuscripts; it is not a claim to have read every cached text. It located C as the complete-quadrangle source and no textual `nonconical` hit. All cache Git and SHA identities are checked without copying the cache.

**No-count-padding verdict:** submit at most **one** full author candidate for separate proof and significance review. Assign **zero accepted findings now**. The independent A1–A5 check, canonical linear equivalence, primitive-space dimension bound, formal realization, Euler invariant, branch obstruction, and choice of larger primes are not individual findings. There is no new acceptance and no full-proof PASS from an independent reviewer in this record.

## 9. Deterministic validation, provenance, and remaining review obligations

Run from the `openai-proof-research` root:

    python frontier/experiments/i31_nonconical_no_mcm/resumed/diagnostics.py
    python frontier/experiments/i31_nonconical_no_mcm/resumed/verify.py

The diagnostic checks exact integers and rational sparse polynomials. It verifies source surface invariants for primes 3 through 101 and the allowed Veronese inequality; the primitive intersection and Euler detector; 4,000 shifted Rees-generator identities; 200,000 section-lifting indices and 1,980 later-obstruction indices; 112 Euler brackets, 112 exact truncated Euler conjugations, 336 exponential-product identities, and 112 second-order Baker–Campbell–Hausdorff discrepancies. It retains the twisted-cubic new-initial-monomial check and the μ₇ weight residue. No floating-point experiment is used.

These diagnostics do **not** construct a numeric Čech representative on the large Kummer surface, calculate its full defining ideal, prove coherent-cohomology vanishing, certify the infinite induction, or formally verify the algebraization/no-grading argument. The explicit geometric proof is responsible for those assertions. The scripts test its arithmetic, degree conventions, and local formal-algebra identities, rather than padding a count of random tests.

Provenance is separated into: (i) the parent's 43-file interruption checkpoint, (ii) all 111 original I28 files, (iii) additional initial artifacts not in that checkpoint, (iv) resumed input snapshots and current immutable dependencies, (v) pinned C blobs and the complete corpus manifest/tree, and (vi) the final report, scripts, literature, contracts, passages, and deterministic outputs. The report and new artifacts are sealed. Verification reports live `TEN-FINDINGS.md` drift independently and never treats a later shared-ledger edit as proof corruption.

One recovery detail is recorded explicitly: an in-flight pre-resume retrieval command appended two attempt records to the original literature manifest after the parent had checkpointed it. On resumption the 17-entry checkpoint manifest was reconstructed and its expected digest checked **before** restoring its original bytes. The appended 19-entry bytes remain under `resumed/pre-resume-appended-literature-manifest.json`; the recovery record names both hashes. All 43 checkpointed files now have their checkpoint bytes, and no retained response was overwritten. A failed old-host Demailly TLS attempt and the HTTP-420 Wahl response remain evidence of retrieval limits; the corrected author-host Demailly download is a distinct resumed artifact.

The four source identities are frozen in `pinned-manifest.json`; notably `paper.tex` has Git blob `df6c3550b6fa6866034f792a2f53941b6a3e6703` and SHA-256 `76d8de92a9ef5850d2f6f185812051aeedfa100885f96fe93ef9cd7b5d94dea0`, while `surface.tex` has Git blob `166f5c263832cc3e41a2517433b0e6482ac1eef5` and SHA-256 `efc4a3511aab3c9271ae7aeaa2dede4412b47ebc2ecfb7466123c72156a5f9c4`. Full immutable raw URLs, exact source statements, read-passages, literature versions and retrieval dates accompany those hashes. No reliance on the truncated root-tree cache occurs.

**Review handoff.** The author supplies a complete constructed proof of the stated complete-local candidate, without claiming analytic convergence, a finite-type C presentation, quantitative local-cohomology bounds, or distinct nonzero-fiber isomorphism classes. The most important independent proof checks are the pronilpotent Čech induction and section lifting in §5, the intrinsic normalized-blowup identification, and the lifted-action/Euler argument in §6. Significance review must compare the *whole realization* against positive-weight subcanonical-cone deformation theory, while discounting the known primitive-cohomology identity and the I28 transfer. These review gates, not an unproved extra claim silently added to the theorem, are the remaining obligations before acceptance.

The final retained integrity run is `../experiments/i31_nonconical_no_mcm/resumed/verification.json`: **PASS for integrity and deterministic replay**, with zero errors, 43 checkpointed files, 111 I28 files, four pinned C sources, all 9,340 cache files across 749 manuscripts, six exact source contracts, 18 hashed read passages, and 26 sealed candidate artifacts. Both initial and resumed ledger drift are informational. This is expressly not an independent mathematical proof PASS.
