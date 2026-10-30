# Author proof of T195D93

Status: complete author argument submitted for independent assessment, conditional on the stipulated pinned source. No independent correctness or contribution verdict is asserted. The statement is exactly `FROZEN.md`; `freeze.json` records its bytes and the substantial feasibility work preceding the freeze. This is a research proof, not a publication manuscript.

Write h=H², Δ=K_X²−2c₂(X). Length means module length; all residue fields used for length comparisons are C. For a coherent sheaf F of positive rank on D=P², write c₁(F) for the integer coefficient of the line class and ch₂(F) for the degree of its second Chern character. Define the additive expression

    Φ(F)=2ch₂(F)−c₁(F).

It is additive in exact sequences, including sequences with torsion terms. In particular Φ(O_D)=0. The proof retains the actual exceptional-divisor lattice throughout; stable free summands will have zero cost for this expression.

## 1. Inputs and the fixed geometric model

The pinned input is source195, *A Complete Local Domain Without a Small Cohen–Macaulay Module*, September 23, 2026, `build/paper.tex`, at revision fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Its complete URL, Git blob and SHA256 are in `canonical.json`. The operative inputs are §2 `sec:cone`, equations `eq:completion`, `eq:conormal`, the double-dual extension argument; §3 `lem:balance`, `eq:transform`; §4 `eq:layers`, `eq:Tor`; and §5 `lem:factor`, `eq:RR-variance`. All these operations are stipulated, not truth-audited here.

Choose three sections of O_X(H) without a common zero, as in §2. They define a finite surjection f:X→D=P² of degree h, with f*O_D(1)=O_X(H). Let S=C[x₀,x₁,x₂], A=C[[x₀,x₁,x₂]], and identify R=T⊗_S A with the completion in the frozen statement. Let V be the base change to A of Tot(O_D(−1)), and W its base change by X→D. The source gives the diagram

    X ⊂ W --p--> Spec R
    |   |g          |
    D ⊂ V ------> Spec A.

Here V and W are integral regular Noetherian schemes, proper over Spec A; g and f are finite. The complements of X and D are respectively the punctured spectra of R and A. Denote them by U_R and U_A. The ideals J of X and I of D are invertible and satisfy J=g*I, I|D=O_D(1), J|X=O_X(H). There is a projection ρ:V→D, inherited from the total space. The ring R is a normal three-dimensional complete local domain, regular outside its closed point.

The finite map f is flat. Indeed, at a point of X over a point of D, parameters of the regular local base form a system of parameters in the finite local algebra. The latter is regular, hence Cohen–Macaulay; these parameters are a regular sequence. The local flatness criterion, or Auslander–Buchsbaum applied over the regular base, gives finite local freeness. Its rank is h. Base change gives the same assertion for g and for U_R→U_A.

Let M be any nonzero finite reflexive R-module of rank r. Its rank is positive since R is a domain. Its restriction to U_R is locally free: local rings there are regular of dimension at most two, and a reflexive module over such a ring is free by depth at least two and Auslander–Buchsbaum (with the dimension-one case included). Consequently its finite pushforward E, viewed as an A-module, is locally free on U_A of rank N=rh. At the closed point depth_A E=depth_R M≥2: local cohomology for the maximal ideal of A agrees with that for m because its extended ideal has radical m. The module E is torsion-free over A. It is therefore reflexive, since it is free off the closed point and satisfies S₂ there and at the closed point. Its projective dimension over A is at most one.

Set

    T_E=Ext¹_A(E,A),       L=length_A T_E.

The Ext module is finite and is zero away from the closed point, so L is finite. Local duality over the complete regular local ring A of dimension three identifies T_E with the Matlis dual of H²_n(E). Matlis duality preserves finite length. Independence of local cohomology from the radical of the ideal gives H²_n(E)=H²_m(M). Both lengths are C-vector-space dimensions. Thus

    L=length_R H²_m(M).                                      (1)

These are the usual local-duality and Auslander–Buchsbaum statements; primary references are Stacks Project Tags 0AAK and 090V. Chen, Lemmas 2.4–2.5 in the version cited below, also treats finite deficiency and punctured freeness in this precise section-ring setting. Neither Chen's later main claim nor an unproved algebraization of M is used.

Take the coherent extension ℰ=(p*M~)** on W. The source's local depth argument, which requires the already established punctured local freeness, gives a torsion-free restriction P=ℰ|X of rank r. The rest of the proof is allowed to alter ℰ along X, but never changes ℰ|U_R=M~|U_R. In particular ℒ=g_*ℰ is a torsion-free coherent lattice on V extending E~|U_A.

## 2. A classical syzygy filtration with the exact defect multiplicity

We prove the local statement needed rather than presupposing a graded model for E. This is the dimension-three horseshoe/Schanuel form of the classical Horrocks devissage. Horrocks's primary *Construction of bundles on Pⁿ*, Astérisque 71–72 (1980), pp.197–203, theorem on p.197 and Eilenberg–MacLane discussion on p.198, gives the corresponding projective stable filtration by twisted exterior tangent bundles. Those pages were read from the original volume. The following local proof supplies the precise version and multiplicity used here.

Choose a finite free resolution

    0 → A^b → A^a → E → 0.

Its dual is exact as

    0 → E* → A^a → A^b → T_E → 0.                            (2)

Thus E* is a second syzygy of T_E. Choose a composition series of T_E with L residue-field factors. Resolve each such factor by the Koszul resolution on x₀,x₁,x₂. Repeated applications of the horseshoe construction give a finite free resolution of T_E whose second syzygy Z has a filtration with exactly L successive factors Ω²_A C. To see the exactness at the syzygy level, in each horseshoe diagram the free terms are the direct sums of the outer terms; taking successive kernels and using the snake lemma gives

    0 → Ω²(T') → Ω²(T) → Ω²(T'') → 0

for the chosen horseshoe resolutions of 0→T'→T→T''→0. Iteration through the composition series proves the assertion. For L=0 take Z=0.

Comparison of two finite free presentations through degree one gives Schanuel's stable equivalence. Hence, for some finite u,v≥0,

    E* ⊕ A^u ≅ Z ⊕ A^v.                                   (3)

This follows by applying the elementary pullback proof of Schanuel's lemma twice; no cancellation of nonfree modules is assumed. Restrict (3) to U_A and dualize. All factors of the filtration of Z are locally free there, so the dual filtration is exact in the reverse order. Since E is reflexive, this gives a filtration of

    E~|U_A ⊕ O_U_A^u

with L factors (Ω²_A C)~*|U_A and v trivial line factors.

The Koszul complex identifies Ω²_A C with the kernel of A³→A, (a_i)↦Σx_i a_i. After pullback to V and division by the exceptional parameter, its bundle on U_A identifies with ρ*Ω¹_D(1)|U_A, by the Euler sequence. Its dual is

    ρ*B|U_A,        B=T_D(−1)≅Ω¹_D(2).                     (4)

The ideal I is trivial on U_A, so the harmless choice of divisor trivialization in this identification changes none of the assertions. The resulting filtration is a filtration of the actual punctured bundle after the stable isomorphism (3), not an assertion that E descends to P² or is graded.

## 3. The two atom budgets for every lattice

For either B₀=O_D or B₀=B from (4), let ℒ₀=ρ*B₀. Let K be any coherent torsion-free sheaf on V whose restriction to U_A is identified with ℒ₀|U_A. We claim

    Φ(K|D) ≥ 0          if B₀=O_D,
    Φ(K|D) ≥ −2         if B₀=B.                            (5)

The second assertion is needed for arbitrary lattices, not just the pullback of B.

First B is slope stable. It has rank two, c₁(B)=1 and ch₂(B)=−1/2 by the Euler sequence. A saturated rank-one subsheaf of B on the smooth surface D is a line bundle O_D(d): the quotient is torsion-free, and the depth lemma makes the rank-one kernel reflexive. If d≥1, an inclusion would give a nonzero section of Ω¹_D(2−d). There is no such section. For 2−d≤0 this follows from the Euler sequence's injection into O_D(1−d)^3; for 2−d=1 the induced map on sections C³→H⁰(O_D(1)) is an isomorphism. Thus d≤0<1/2. The bundle O_D is semistable as well.

Clearing denominators on a finite affine cover gives, for an integer a≤−1 chosen sufficiently negative and some q≥0,

    I^q(I^aℒ₀) ⊂ K ⊂ I^aℒ₀.

In particular Q=I^aℒ₀/K is killed by a power of I. Set Q_j=I^jQ/I^(j+1)Q and n_j=rank_D Q_j. These are quotients of B₀(a+j), so 0≤n_j≤rank B₀. If µ₀ is the slope of B₀, semistability gives

    c₁(Q_j) ≥ (µ₀+a+j)n_j.                               (6)

For precision, first pass from Q_j to its torsion-free quotient. It remains a quotient of the semistable bundle B₀(a+j), so its slope is at least that of the bundle. The removed torsion has effective divisorial first Chern class; zero-dimensional torsion has first Chern class zero. This also covers n_j=0. No global generation of B is assumed.

The source's Cartier derived-restriction calculation applies verbatim to the reference bundle I^aℒ₀. Since the Cartier equation acts injectively on both lattices, and Tor₁(Q_j,O_D)=Q_j(1), it gives in G₀(D)

    [K|D]=[B₀(a)]+Σ_j([Q_j(1)]−[Q_j]).                    (7)

In particular K|D has the stated atom rank; it need not be torsion-free. For a sheaf Q on P²,

    Φ(Q(1))−Φ(Q)=2c₁(Q),

as follows by multiplying its Chern character by exp(c₁(O(1))). Applying this to (7) and (6) gives

    Φ(K|D) ≥ Φ(B₀(a))+Σ_j 2(µ₀+a+j)n_j.                  (8)

This minimizes an affine expression using the actual layer capacities, independently of how Q's layers are glued.

For B₀=O_D, µ₀=0 and Φ(O_D(a))=a²−a. Negative coefficients in (8) occur for j=0,...,−a−1. Since n_j≤1, filling all those slots and discarding nonnegative terms gives the lower bound

    a²−a + 2Σ_{j=0}^{−a−1}(a+j)=0.

For B₀=B, µ₀=1/2 and Φ(B(a))=2a²−2. The negative coefficients are 2a+1+2j for the same indices; now n_j≤2. Hence the lower bound is

    2a²−2 + 2Σ_{j=0}^{−a−1}(2a+1+2j)=−2.

These prove (5). Notice that the target K was never twisted. The integer a changes the comparison bundle, keeping the affine functional on the original restriction fixed.

## 4. Transport to the actual lattice and exact stable cancellation

Let ℒ be any coherent torsion-free lattice for E~|U_A on V. Use (3) to view the punctured restriction of ℒ⊕O_V^u as a bundle with the filtration in §2. Extend this filtration to saturated coherent subsheaves of ℒ⊕O_V^u. Concretely, for each generic subspace in the filtration, intersect it with ℒ⊕O_V^u in the generic vector space. On a Noetherian affine chart this is a submodule of a finite module and is finite; these intersections glue. The quotient is torsion-free because multiplication by a nonzero regular function does not change membership in the generic subspace. Over U_A the intersection agrees with the original subbundle: its quotient there is already locally free. The successive quotients K_i on V are therefore torsion-free lattices for exactly the specified B or trivial-line factors.

Restriction of each filtration sequence to D remains exact. Indeed, its quotient K_i is torsion-free on the integral scheme V, so multiplication by the Cartier equation is injective and Tor₁(K_i,O_D)=0. Additivity of Φ and (5) now yield

    Φ((ℒ⊕O_V^u)|D) ≥ −2L.

But Φ(O_D)=0. Consequently the stable summands disappear without an error depending on u or v:

    Φ(ℒ|D) ≥ −2 length_A Ext¹_A(E,A).                     (9)

This applies to every lattice of E, including the pushforward of the balanced extension in the next section. No new independent choice of a favorable lattice is made after balancing. The integer L counts composition factors of the actual Ext module, rather than a number of generators or the length of a graded substitute.

## 5. Align the surface factors using the already available operation

Put

    b=K_X.H/(2h)+3/2,       c=1/4−Δ/(12h).

Starting from ℰ in §1, twist by an integer power of J so that the maximum normalized H-slope of P=ℰ|X is strictly below b+1. Whenever its last HN quotient G has slope below b, perform the source elementary transform ℰ'=ker(ℰ→i_*G). The source Cartier identity supplies

    0 → G(H) → ℰ'|X → ker(P→G) → 0.

The new restriction is torsion-free, its maximum slope is still below b+1, and its average slope increases by rank(G)/r≥1/r. Thus only finitely many such steps occur: an infinite sequence would have an unbounded average below the fixed upper bound b+1. The terminal HN slopes are all in [b,b+1). Every step preserves rank and the entire punctured bundle.

This fixed-interval operation is already explicit in Chen, Proposition 3.3, and in actual arithmetic r83 `slope-budget.md`; it is credited in full. The offset b is a parameter of that same operation. We retain the notation ℰ,P for the terminal pair and put F=f_*P. Finite pushforward is exact. The source's identity J=g*I gives

    F=(g_*ℰ)|D,

of rank N=rh. Therefore (9) applies to this very F.

Let G_i be the HN factors of P, of rank u_i, and set w_i=u_i/r. The source `lem:factor` gives for F_i=f_*G_i

    m_i=c₁(F_i)/(u_i h)=µ(G_i)−b ∈[0,1),
    v_i=2ch₂(F_i)/(u_i h)−m_i² ≤ c.

By exactness and additivity,

    Φ(F)/N = Σ_i w_i (v_i+m_i²−m_i) ≤ c,                  (10)

because m_i²−m_i≤0. This uses the factor bound at its full arbitrary-surface scope, including the Hodge-index square completion in `eq:RR-variance`. No assumption K_X≡aH is inserted.

Combining (9), (10), N=rh and (1) gives

    −2L ≤ Φ(F) ≤ rh(1/4−Δ/(12h)),
    L ≥ r(Δ−3h)/24.

Length is nonnegative, so this is exactly

    length_R H²_m(M) ≥ r max(0,(Δ−3h)/24).

Finite length was proved in §1. Every quantifier and constant in the frozen statement is retained. This completes the author argument.

## 6. Attribution and mathematical boundaries

Horrocks's stable devissage is classical. The elementary horseshoe/Schanuel proof, Koszul/Euler identification, slope stability of Ω¹(2), local duality, and saturated extension of a subbundle filtration are also credited classical operations. The source supplies the regular model, the exact Cartier layers, transforms and numerical factor estimate. The fixed interval and the zero-defect 3h threshold were already recovered in r83. None is relabelled as new here.

The deduction requiring assessment is the quantitative passage from an arbitrary punctured reflexive module's finite Ext defect to the SAME balanced lattice: the two atom capacities give costs 0 and −2 for the additive functional Φ, and the stable free summands cancel exactly. This paragraph identifies the integration being assessed; it does not certify it as unpaid or substantial. The complete generic reduction above could be judged technical by an independent contribution review.

Chen's *A local cohomology obstruction to small Cohen–Macaulay modules*, [2609.24142v1](https://arxiv.org/pdf/2609.24142v1), prints “Main claim” and “Proposed proof”; those qualifications are retained. Its claimed bound for K_X≡4H is precisely the specialization here, since Noether's formula gives (Δ−3h)/24=15h/8−χ(O_X). Its §§3–6 contain fixed-interval normalization, Euler estimates, two-tail bounds and fixed-source persistence. Those operations were actually read. Their printed tail bounds use the specified slope range and canonical slope, not arbitrary canonical degree. The proof here does not import Chen's main claim as stipulated truth, or infer a uniform tail inequality outside its hypotheses.

Anghel's [2609.15589v1](https://arxiv.org/pdf/2609.15589v1), Theorem 1.1 and §2, supplies the graded/aCM threshold Δ≤3h via finite projection, Horrocks splitting and majorization. It is not permission to grade an arbitrary completed-local reflexive module. The argument here instead uses stable syzygy devissage on the puncture and the actual Cartier lattice. Horrocks's original [Astérisque volume](https://smf.emath.fr/system/files/filepdf/AST_1980__71-72__1_0.pdf), pp.197–198, is the primary stable-filtration antecedent; the unacquired Evans–Griffith book statement is not an unproved dependency.

No claim is made about worldwide priority, an equality classification, a uniform choice of stabilization ranks, a bound on balancing steps independent of M, nonconical deformations, or lim Cohen–Macaulay sequences. No finite experiment is used to prove the theorem.
