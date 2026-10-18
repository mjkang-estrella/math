# Different costs among spectral-gap actions of one finitely presented group

Myeongjin Kang; no affiliation. Original prose CC BY 4.0.

Author-side candidate T259S, at the unchanged scope in `scope-259.md`. No independent proof or contribution verdict, formal certification, acceptance or campaign count is asserted. The lower bound from source259 is stipulated, not re-audited.

## 1. Statement and dependencies

Put A=F(a,b₁,...,b₉₉), u₀=1, uᵢ=uᵢ₋₁abᵢ, w=u₉₉a, J=⟨b₁,...,b₉₉,w⟩ and Γ=A *_J (J×⟨t⟩). Write B=J×⟨t⟩. Let F=F(c,d). There is a surjective homomorphism q:Γ→F satisfying

    q(a)=d, q(t)=1, q(u₁)=c, q(uᵢ)=1 (2≤i≤99).

On X=[0,1]^Γ and Z=[0,1]^F with product Lebesgue measures use the right Bernoulli convention (xg)(h)=x(gh). Define Y=X×Z and (x,z)g=(xg,zq(g)).

**Theorem.** Γ is finitely presented. Both Γ-actions X and Y are essentially free, p.m.p. and weakly mixing. The full orbit relation on Y has cost 1. For every complex mean-zero f∈L²(Y),

    ||f(·w)−f||²₂ + ||f(·b₁)−f||²₂ ≥ (4−2√3)||f||²₂.       (1)

The same inequality holds on X. In particular both actions have spectral gap and are strongly ergodic. In contrast, the cost on X is at least 1+η, for every source-admissible η=α/100>0 with

    0<α<1/200,    e⁹⁶ 96⁹⁹ α³/95⁹⁵ < 1/2.

These admissible α exist since the expression tends to zero with α. Thus this explicit finitely presented group has two free weakly mixing spectral-gap actions with different costs.

The only deep input in the last comparison is source259's Bernoulli lower bound (`introduction.tex`, main theorem; `conclusion.tex`). Its normal-form lemma supplies the embeddings, infinitude of Γ and infinite order of t. The standard lower bound of one for an aperiodic p.m.p. relation is also available as source259 `compression:cost-one`. The construction of cheap B-graphings is Gaboriau's commuting-marker argument (Proposition VI.23), used explicitly in source259. All these are credited inputs; the proposed additional operation is the quotient that makes exactly one row position exceptional while retaining a free subgroup acting as a Bernoulli shift on the whole space.

## 2. The quotient and finite presentation

The elements a,u₁,...,u₉₉ form a free basis of A: the recursive definitions express each uᵢ in the original basis, and the inverse expressions are

    bᵢ=a⁻¹uᵢ₋₁⁻¹uᵢ.

These mutually inverse substitutions define inverse homomorphisms of the corresponding free groups. Hence the prescribed values on a and the uᵢ define a homomorphism q_A:A→F. More explicitly,

    q_A(b₁)=d⁻¹c,  q_A(b₂)=d⁻¹c⁻¹,
    q_A(bᵢ)=d⁻¹ (3≤i≤99),  q_A(w)=d.

On B put q_B(jtⁿ)=q_A(j). This is a homomorphism because the t-factor is killed, and its restriction to J agrees with q_A. The amalgam universal property gives q. Its image contains d=q(a) and c=q(u₁), so it is surjective.

Γ has the finite presentation

    ⟨a,b₁,...,b₉₉,t | [t,bᵢ]=1 (1≤i≤99), [t,w]=1⟩.        (2)

Indeed, a map from this presentation to any group is exactly a homomorphism from A together with an element commuting with each displayed generator of J, hence with all of J. This is precisely the universal property of A *_J (J×Z). The source's embeddings imply that Γ is countably infinite and t has infinite order. Finite presentability is already immediate in the source and in the previous parent screen; it carries no separate contribution claim here.

## 3. Measure spaces and complete markers

The countable products X,Z,Y are standard Borel probability spaces. Coordinate permutations preserve the product measures and obey the stated right-action law. For any g≠1, xg=x implies x(g)=x(1), an event of probability zero for two independent atomless coordinates. Countability of Γ gives an invariant Borel conull set of free points in X. The action on Y is free on its product with Z. Restriction to an invariant conull set preserves cost and all L² assertions.

We construct graphings on the full Y; exceptional null sets can be included in marker domains, so generation is pointwise even before this restriction.

Fix 0<p<1. In X set

    C⁰_p={x:x(1)<p},
    N_p={x:x(tⁿ)≥p for every n∈Z},
    C_p=(C⁰_p∪N_p)×Z.

These sets are Borel. Infinite order of t and product independence imply µ(N_p)=0: the constraints for 0≤n<N have probability (1−p)^N. Consequently µ_Y(C_p)=p. Every t-orbit meets C_p. An orbit missing C⁰_p×Z lies entirely in N_p×Z, using q(t)=1 and (xtᵏ)(tⁿ)=x(tᵏ⁺ⁿ).

Independently fix 0<ρ<1 and put

    E⁰_ρ={z:z(1)<ρ},
    E_ρ=E⁰_ρ ∪ (Z \ ⋃_{n≥0} E⁰_ρ cⁿ).

Here Ecⁿ means the image of E under the right shift cⁿ. These are Borel sets. A point z belongs to E⁰_ρcⁿ precisely when z(c⁻ⁿ)<ρ. The coordinates c⁻ⁿ are distinct, so the complement of their union has probability zero. Thus ν(E_ρ)=ρ and, by construction,

    Z=⋃_{n≥0} E_ρcⁿ.                                      (3)

The extra null set merely gives pointwise coverage; no invariant-measure limit or finite-level approximation is used.

## 4. Graphing the commuting factor

Let Φ_p contain the full t-map on Y and the restrictions to C_p of b₁,...,b₉₉,w. Each is a measure-preserving Borel partial bijection. Its cost is

    C(Φ_p)=1+100p.

For any y and any displayed generator j of J, choose n∈Z with ytⁿ∈C_p. The path

    y → ytⁿ → ytⁿj → ytⁿjt⁻ⁿ=yj

uses t-steps, one retained j-edge, and reverse t-steps. The endpoint equality follows from [t,j]=1. Thus Φ_p generates the full B-orbit relation everywhere. This is exactly the classical/source marker operation, with the extra coordinate carried along.

Add to Φ_p the a-map restricted to X×E_ρ. Denote the resulting finite graphing by Ψ_{p,ρ} and its generated Borel equivalence relation by R. A relation generated by finitely many Borel partial bijections is Borel because it is the union of the graphs of countably many finite words in these maps and their inverses. Its cost is

    C(Ψ_{p,ρ})=1+100p+ρ.                                   (4)

All its edges are Γ-orbit edges, and R contains every B-edge. We next prove that it contains every a-edge as well.

## 5. One exceptional row position

Call a Borel set D⊂Z available if

    ((x,z),(x,z)a)∈R for every x∈X and z∈D.                 (5)

The quantifier over **every first coordinate** is essential. Initially E_ρ is available. We claim that availability of D implies availability of Dc.

Take any v=(x,z) with z∈Dc and put y=vu₁⁻¹. Then the quotient coordinate of y is zc⁻¹∈D. The source vertices of the 100 a-edges in the row word

    w=a b₁ a b₂ ... a b₉₉ a

are yuᵢ, 0≤i≤99. Their quotient coordinates are all that of y, except for i=1, where the coordinate is that of y times c. Indeed q(u₀)=1, q(u₁)=c and q(uᵢ)=1 for2≤i≤99.

Thus all the row's a-edges except the one starting at yu₁=v are in R, by (5). Every intervening bᵢ-edge and the full w-edge are already in R. More explicitly, y connects to yu₁ by the first known a-edge followed by b₁. Starting at yw, traverse the suffix of the row backwards, stopping at yu₁a: its reverse a-steps are reversals of known edges at yuᵢ for i=2,...,99, and its other steps are inverses of b₂,...,b₉₉. Consequently

    v=yu₁  R  y  R  yw  R  yu₁a=va.

This proves (5) over Dc. The first coordinate of y is xu₁⁻¹, with no restriction, which is why the argument establishes every a-edge over Dc, not only a selected section of that fiber.

Induction shows E_ρcⁿ is available for every n≥0. Equation(3) therefore supplies every a-edge. Since B together with a generates Γ, R is exactly the full Γ-orbit relation on Y.

For any ε>0 choose p=min(1/2,ε/400) and ρ=min(1/2,ε/4). Then100p+ρ<ε (each summand is at most ε/4). Equation(4) gives an actual finite Borel graphing of the full relation of cost below1+ε. Hence Cost(Y)≤1. On the invariant conull free part all orbits are infinite, so `compression:cost-one` gives Cost(Y)≥1. This proves the exact cost assertion.

## 6. Bernoulli restriction to a free subgroup

Let H=⟨w,b₁⟩. Source259's free-basis statement for J makes H free on this pair. Equivalently one can see this directly from q: their images d,d⁻¹c are a free basis of F(c,d), with inverse substitution c=d(d⁻¹c). Any relation in w,b₁ would therefore map to a relation in a free basis and be trivial. Moreover q|H maps this basis onto a basis and is an isomorphism H→F.

Choose representatives r for the coordinate orbits Hr of left multiplication by H on Γ. The coordinate map

    x ↦ (h ↦ (x(hr))_r)

identifies X|H, preserving measure, with the H-Bernoulli shift whose base is [0,1]^{H\Γ}; notation H\Γ denotes this set of coordinate orbits. The action of g∈H replaces h by gh, precisely the right Bernoulli convention. The isomorphism q|H similarly identifies Z|H with the H-Bernoulli shift of base [0,1]. Consequently Y|H is the H-Bernoulli shift of base

    K=[0,1]^{H\Γ}×[0,1]

with its product probability. This statement concerns the restriction to H, not the full Γ-action.

## 7. Explicit spectral gap

For completeness we give the elementary representation estimate, so the displayed constant is not an unstated imported hypothesis. For any standard probability base K, choose a countable orthonormal basis {e₀=1,e₁,...} of L²(K). The tensors

    ∏_{h∈H} e_{ℓ(h)}(z(h)),

where ℓ:H→{0,1,...} has finite support, form an orthonormal basis of L²(K^H); finite-coordinate functions are dense by the product sigma algebra. Removing the all-zero label gives a basis of L²₀. H permutes these labels by translation. The stabilizer of a nonempty finitely supported label is trivial: if g stabilizes its finite nonempty support S, then all gⁿs lie in S for any s∈S, forcing g to have finite order; the free group H is torsion free. Each orbit of basis vectors therefore spans a copy of the regular representation of H. Thus L²₀ is a Hilbert direct sum of regular copies.

In a regular copy let T be adjacency on the Cayley tree for w,b₁ and their inverses. This tree has degree4. Choose any end, orient every vertex toward its unique neighboring parent on the ray to that end, and call the other three neighbors children. For a finitely supported complex function ξ,

    |⟨Tξ,ξ⟩| ≤ ∑_{parent v, child u} 2|ξ(v)||ξ(u)|
               ≤ ∑_{parent v, child u}
                    (|ξ(v)|²/√3 + √3|ξ(u)|²)
               =2√3 ||ξ||².

The middle inequality is the elementary nonnegative square inequality. Each vertex occurs three times as parent and once as child. Boundedness of T follows already from its four unitary summands; density extends the quadratic-form bound to all ξ. Summing over regular copies gives the same bound on L²₀(K^H).

For U_g f=f(·g), unitarity gives

    ||U_w f−f||²+||U_{b₁}f−f||²
       =4||f||²−⟨(U_w+U_w⁻¹+U_{b₁}+U_{b₁}⁻¹)f,f⟩
       ≥(4−2√3)||f||².

The adjacency operator is self-adjoint, so its quadratic form is real; the formula is valid for complex f. Applying the Bernoulli identifications proves(1) on both Y and X.

If (A_n) is asymptotically invariant under Γ, apply(1) to f_n=1_{A_n}−µ(A_n). The left side tends to zero, while ||f_n||²=µ(A_n)(1−µ(A_n)). This is strong ergodicity.

## 8. Weak mixing and the cost comparison

An H-Bernoulli shift is mixing: for two finite-coordinate functions, sufficiently far translates have disjoint finite coordinate supports and hence independent values. Approximation in L² and Cauchy–Schwarz extend the correlation limit to arbitrary L² functions. The diagonal square of a Bernoulli shift is again Bernoulli, with the squared base, so is ergodic. Hence X×X and Y×Y are H-ergodic and consequently Γ-ergodic. This is weak mixing of the full Γ-actions.

Finally, source259's main theorem gives Cost(X)≥1+η at the displayed admissible parameters. Sections3–7 prove Cost(Y)=1 and the required dynamical properties without changing that source. This completes every item of the frozen T259S theorem.

There is no claim that Y is Γ-mixing. The infinite subgroup ⟨t⟩ fixes the nontrivial Z-factor, so correlations of nonconstant functions depending only on Z do not decay along tⁿ. Neither a finite-height limit nor a product with the old profinite action would remove that old action's asymptotically invariant factor; this construction uses a different quotient action.

## 9. Credit and proof status

The source group, the Bernoulli cost separation input, finite presentability and commuting-marker graphing are pre-existing. The earlier parent packet `fresh-parent-discovery-r2/screen.md` already supplied the routine cost-one profinite-height action and identified its lack of strong ergodicity. The regular-representation decomposition and free-tree estimate are classical elementary facts, fully proved here but not claimed new. The proposed residual construction is the nonamenable quotient with one exceptional row source, together with its simultaneous graphing and free-subgroup properties. Whether that contribution is substantial remains for an independent comparison; bounded searches do not establish literature priority.

The parent read the frozen scope and source group-actions body, checked the interior-edge recovery and Bernoulli restriction, and emphasized the all-first-coordinates quantifier in availability. The parent also supplied the equivalent rooted-tree adjacency estimate; the author proof here uses an end orientation. That is author-side assistance, not an independent gate. No scope change or mathematical repair was requested. Precise primary and source reading limits are separate from this mathematical proof.
