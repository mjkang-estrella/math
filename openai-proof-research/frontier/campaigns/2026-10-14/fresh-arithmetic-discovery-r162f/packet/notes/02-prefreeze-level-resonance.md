# Arithmetic162f: full-category level-spreading feasibility calculation

PREFREEZE / no nominee. These are calculations testing a proposed operation, not a frozen theorem or an author-proof submission. All source proofs remain stipulated true. The source/primary/history integration in note 01 preceded this extended derivation.

## 1. The exact proposed operation and a necessary test

Fix a smooth projective connected complex curve X and a connected simple G. Put Y=Bun_G(X) and L=det RΓ(X,ad E). Let s be the determinant exponent, so the shifted source level is c=2h∨s+h∨. A prospective algebraic spreading operation would produce a nonempty Zariski open T⊂A¹_s and a quasi-compact open U⊂Y such that the relative twisted category on Y×T restricts equivalently to the one on U×T, with inverse star extension, and these identifications recover the full twisted D-module categories after every geometric specialization t∈T(C). Allowing a quasi-compact open in Y×T varying with t would be a stronger repair to test.

This is motivated by the already-paid fact that a SINGLE U works for every irrational s. It additionally asks that the cutoff live in an ordinary finite-type algebraic level neighborhood with base change. A construction only on irrational closed points, or one silently deleting further rational fibres, does not meet this test. There is no assumed flat connection in the level direction; these would be relative D-modules along Y, not absolute D-modules on the product.

A necessary condition is that each fibre admit a quasi-compact categorical cutoff. We compute this condition completely for G=SL_2 and every X, retaining the full category. This is an allowed test case for the full proposed operation, not a restricted substitute for a failed theorem. No claim was frozen before the test.

## 2. Exact stabilizer and determinant character

Choose a point x₀∈X and, for each integer d>max(0,g−1), the line A_d=O_X(dx₀). Give

    E_d=A_d ⊕ A_d⁻¹

the evident determinant trivialization. Since Hom(A_d,A_d⁻¹)=H⁰(A_d⁻²)=0, its determinant-preserving automorphism group consists of upper triangular matrices with diagonal (a,a⁻¹). Thus

    H_d=Aut_SL2(E_d)=G_m ⋉ H⁰(X,A_d²),

where G_m acts on the vector group by a². Riemann–Roch and 2d>2g−2 give dim H⁰(A_d²)=2d+1−g. Nothing here assumes the torus is central in H_d: it is not.

The adjoint bundle, with this torus action, decomposes as

    ad(E_d)=O_X ⊕ A_d² ⊕ A_d⁻²,
    torus weights 0, +2, −2.

The determinant convention is det H⁰ ⊗ (det H¹)⁻¹. Its character is therefore a↦a^m_d, where

    m_d = 2χ(A_d²) − 2χ(A_d⁻²)
        = 2(2d+1−g) − 2(−2d+1−g)
        = 8d.                                      (2.1)

The genus terms cancel exactly. The unipotent radical has no nontrivial algebraic characters, so the whole H_d-character of L|_(BH_d) is this power of a. The constant determinant factor is a fixed one-dimensional vector space and does not change the twist.

This also checks the source's trace-form formula: the standard SL_2 torus cocharacter has adjoint weights 0,±2, hence Q(z,z)=8 and Q(z,dz)=8d. The factor is 8d, not 4d; omitting the negative-root H¹ contribution would give the wrong rational resonance set.

## 3. Necessary AND sufficient resonance on the residual gerbe

The residual gerbe of E_d is BH_d. On the Levi cover BG_m→BH_d the twisting character has weight m_d. This map is smooth surjective, with fibre H_d/G_m isomorphic as a variety to the vector group. We may therefore use central inertia on BG_m and smooth descent, without incorrectly treating G_m as central in H_d.

At exponent s₀ the Laurent de Rham complex for the relevant Kummer factor is, in degrees 0 and 1,

    C[z,z⁻¹] --(z∂_z−m_d s₀)--> C[z,z⁻¹].       (3.1)

The monomial zⁿ has eigenvalue n−m_d s₀. If m_d s₀∉Z, all eigenvalues are invertible. The complex is contractible, with coefficientwise inverse on the second term. The constant-factor version has cohomology C in degrees 0 and 1. The strong equivariance identity of foundations:inertia therefore forces every twisted object on BG_m to vanish, even unbounded ones; tensoring with C⊕C[−1] detects zero. Smooth descent gives

    D(BH_d,L^s₀)=0 if 8d s₀∉Z.                  (3.2)

Conversely, if k=8d s₀∈Z, the character a↦a^k is an honest algebraic character of H_d. Let K_k be its line on BH_d. Its infinitesimal twisting class equals s₀ times the class of L: dlog(a^k)=s₀ dlog(a^(8d)). This is equality of the equivariant twisting data on the classifying stack, not an assertion that a fractional power exists as a line on all of Bun. Consequently the local twist is the integral twist of K_k, and tensoring by that actual line identifies D(BH_d) with D(BH_d,L^s₀).

The untwisted dualizing object on BH_d is nonzero, as seen on its smooth point atlas. Its integral transport gives a nonzero twisted object V_d. Thus

    D(BH_d,L^s₀)≠0  iff  8d s₀∈Z.               (3.3)

For rational s₀=p/q in lowest terms, infinitely many arbitrarily large d satisfy this condition: d=qℓ is sufficient. More exactly, the allowed d are multiples of q/gcd(q,8). This proves actual existence, not just failure of the irrational vanishing argument.

## 4. Extension to the full bundle category and failure of every cutoff

The primary rank-two HN description supplies a locally closed stratum of maximal line degree d. For d>g−1 its extension classes split, since H¹(A_d²)=0; the Picard parameter can still vary. Fixing the class of A_d in Pic^d yields its residual gerbe BH_d as a locally closed substack of Y. The maximal positive line is unique. In particular one must not replace this entire stratum by a single point when g>0.

Let i_d:BH_d→Y be that locally closed immersion. Factor it into a closed immersion in an open substack followed by the open immersion. Chartwise Kashiwara, open star extension and smooth descent give a fully faithful twisted star image. Equivalently, the base-change identity i_d^! i_(d,*)≃Id detects the resulting object's nonvanishing. Define

    M_d=i_(d,*)V_d ∈ D(Y,L^s₀).                  (4.1)

All twisting data on BH_d are the restrictions of the given L^s₀, so there is no gluing of incompatible twists here. The pushforward is along a schematic quasi-compact locally closed immersion; it is not an unsafe arbitrary stack pushforward. The construction exists for the full category. It uses no unproved compactness of V_d or M_d.

Every quasi-compact open U⊂Y is contained in an HN open of bounded maximal line degree N. This follows already from the increasing open HN exhaustion and quasi-compactness. Choose resonant d>N. Then BH_d×_Y U is empty. Open base change for star image gives

    M_d|_U=0,     but     i_d^!M_d=V_d≠0.        (4.2)

Thus restriction to U is not conservative, and cannot be an equivalence. No assumption about the set-theoretic closure of the underlying D-module support is needed: the empty fibre product proves the restriction calculation.

We have established the precise necessary-condition failure:

    For EVERY rational s₀, EVERY smooth projective connected X,
    and EVERY quasi-compact U⊂Bun_SL2(X), restriction of the full
    L^s₀-twisted category to U has a nonzero kernel.             (4.3)

The source proves the complementary irrational cutoff statement. This rational obstruction is a classical residual-gerbe/character calculation combined with its HN geometry, not a proposed substantial discovery.

## 5. Parameter, normalization, and global-form checks

Every nonempty Zariski open of A¹_C omits only finitely many closed points and contains rational exponents. Equation (4.3) therefore disproves the finite-type neighborhood test in §1. Allowing U to vary in a quasi-compact open W⊂Y×T does not repair it: the geometric fibre W_t is quasi-compact (the fibre is closed over a complex point), and (4.3) applies at a rational point t. Even an independently chosen finite bound in each rational fibre is insufficient.

A finite étale surjective parameter cover still has points over every rational exponent in T, with complex residue fields. A nonconstant map from an integral algebraic curve to the level line has image containing a nonempty open; hence it meets rational exponents as well. Neither repair changes the determinant character in those fibres. A finite constructible stratification likewise cannot manufacture a cutoff in a rational fibre. These failures concern the tested cutoff, not the existence of any conceivable quantum Langlands correspondence at those levels.

Integral determinant transport sends s₀ to s₀+n and multiplies the twisting character by a^(8dn), an honest integral character. Condition 8d s₀∈Z is invariant. For SL_2, h∨=2. In the theorem convention s₀=(c−2)/4, resonance is

    8d s₀=2d(c−2)∈Z  iff  2dc∈Z.              (5.1)

In the working convention (c+2)/4 the difference is 8d and the same condition holds. Thus this is not a sign/shift artifact. The rational-to-irrational boundary is unchanged by the affine change of parameter or by the dual map c↦−1/c away from zero.

The chosen group is the actual simply connected SL_2 in the source's permitted class. It has only the zero bundle component. Its finite central μ₂ acts trivially on L; the resonant line K_k can have a nontrivial μ₂ character, which is permitted because the FULL category retains every central sector. If a particular central sector were imposed, one could choose d in a further fixed multiple so k is even; that observation is not used as a restricted replacement. There is no passage to PGL_2 and no assertion matching rational HN strata across Langlands duality.

## 6. The universal coefficient calculation: where the obstruction sits

The fixed-weight calculation can be done before choosing a scalar. Over A=C[s], for m≠0, the relative Laurent complex is

    K_m = [ A[z,z⁻¹] --(z∂_z−ms)--> A[z,z⁻¹] ]
        = direct_sum_(n∈Z) [ A --(n−ms)--> A ]. (6.1)

Each n−ms is a nonzero divisor, so

    H⁰(K_m)=0,
    H¹(K_m)=direct_sum_(n∈Z) A/(n−ms).          (6.2)

At s₀ with ms₀∉Z, the derived fibre vanishes. If ms₀=n₀∈Z, exactly one summand has zero differential after specialization, and its fibre has one-dimensional cohomology in each of degrees 0 and 1. The degree-zero class is the Tor₁ of A/(n₀−ms) with C_(s₀); it is not visible by taking the ordinary fibre of H⁰(K_m)=0. The whole two-term complex is A-flat termwise, so derived base change is computed by its displayed differential without a hidden derived-limit operation.

Although each monomial summand is a perfect two-term complex, the total H¹ is not a finitely generated A-module: it has infinitely many distinct point supports. In particular generic vanishing of this universal Laurent calculation cannot be upgraded by the usual finite/coherent generic-freeness argument to vanishing on a nonempty Zariski level open. Even one fixed m has infinitely many additive resonances n/m.

On the multiplicative monodromy line the corresponding finite topological calculation is

    [ C[q,q⁻¹] --(q^m−1)--> C[q,q⁻¹] ].        (6.3)

For m=8d it has the finite resonance set q^(8d)=1. As d ranges over arbitrarily large integers, the union is ALL roots of unity: any order N divides 8d for arbitrarily large d. Consequently deleting finitely many monodromy values does not kill all unstable tails either. Under q=exp(2πis), (6.3) has exactly the scalar resonance criterion of (6.1), but it is not an algebraic base change of C[q,q⁻¹]-complexes to C[s]. The map q↦exp(2πis) is transcendental. This is consistent with the source's explicit use of Fourier and Riemann–Hilbert after field specialization and its carefully finite q-diagrams.

The comparison identifies a concrete interface, rather than claiming that the source has no deformation: it DOES have the mixed-origin q-calculus and logarithm transition argument. Those operations do not remove the actual rational objects (4.1), and they do not state finite presentation of the universal additive-level Laurent cohomology (6.2).

## 7. Strongest repairs that really work at the cutoff step

It would be incorrect to infer a general impossibility of level-relative cutoff, or of coherent relative quantum Langlands, from §5.

First put

    R=C[s][ (s−r)⁻¹ : r∈Q ].                   (7.1)

Every n−ms, m≠0, is a unit in R. The coefficientwise homotopy dividing the second term of (6.1) by n−ms therefore contracts K_m⊗_A R. The same homotopy works after every R-algebra base change. The constant torus complex still contains the coefficient ring as a direct summand, so the source's inertia argument works at this local relative step, for unbounded coefficient complexes too.

R is a localization of the PID C[s], hence is Noetherian; its failure is NOT non-Noetherianity. It is not finitely generated as a C-algebra. Indeed finitely many generators as rational functions would have poles at only finitely many rational points, while R contains (s−r)⁻¹ for every rational r. It admits every irrational complex evaluation and the generic point, and no rational complex evaluation. Thus infinite localization supplies exactly the units missing from finite-type algebraic spreading. We do not promote this local calculation to a construction of the whole relative global equivalence.

Second let B be any local Artinian C-algebra, ε∈B nilpotent with ε^(N+1)=0, and s=s₀+ε with s₀ irrational. For every n and nonzero integer m,

    (n−m(s₀+ε))⁻¹
       = sum_(j=0)^N (mε)^j / (n−ms₀)^(j+1).  (7.2)

This finite identity contracts the relative Kummer complex over B. For the completed coefficient ring C[[t]], the corresponding formal geometric series supplies a t-adic inverse. There is no claim of analytic norm convergence uniform in n,m, nor any interchange of a nonproper pushforward with a limit. At the local inertia step, arbitrary infinitesimal order causes no new obstruction. Conversely, these units cannot all descend to one finitely generated localization of C[s], by §6–7. Pointwise/formal success and failure of algebraic spreading are compatible.

Third, truncating the problem to bounded HN types or finitely many q-diagrams only creates a finite resonance list on the q-line. That is precisely the finite regime already controlled by the source's rank lemma. Its logarithm-colimit proof additionally kills completed generators by later transitions and transfers the zero transition ranks to every nontorsion q. Rephrasing that step as a new uniformity theorem would duplicate an actual paid proof operation. None of these repairs gives the original finite-type/all-fibres cutoff, and none is nominated as a new theorem.

The parameter repair also survives the actual Langlands inverse, so that inverse is not itself an additional obstruction. In shifted coordinates put R_c=C[c,(c−a)⁻¹ : a∈Q]. For the lacing number ℓ, the substitution σ(c)=−1/(ℓc) sends

    σ((c−a)⁻¹)=−ℓc/(1+ℓac).

For a=0 this is −ℓc, and for a≠0 its only denominator zero is the rational point −1/(ℓa). Thus σ is an automorphism of R_c, with σ²=Id; the rational affine conversions between s and c also preserve the corresponding localization rings. At a formal irrational point c₀, the inverse has expansion −1/(ℓc₀)+t/(ℓc₀²)−t²/(ℓc₀³)+⋯, with irrational constant term. The two sides therefore have simultaneous invertible inertia eigenvalues. This closes the base-ring and local dual-level compatibility test. It supplies neither the relative localization functor nor its Whittaker comparison.

One can also extract the exact elementary logarithm length already implicit in the source. If a completed stalk module has finitely many homogeneous pro-generators of weights w₁,…,w_k and its stage cohomologies have the common upper weight bound C, then

    a=max(1, floor((C−min_j w_j)/2)+1)

satisfies C−2a<w_j for every generator. A common later transition killing their length-a images kills the entire completed module, by strictness. Finite rank constancy transfers that zero map to every nontorsion q. The existence of that transition follows from the finite-length colimit vanishing and the finite generator set; this formula does not estimate its pole bound, and it does not claim a uniform generator-weight lower bound over all stages. This quantitative extraction is already contained in the read proof of deform:colimit and is not a fresh operation.

For topology, a complex neighborhood of a nonreal s₀ can avoid Q, whereas every complex neighborhood of a real irrational s₀ meets Q. This elementary distinction does not assert analytic relative functoriality in the former case or disprove it on an appropriate non-finite-type parameter object in the latter.

## 8. What is closed, and what remains unpaid

The proposed finite-type spreading operation has failed a complete necessary-condition test, not merely a naive proof attempt. The failure is exhibited by explicit objects at arbitrarily unstable rational resonances, with the exact determinant exponent, stabilizer, integral untwisting, extension, base-change and normalization interfaces checked. The universal coefficient complexes locate the lost classes and explain why finite presentation and algebraic exponentiation cannot be assumed. The strongest local repairs—ordinary rational-point localization and formal unit inverses—were carried through explicitly.

These computations combine classical primary HN/contraction/extension operations with the source's own inertia mechanism. They are retained as prefreeze feasibility work, not offered for a substantial-contribution verdict or counted. There is no viable exact theorem to freeze and no full positive author-proof nominee.

The possible broader goal of an R-linear, or otherwise precisely based, quantum Langlands equivalence is still unpaid here. In particular no relative algebraization of the finite q-diagrams, their transition system, the localization quotients and the specified comparison maps has been constructed over (7.1). Even a relative cutoff would not supply those operations. This is an explicit limit of the completed calculation, not a newly nominated conjecture, not a claim that the source's pointwise construction fails, and not a claim that no other substantial operation in Source069 exists. No additional family was scanned. All archived scopes remain immutable.
