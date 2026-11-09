# Stabilized tensor growth and its missing global comparison

Status: **PREFREEZE / no nominee**. These are author feasibility calculations, not an independent mathematical verdict. No candidate theorem was frozen, changed or weakened. The nonroutine global comparison in §7 was not proved; the completed local calculations are credited to compatible source/primary operations. They are retained to make the attempted operation concrete, not to count a restricted substitute.

## 1. Exact inputs and conventions

Let k be an algebraically closed field of characteristic p>0, r≥1, q=p^r, s=p^(r−1), and E=(C_p)^r. Fix an ordered basis g_1,…,g_r of E and a faithful additive embedding λ:E→(k,+). Equivalently its parameters λ_i are linearly independent over F_p. All tensor products of E-modules below use the **group** coproduct g↦g⊗g, not the primitive coproduct on a truncated polynomial algebra. All modules are finite dimensional.

Let R_λ be restriction from SL_2 along this embedding into its unipotent subgroup, let T_i denote its indecomposable tilting module of highest weight i, and put S=R_λ(T_(s−1)). Write core(Y) for the direct sum of the nonprojective indecomposable summands of Y. Krull–Schmidt makes its isomorphism class well defined. For any Y write

    γ_E(Y) = lim_n dim core(Y^⊗n)^(1/n).

Existence of this limit is the submultiplicative argument in Benson–Symonds, 1902.02895v2, Theorem4.4. Zero is allowed.

The pinned family208 manuscript is *Fiber functors for finite symmetric tensor categories in positive characteristic*, at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. The following operations are stipulated true and were read at their operative bodies:

- `restricted.tex`, `thm:restricted-tilting`: S⊗Y is a restricted tilting module for every Y. Its proof passes through bounded polynomial lifts, equivariant bundle extension, tilting at the origin and a formal comparison with exact cancellation of the torus reparameterization.
- `higher.tex`, equation `eq:theta` and `lem:theta-detection`: the additive strong symmetric monoidal functor Θ_λ:Rep(E)→Ver_q kills projectives and agrees with the tilting quotient. This functor is not asserted exact on Rep(E).
- `support.tex`, `lem:steinberg-support`, `lem:moore-selection` and `prop:support-selection`: S has one-point rank support, and every support point with F_p-independent coordinates can be reached by such a Steinberg module. The source supplies actual compatible embeddings, not just a numerical support condition.

The necessary primary interfaces are stronger than these headlines. Coulembier–Flake, 2405.19506v2, Theorem5.3.5 and its proof identify the restricted indecomposables and the quotient on morphisms; Lemma5.4.5 and its proof turn the source's S⊗Y assertion into closure of the whole S-generated object ideal. Their Lemma5.4.6 and Theorem5.4.3 construct the monoidal extension using an actual cokernel presentation. Their later 2610.04096v1, Theorem3.20, supplies the explicit iterated-cohomology splitting used in §4. The latter is an external primary input, separately acquired/read, not a newer upstream dependency or an upstream truth audit.

Benson–Etingof–Ostrik, 2003.10499v4, Theorems4.2 and4.5, identify the surviving tilting category and its positive Frobenius–Perron dimension. Write f(Y)=FPdim(Θ_λ(Y)). It is additive on direct sums, multiplicative on tensor products, and strictly positive on a nonzero target object. It need not respect short exact sequences of E-modules, because Θ_λ need not be exact.

## 2. The finite object ideal really is closed under arbitrary tensor factors

The S-generated object ideal consists of sums of the restricted T_i for s−1≤i≤q−1. Its nonprojective indecomposables are

    U_i=R_λ(T_i),       s−1≤i≤q−2.

There are m=q−s of them. The final object R_λ(T_(q−1)) is the regular projective kE. These statements include r=1 and p=2. They are not consequences of mere point support; there are many other modules with one-point support.

Here is the compatibility argument, retaining the strongest known reduction. Each tilting T_i in the relevant ideal is a summand of T_(s−1)⊗T′. Since S is self-dual, the triangular identities give S as a summand of S⊗S⊗S. Thus T_i is a summand of S⊗S⊗T″ for another restricted tilting T″. For an arbitrary Y, the source makes S⊗Y a restricted tilting. Consequently T_i⊗Y is a summand of S⊗T″⊗(S⊗Y), hence stays in the same tilting ideal. Restricted tiltings remain closed under summands by the primary indecomposable classification. Projective factors stay projective. This is precisely the compatible proof of CF Lemma5.4.5, not a newly unpaid closure step.

For each Y define the nonnegative integral matrix A_Y, with columns indexed by i and rows by j, through

    core(U_i⊗Y) ≅ ⊕_j U_j^(A_Y[j,i]).

Krull–Schmidt and tensor exactness give A_(Y⊕Z)=A_Y+A_Z, A_(Y⊗Z)=A_Y A_Z, and A_k=I. The matrices commute. This conclusion uses an object ideal; it does not require lifting arbitrary E-module homomorphisms to SL_2 homomorphisms.

Set d_i=dim_k U_i and f_i=FPdim Θ_λ(U_i)>0. Projectives vanish under Θ_λ, so its monoidal structure gives the exact positive left-eigenvector identity

    f^t A_Y = f(Y) f^t.

All the d_i and f_i depend only on p,r and the tilting label, not on λ. Define explicit finite constants

    a_(p,r)=min_(s−1≤i≤q−2) d_i/f_i,
    b_(p,r)=max_(s−1≤i≤q−2) d_i/f_i.

They are finite and strictly positive. Their expression in terms of a finite prescribed tilting list is intentional; no claim of an efficient all-p,r numerical algorithm is needed.

## 3. Exact stabilized recurrence, generating series and growth

Let e be the unit coordinate vector for U_(s−1)=S. For every n≥0,

    c_n^λ(Y):=dim core(S⊗Y^⊗n)=d^t A_Y^n e.                 (1)

Indeed the identity holds at n=0, and tensoring the decomposition once more by Y propagates it; discarded projectives can never produce nonprojective summands. Ordinary matrix algebra therefore gives the identity of formal rational series

    Σ_(n≥0)c_n^λ(Y)t^n = d^t (I−tA_Y)^(-1)e.               (2)

The denominator det(I−tA_Y) has degree at most q−s and constant term1. Cayley–Hamilton supplies a linear recurrence of order at most q−s, valid for every n≥0 in its usual characteristic-polynomial form. There is no uniform assertion that this order is minimal.

The positive eigenvector gives a stronger, elementary conclusion than a generic spectral-radius limsup:

    a_(p,r) f(S) f(Y)^n ≤ c_n^λ(Y)
                            ≤ b_(p,r) f(S) f(Y)^n.         (3)

For n=0 interpret f(Y)^0 as1. For n≥1 the formula also covers f(Y)=0: the positive f_i force A_Y=0, so c_n=0. If f(Y)>0, taking nth roots in (3) proves

    lim_n c_n^λ(Y)^(1/n)=f(Y).                              (4)

This calculation rules out an extra polynomial factor in this stabilized sequence; even periodic transition matrices satisfy the two-sided bound. It does not require primitivity of A_Y.

The same comparison on the finite ideal, starting with the decomposition of S⊗Y, gives

    γ_E(S⊗Y)=f(S)f(Y).                                     (5)

When S⊗Y is projective both sides are zero; otherwise all positive-weight comparisons apply to its tensor powers. Thus the completed scope includes **every** finite E-module Y, every faithful λ and every p,r, while retaining the stabilizing S. It does not prove γ_E(Y)=f(Y).

For Y_1,…,Y_l and any nonnegative exponents n_1,…,n_l, the corresponding formula is d^t A_(Y_1)^n_1⋯A_(Y_l)^n_l e, with positive weight f(S)∏f(Y_j)^n_j. Its multivariate series is

    d^t ∏_(j=1)^l (I−t_j A_(Y_j))^(-1)e.

These are finite-matrix consequences of the already proved ideal closure. Benson–Symonds Sections9–11 and Benson2008.13155v2 Sections3.2–3.3 give the stronger surrounding spectral framework. Neither the recurrence nor its length is nominated as a substantial operation.

## 4. An explicit local rate from iterated generalized cohomology

This part uses the full actual splitting theorem of CF2610.04096v1, not a guessed natural decomposition. Let

    A_r=k[z_0,…,z_(r−1)]/(z_0^p,…,z_(r−1)^p).

There is an algebra isomorphism φ_λ:kE→A_r given, on e∈E, by

    φ_λ(e)=∏_(j=0)^(r−1) exp(λ(e)^(p^j) z_j),
    exp(u)=Σ_(b=0)^(p−1)u^b/b!.

Its matrix is a Vandermonde evaluation matrix at the q distinct elements λ(e), in the divided monomial basis. This proves invertibility directly. It is **not** being used as a Hopf isomorphism to a primitively generated algebra. Set c_j=φ_λ^(-1)(z_j).

For a p-nilpotent endomorphism d put

    B_j(d;M)=(ker d ∩ im d^(j−1))/(ker d ∩ im d^j),  1≤j≤p.

Operators commuting with d descend to these subquotients. For a=Σa_j p^j, 0≤a<q, define

    H_Y^λ(a)=B_(a_0+1)(c_0; … B_(a_(r−1)+1)(c_(r−1);Y)…),
    h_a=dim_k H_Y^λ(a).

Iterated ordinary Jordan counting gives

    dim Y = Σ_(0≤a<q) h_a ∏_j(a_j+1).                     (6)

For r=1 this is ordinary Jordan decomposition (S=k); the restricted L(a), 0≤a<p, are the single Jordan blocks. For general r the primary's Theorem3.20 identifies S⊗Y with the direct sum of h_a copies of S⊗R_λ(L(a)), where L(a) is the simple SL_2-module of highest weight a. The source already makes every S⊗R_λ(L(a)) tilting. The primary proof is substantive: it retains the higher carry operator, corrects a filtered retraction to intertwine both remaining operators, and then applies Nakayama. We credit that operation in full. The resulting splitting is not claimed natural in Y; naturality is unnecessary for the dimension formula.

Set θ=π/q and define the explicit real algebraic integers

    w_a=∏_(j=0)^(r−1) sin((a_j+1)p^j θ)/sin(p^j θ).

Every denominator is positive. All weights are nonnegative; w_a=0 exactly when a_(r−1)=p−1. For a lower digit, (a_j+1)p^j θ≤π/p<π; for the top digit the numerator reaches π exactly in the zero case. Each factor is a finite Laurent character sum evaluated at a root of unity, so it is an algebraic integer and at most a_j+1 in absolute value.

The character evaluation in BEO Theorem4.5 sends T_1 to 2cosθ and any tilting character to its value at exp(iθ). Tilting characters form a triangular integral basis of the SL_2 character ring. Steinberg's tensor product formula gives χ_(L(a)) as the product of the digit characters above. Since S⊗L(a) is tilting and

    f(S)=sin(sθ)/sinθ=sin(π/p)/sin(π/q)>0,

taking FP dimensions of the primary splitting and cancelling f(S) gives

    f(Y)=β_λ(Y):=Σ_(0≤a<q) h_a w_a.                       (7)

This also proves directly 0≤β_λ(Y)≤dimY by (6). Since Θ kills projectives, the stronger bound is

    0≤β_λ(Y)≤dim core(Y).                                 (8)

The monoidal functor, not an illicit primitive coproduct, proves that β_λ is additive on sums and multiplicative on tensor products. Thus β_λ is a positive core-bounded species of the stable Green ring. Applying (8) to Y^⊗n and taking nth roots yields β_λ(Y)≤γ_E(Y).

## 5. Finitely many constructible local values; no hidden limit interchange

Fix p,r and a particular D-dimensional module Y, with its action matrices. The faithful embeddings form the nonempty Moore-determinant open set in A^r_k. On it, each c_j acts by a matrix whose entries are regular rational functions of λ: use the inverse of the q×q Vandermonde matrix above. The iterated subquotients H are obtained by kernels, images, intersections and quotients of these commuting matrices.

For completeness, these dimensions are constructible without assuming any splitting is natural. Stratify by the ranks of the finitely many relevant matrices; on a chart where chosen maximal minors are nonzero, Gaussian elimination provides bases for kernels and images with rational entries. Intersections are kernels of the maps to the respective quotient, and induced operators on subquotients are again matrices with rational entries. Refining into finitely many rank/minor charts at each of r finite steps gives a finite constructible stratification on which every h_a is constant. No infinite stratification is used.

Equation(6) bounds every h_a by D, so at most (D+1)^q arrays can occur. Consequently β_λ(Y) takes a finite set of real algebraic-integer values, with an attained maximum. This bound is only a coarse finite bound, not a contribution claim. Nonempty constructible strata over an algebraically closed k have k-points, so allowing an algebraically closed scalar extension cannot add a new array for this fixed module.

For a nontrivial elementary abelian E and arbitrary Y define

    b_E(Y)=max_(1≠H≤E, λ faithful additive embedding of H) β_λ(Y|_H).     (9)

There are finitely many subgroups, and §5 makes this an attained maximum over a finite set of values. Restricting a projective E-module gives a projective H-module, so the core norm cannot increase. Therefore

    0≤b_E(Y)≤γ_E(Y).

Moreover b_E(Y)=0 exactly when Y is projective. To prove the nontrivial direction, choose a subgroup H of minimal positive rank on which Y is nonprojective. Its restrictions to proper subgroups are projective. The source's independent-support and Moore-selection lemmas supply λ with S_λ⊗Y|_H nonprojective. The positive tilting list then makes β_λ(Y|_H)>0. In fact that value is at least1, as it is the FP dimension of a nonzero object.

For fixed Y, each local β is multiplicative, hence b_E(Y^⊗n)=b_E(Y)^n. Equations(3) and(9) show that the maximum of all the stabilized core dimensions also has nth-root limit b_E(Y), with comparison constants depending only on p and rank(E). There is **no remaining exchange-of-supremum-and-limit problem** here. The finite arrays and uniform finite-list constants pay that issue.

## 6. An explicit test against a too-strong norm comparison

The hoped-for estimate cannot be a bound dim core(Z)≤C_E b_E(Z) uniform over all finite modules Z. Let r≥2, q=p^r, and let Ω^m k be the projective-free mth syzygy of k. The minimal resolution for k over kE is the tensor product of the one-generator resolutions alternating multiplication by x and x^(p−1). All differentials lie in the radical. Its degree-m free rank is

    β_m=binom(m+r−1,r−1).

Exactness follows by tensoring the augmented resolutions over the field; minimality follows from the radical condition. If d_m=dim Ω^m k and d_0=1, then

    d_(m+1)+d_m=q binom(m+r−1,r−1),
    Σ_(m≥0)d_m t^m=(1+q t/(1−t)^r)/(1+t).                 (10)

In particular r=2 gives d_(2u)=qu+1 and d_(2u+1)=q(u+1)−1. These dimensions are unbounded. The projective-free assertion follows from minimality and self-injectivity: a projective summand in a syzygy inside a radical would split in the ambient free module, contradicting that a nonzero direct free summand cannot lie in its radical.

In the stable category Ωk is tensor-invertible, with inverse Ω^(-1)k. Tensoring a projective presentation by a module and Schanuel's lemma give (Ωk)^⊗m≅Ω^m k stably. Restriction to any nontrivial H preserves this stable statement. Applying Θ_λ, which kills projectives, sends these stable inverse objects to inverse objects in Ver_(|H|). Invertible objects have FP dimension1. Thus

    β_λ((Ω^m_E k)|_H)=1,       b_E(Ω^m_E k)=1.

This disproves only the uniform linear norm comparison. It does not disprove the global exponential-rate equality in §7: (10) gives γ_E(Ωk)=1. For tensor powers of a fixed module, a polynomial or other subexponential loss could still be harmless. The example and its growth phenomenon are classical; Benson–Symonds Lemma9.13 and Benson's later Section5.9 already discuss the corresponding species behavior.

## 7. Exact unpaid operation and strongest integrated comparison

The nonroutine operation sought in this round would establish, for every algebraically closed k of characteristic p, every r≥1 and every finite k(C_p)^r-module Y,

    γ_E(Y) = b_E(Y).                                      (U)

No proof-feasible full candidate for (U) emerged, so it was never frozen. All quantifiers above are retained; (1)–(9) are not substituted for (U). We do not assert that (U) is false, globally open, or a new-to-literature formulation.

The remaining obligation is the upper inequality γ_E(Y)≤b_E(Y). One concrete sufficient estimate would be, for each fixed Y, subexponential numbers C_n with lim C_n^(1/n)=1 such that

    dim core_E(Y^⊗n) ≤ C_n max_(H,λ) dim core_H(S_λ⊗(Y|_H)^⊗n),     n≥1. (N)

The local transition matrices and cohomology strata do not supply (N). They describe the result after multiplication by S_λ, whose object ideal loses other extension information. The syzygy calculation shows why a constant independent of Y cannot simply be inserted. It leaves (N) for a fixed Y unresolved.

We tested the strongest located spectral alternative as well. Benson–Symonds Theorem9.16, with its actual Banach-algebra proof chain, and Benson2008.13155v2 Theorem3.3.7 express γ as the maximum modulus over **all** core-bounded species. Equation(7) constructs a particular positive family. It does not classify all such species or prove pointwise domination on every module by that family. Even in the Klein-four primary example there are continuous syzygy-phase species and discrete families beyond the displayed positive choice. Their existence alone does not refute domination on positive modules; it prevents treating the set of constructed species as the entire spectrum without proof.

Carlson's comparison, as stated in both these primary books/papers and used in their displayed proofs, already pays reduction from a finite group to its elementary abelian subgroups. For G=E, that maximum includes E itself. It is not a further comparison with the nonexact Θ functors. The original1981 Carlson body was not acquired: a bounded DOI attempt failed. We therefore claim neither a fresh read of that proof nor an absence result about stronger classical operations elsewhere.

The full refined splitting, finite ideal, positive FP dimension and ordinary matrix/rank arguments pay every completed local calculation here. What is missing is a new **closed** norm/spectral comparison, not a longer proof of those paid operations. No substantial-result review is requested, and no independent correctness, contribution, acceptance or count is assigned.

## 8. Bounded exact support calculation

`growth_check.py` uses only the Python standard library and GF(4), with w²=w+1, for E=C_2² and λ=(1,w). It computes actual group tensor actions and removes free summands by the rank of (g_1−1)(g_2−1). For this local Frobenius algebra the rank of its socle norm counts regular summands: a vector with nonzero socle image generates an embedded regular module, which splits by self-injectivity; induction leaves zero norm on the remainder.

The two stable basis objects are S and S², of dimensions2 and4. For X=S the matrix is [[0,2],[1,0]] and the stabilized core dimensions through n=6 are2,4,4,8,8,16,16. For X=V_(1,w²) every positive-n value is0. For X=Ωk they are all2. For X=k⊕S the matrix is I+A_S and the values through n=4 are2,6,14,34,82. Independent interpolation of c_0,c_1 and the two successive generalized-cohomology ranks gives respective rates √2,0,1,1+√2. The largest matrix has dimension162. These checks test the group coproduct and the normalization; they do not prove (U), the general source operations, or a contribution gate.
