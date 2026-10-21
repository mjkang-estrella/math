# r142 — integrated relative descent and two-system calculations

Research notes, PREFREEZE. No theorem is nominated or frozen. These are deductions and feasibility calculations after complete operative reading of both SOURCE041 manuscripts at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, followed by the primary and original-history reading recorded privately. All stipulated source proofs are used as true. No mathematical self-grade or novelty claim is made.

## 1. Exact paid input and the normalization that must precede descent

Write q(x,y) for the integral BBF bilinear form, q(x)=q(x,x), and dim X=2n. The strong SYZ source applies to an actual holomorphic line bundle with nonzero nef isotropic c1 on a compact IHS Kähler manifold. It gives semiampleness on that manifold. It does not give a uniform exponent for arbitrary data or address an irrational nef real class. The companion identifies the normal projective base of a projective Lagrangian fibration with P^n; it is not, by its headline alone, a theorem for arbitrary analytic targets or relative bases.

The calculation below first restricts its setting to a smooth projective family π:X→S over a connected smooth complex algebraic variety. Every geometric fiber is an IHS manifold of dimension 2n. An actual L∈Pic(X) restricts to a nonzero nef isotropic class on every fiber. Write c1(L_s)=d e_s with e_s primitive integral and d>0. Torsion-freeness of H² and local constancy of the integral lattice make d constant and the positive primitive roots e_s monodromy invariant. This is integral divisibility of the vector, not the BBF divisibility div(e)=gcd q(e,H²).

On one fiber source SYZ supplies f_s:X_s→B_s; projectivity permits the companion, hence B_s=P^n. Kim–Oguiso–Shinder (KOS), arXiv:2608.10102v1, Theorem 3.4 and Remark 3.5, supply no codimension-one multiple fibers and primitivity of f_s^*O(1). The currently corrected Kamenova–Verbitsky paper, arXiv:1612.07378v4, Theorem 3.2, requires the former condition. Its abstract landing page omits that condition, whereas the actual PDF states it. The actual KOS proof already combines cyclic roots, locally free higher images, Horrocks splitting and the Beilinson norm; thus primitivity is not a new deduction to nominate here.

In detail, if L_s^m=f_s^*O(a), then m d e_s=a v_s with v_s=c1(f_s^*O(1)) primitive. Since both vectors have the same positive rational ray, e_s=v_s and a=md. The exponential sequence and H¹(O_Xs)=0 make c1 injective on Pic(X_s). Consequently

    L_s ≅ f_s^*O(d),   h⁰(X_s,L_s^k)=binom(n+dk,n), k≥0.

In particular L_s itself is generated; the primitive root has n+1 sections. This exponent-one statement in the projective case is a paid SYZ/base/primitivity composition, not a nominee. The primitive morphism has connected fibers. The morphism given by L_s is its d-Veronese embedding, not a different Stein base.

The strongest source mechanisms used below include companion Proposition def:fixed-base (the entire nearby e-Hodge locus, not just a curve), and Proposition secsys:second-system (two nef null classes on the SAME nearby projective model with the WHOLE positive span Kähler). Its proof uses actual parallel transport, null rotations, a loxodromic element and wall avoidance. The finite smooth abelian cover of the first base is already paid. We do not replace any of these by a weaker birational assertion.

## 2. The relative construction with an actual primitive bundle

Suppose first d=1, so that L itself is the primitive bundle on every fiber. Set V=π_*L. Its fiber dimension is n+1. Algebraic cohomology and base change, or the actual Matsushita deformation proof locally on the pair-deformation space, gives a vector bundle V and its fiber identifications. The evaluation π^*V→L is surjective: its cokernel vanishes on every fiber, so Nakayama eliminates it. With quotient convention P_S(V)=Proj Sym(V), evaluation gives

    f:X→P_S(V),   L=f^*O(1).

On each fiber this is the connected Lagrangian contraction onto the entire P^n. Properness then gives surjectivity globally. The same argument applies to every positive power: π_*L^k is locally free of rank binom(n+k,n), and

    Sym^k(V) → π_*L^k

is an isomorphism because it is one on every fiber and both sides are vector bundles of equal rank. These isomorphisms are the actual multiplication maps; they respect the graded algebra structure. Thus

    ⊕_{k≥0} π_*L^k ≅ Sym(V).

For precision, constant h⁰ can be used over the smooth reduced S as follows. Locally the derived direct image is computed by a finite free complex in nonnegative degrees. The degree-zero differential has constant rank because h⁰ is constant. Its kernel is therefore a subbundle and commutes with base change. Alternatively, Matsushita Theorem 1.2 gives local freeness of all higher images for the pulled-back ample bundle and its powers in the local universal pair deformation; its proof establishes base change by reverse induction, and Corollary 1.3 proves evaluation surjectivity. No flat relative Stein target is being assumed in advance.

All these assertions are ordinary relative algebraic geometry applied to the paid fiberwise normalization. They are not a substantial nominee. In particular they do not mean P_S(V) is S×P^n: V can be nontrivial.

## 3. General d: the scalar cocycle and its exact annihilators

Locally in the étale topology of S one can choose primitive bundles E_i on X_{S_i} with E_i^d=L, after a possible base-line twist and further local trivialization. One justification is the relative Picard functor: multiplication by d has invertible differential in characteristic zero, and the unique primitive fiber classes give a section of the local root locus. Equivalently the relative root problem is an étale-locally nonempty μ_d gerbe. No arbitrary invariant integral class is being asserted to have a global line bundle.

On overlaps, E_i and E_j differ by a line bundle from the base because their restrictions agree and H¹(X_s,O)=0. Refining covers and trivializing these difference lines gives isomorphisms φ_ij. Their triple products are invertible scalar functions

    φ_ij φ_jk φ_ki = c_ijk id.

Indeed π_*O_X=O_S. Set β=[c_ijk] in H²_et(S,G_m), choosing the sign convention for projectivization consistently. Replacing the φ changes c by a coboundary. The local rank-(n+1) bundles V_i=π_*E_i have the same scalar cocycle. Their projectivizations glue, as do the evaluation maps:

    X → B → S,    B locally ≅P^n_S.

This is a Brauer–Severi scheme with class ±β. The sign is immaterial for vanishing or order. Determinants of the transition matrices show

    (n+1)β=0.

Comparison with the ACTUAL global L gives dβ=0. Hence

    per(β) | gcd(d,n+1).

There is a global relatively ample A on B restricting to O(d), with L=f^*A. Locally this is O(d) on P(V_i); its gluing is exactly the one inherited from L. Equivalently f_*L is that line bundle. Its relative section algebra is the d-Veronese algebra of the locally twisted primitive sections:

    π_*L^k locally = Sym^{dk}(V_i),
    rank π_*L^k=binom(n+dk,n),
    B=Proj_S(⊕_{k≥0}π_*L^k).

The graded pieces and multiplication glue; a choice of a global V_i does not follow. Generation of a Veronese ring in its degree one follows fiberwise and then by Nakayama. This construction produces the actual relative contraction, not just a list of fiberwise bases.

The same annihilator computation is the classical Brauer–Severi operation in Gounelas–Huybrechts, arXiv:2510.20474v2, §1.1, Lemma 1.1 and Remark 1.2: a relative O(d) is equivalent to d times the Brauer class vanishing. Its exact automorphism extension is GL(n+1)/μ_d, and for d=n+1 the relative anticanonical line provides the natural lift. No novelty is attached to rewriting it in the SYZ setting.

If gcd(d,n+1)=1, β=0 and B=P_S(V) for some honest V; a primitive bundle E exists on X. One obtains

    L ≅ E^d ⊗π^*N,  N∈Pic(S).

One must not delete N. The μ_d root obstruction of the specified L can survive even when its G_m Brauer obstruction vanishes. For example, on X_0×P¹, with E_0 a primitive elliptic K3 fiber bundle, L=E_0^d⊠O_P¹(1) has primitive fiber class d e but no actual d-th root: restriction to {x_0}×P¹ would have degree 1/d. This distinction rules out an unjustified global-root statement.

There is also a numerical determinant refinement. For any actual relative line H and integer k, the local perfect complexes Rπ_*(H⊗E_i^k) have scalar weight k. Their determinant has weight kχ(H_s⊗E_s^k), so

    k χ(H_s⊗E_s^k) β=0.

Writing RR_X(q(H)+2k q(H,e)) for that Euler characteristic gives the exact gcd bound with d and n+1. Since the polynomial in k has degree at most n+1 after multiplication by k, its integer-value ideal is generated by its values at 0,1,…,n+1 (Newton finite differences). This is a finite computation, but it is determinant bookkeeping, not a new period-index theorem. It cannot force β=0 in the example below.

## 4. A geometric obstruction, even with the full positive two-system cone

The following explicit construction tests whether the strongest second-system operation can force global neutrality. It shows that neutrality under only the relative hypotheses above is false. This is a feasibility diagnostic, not a new campaign nominee, not a counterexample to either pinned theorem, and not the abstract cyclic-extension diagnostic from r141.

### 4.1 A smooth K3 double cover with two ample-span fibrations

Let Y=P¹_[x:y]×P¹_[z:w] and M=O_Y(2,2). Put

    P(x,y)=x⁴+x²y²+y⁴,
    Q(x,y)=x⁴−x²y²+y⁴,
    F=P(x,y)z⁴+Q(x,y)w⁴ ∈H⁰(Y,M²).

The branch divisor (F=0) is smooth. The polynomials P and Q have no common root: their difference is 2x²y² and neither vanishes at x=0 or y=0. They have simple roots: on y=1, a common zero of t⁴±t²+1 and 4t³±2t would force t=0 or t²=∓1/2, giving value 1 or 3/4. There is no root at infinity. At z=0 or w=0 the other quartic has simple zero, giving a nonzero differential along the first P¹. Where zw≠0 the derivative in the second P¹ direction cannot vanish on F=0 unless P=Q=0. Thus all cases are covered.

Define X_0=Spec_Y(O_Y⊕M^{-1}), multiplication on M^{-2} given by F. This is a finite flat double cover h_0:X_0→Y, smooth by the branch check. The canonical bundle formula gives K_X0=h_0^*(K_Y⊗M)=O. Also

    H¹(O_X0)=H¹(O_Y)⊕H¹(O_Y(−2,−2))=0

by Künneth. It is connected because the nonempty reduced branch divisor prevents F from being a square in the function field. Thus X_0 is a projective K3 surface (the standard smooth K-trivial, h¹=0 characterization).

Projection to either P¹ is a connected genus-one fibration. For a generic point of the first factor, F is a squarefree quartic in [z:w], so the fiber is a connected genus-one double cover; similarly in the other direction outside a proper discriminant. Stein factorization and normality give connected fibers everywhere. Let

    e=c1(h_0^*O(1,0)),  u=c1(h_0^*O(0,1)).

They are nef, nonzero, isotropic, and primitive by the paid primitivity operation (or elliptic K3 primitivity). Their intersections are

    e²=u²=0,   e·u=2.

EVERY a e+b u, a,b>0, is Kähler: it is the pullback of a Kähler class on Y under a finite map. For real a,b this also follows from the ample cone and positivity. Thus this example meets the strong positive-span interface, not merely a nef-and-big approximation. The map (f_0,g_0) is finite flat of degree 2, not the resolution of a Kummer map contracting exceptional curves.

### 4.2 An honest group action and a nonneutral base

On the first P¹ let G=(Z/2)² be generated by

    A=[diag(1,−1)],   B=[[0,1],[1,0]] in PGL₂(C).

The lifts anticommute in GL₂, so their projective images commute. On O(2) their induced lifts commute and have order two, giving a G-linearization. Hence M=O(2,2) is G-linearized; F is invariant under both generators. The action therefore lifts to the double-cover algebra O_Y⊕M^{-1} and to X_0. It preserves both e and u, and acts trivially on the second P¹. No averaging or equivariant deformation theorem is used.

Take

    S=Spec C[s^{±1},t^{±1}],
    T=Spec C[r^{±1},v^{±1}],  s=r², t=v².

This is a finite étale G-torsor, with the first generator changing r's sign and the second v's sign. Diagonal quotients define

    X=(X_0×T)/G → S,
    B_S=(P¹_[x:y]×T)/G → S,
    h:X→B_S×_S P¹_S.

The action on the products is free because its action on T is free. Étale locally the family is X_0×T. Consequently π:X→S is smooth and projective, all its geometric fibers are K3 surfaces, and h is finite flat of degree 2. Projectivity can be checked by descent of the ample G-linearized h_0^*O(2,2). The second fibration has split base P¹_S. The first has Brauer–Severi base B_S.

Its Brauer class is the quaternion (s,t). Here is a direct algebra check. Over C(r,v) use the projective descent cocycle with lifts A and B above. In the invariant matrix algebra, the elements

    i=r B,   j=v A

are invariant under the respective semilinear conjugation actions; they satisfy i²=s, j²=t, ij=−ji and span the descended degree-two algebra. Thus the claimed quaternion is the actual descent class.

This class is nonzero. Over the completion C(t)((s)), C(t)(√t)((s)) is the unramified quadratic extension. Every norm has even s-adic valuation, whereas s has valuation one. Therefore s is not a norm, the cyclic quaternion (t,s), equivalently (s,t), does not split, and neither does it over C(s,t). Hence β≠0 in Br(S). It is represented by an Azumaya algebra already on S because s and t are units and the extension T/S is étale.

There is a global line A_2 on B_S restricting to O(2), and L=f^*A_2 is a global line bundle with c1(L_s)=2e_s. There is no global algebraic line bundle E on X restricting to e_s on every fiber: if it existed, π_*E would have rank 2 and evaluation would identify B_S with P_S(π_*E), contradicting β≠0. Equivalently f_*E would descend a relative O(1) on B_S. The invariant primitive class alone is insufficient even though the entire positive cone between e and u is ample and the second fibration exists globally.

The determinant refinement is compatible with this nonzero class. For the actual second-fibration bundle H with c1(H)=u, K3 Riemann–Roch gives χ(H⊗E^k)=2+2k, so kχ is always even. For the descended ample class 2e+2u it gives χ=10+4k, again retaining the factor 2. These are concrete checks, not a claim that those two tests exhaust all possible determinant inputs.

This construction is algebraic. Analytification on a Stein base need not retain this algebraic Brauer obstruction; no analytic nonsplitting assertion is made. No claim is made about compact or simply connected parameter spaces, nor about all possible equivariant enhancements. Those are different scopes.

### 4.3 Why none of the paid operations erases this obstruction

The source's fixed-base theorem is local on a marked deformation neighborhood. It gives a product after choosing such a neighborhood, which is fully compatible with a globally nontrivial PGL cocycle. The all-module ordinary base-change operation in the companion controls the chosen local complexes, their thickenings and overlaps; it does not replace a scalar projective cocycle by a GL cocycle. In this explicit family all local pieces are already constant, yet their algebraic gluing is nonneutral.

The source's second-system construction is also fully respected by every fiber of this example, and a second fibration is even present on the total family. A finite map to B_S×P¹_S does not produce a section or a relative zero-cycle of degree one on B_S. Over C(s,t), every zero-cycle on the nonsplit conic has even degree. Thus a transfer containing the degree 2 cannot yield an integral splitting at the prime 2. This is an actual geometric realization of the relative obstruction, not a claim about r141's different descent extension.

## 5. Exact two-system transfer and the surviving summand

On a single projective IHS X' supplied by secsys:second-system, normalize the two fibrations by their primitive pullback classes v and w. Positive rescaling does not change the source's ample-span assertion. Their bases are P^n. Then

    h=(f,g):X'→P^n×P^n=Y

is finite: a positive-dimensional fiber would contain a curve on which the ample divisor v+w has degree zero. Its image is all Y since it is closed of dimension 2n. It is flat by the equal-dimensional Cohen–Macaulay-to-regular finite flatness criterion. If the Fujiki normalization is ∫x^{2n}=c_X q(x)^n, coefficient comparison gives the exact integer

    D=deg(h)=∫v^n w^n
     = c_X 2^n q(v,w)^n / binom(2n,n).

No unrecorded factorial or BBF-divisibility replacement is allowed. For n=1 above c_X=1, q(v,w)=2 and D=2.

For Chow correspondences let T=h^*h_* on X' (equivalently the composition of the graph and its transpose). Flat pullback and proper pushforward give h_*h^*=D id on Y; consequently

    T²=D T,
    R=DΔ_X'−T satisfies R²=D R,
    P=T/D,   E=Δ_X'−P

are complementary idempotents after inverting D. This is an ACTUAL correspondence calculation, stable under field extension, not just an equality on rational cohomology. Expanding the diagonal of P^n×P^n gives explicitly

    T= Σ_{a=0}^n Σ_{b=0}^n
       (v^{n−a}w^{n−b}) × (v^a w^b)

with the convention that a product α×β acts by z↦(∫zα)β. Intersections pairing these monomials are D on complementary bidegrees and zero otherwise, since v^{n+1}=w^{n+1}=0. Thus this is the Tate summand produced by the two fibrations, with its denominator displayed.

The complementary E cannot be killed by any nonzero integer as a correspondence: Y has H^{2,0}=0, so h_* is zero on H^{2,0}(X'), P acts as zero there and E acts as identity. A torsion correspondence has zero action on complex cohomology. This is a direct obstruction only to applying a torsion-complement argument to THIS projector. It is not an impossibility theorem for other motives or cycle constructions.

In particular r141's geometric e-annihilator for the regular p_g=q=0 surfaces has not been transported here. IHS varieties have H^{2,0}≠0. Their Alb is zero, but zero Albanese is not the missing torsion statement. The paid product lcm and d e² transfer cannot manufacture an annihilator for E. The original r141 formulas, sharp-denominator questions and middle-group obstruction remain unchanged.

Nor is D uniformly bounded by the source construction. Let δ=div(v). Then q(v,w) is a positive multiple of δ. For each prime p,

    v_p(D)=v_p(c_X 2^n/binom(2n,n))+n v_p(q(v,w)).

This is an exact compatibility constraint; cancellation in the rational prefactor must be retained. If an actual transport is chosen congruent to identity mod m and w is ±γ^N v, then q(v,w)≡0 mod m. Congruence refinements do not automatically remove bad primes. The source's unquantified loxodromic wall avoidance gives neither a uniform upper bound on this pairing nor a proof that the gcd of all resulting degrees is one.

Specialization of the displayed integral graph identities is paid when an ACTUAL common smooth proper model and the maps/cycles exist. It does not supply a relative graph or a global primitive bundle from fiberwise classes. The explicit twisted example makes that distinction visible.

## 6. Prefreeze decision

There is no full-scope substantial nominee to freeze. The primitive relative construction and its exact Veronese algebra close by paid source/primary operations and ordinary descent. A universal algebraic global-neutrality strengthening under just the specified fiberwise hypotheses fails in the explicit smooth K3 family above, even with the full positive two-system cone. The actual two-system transfer closes, with exact degree D, but leaves a non-torsion H^{2,0} summand; it cannot be plugged into the regular-surface torsion mechanism.

A new positive operation would have to control a genuinely additional interface, for example a specified geometric neutralization mechanism compatible with global descent, or a different non-Tate correspondence with a proven integral identity. None was established here. No conditional, coprime, restricted or renamed version is offered for acceptance, and none of these calculations changes an older frozen target or disposition. This is a bounded discovery outcome, not exhaustion or a worldwide impossibility/priority claim.
