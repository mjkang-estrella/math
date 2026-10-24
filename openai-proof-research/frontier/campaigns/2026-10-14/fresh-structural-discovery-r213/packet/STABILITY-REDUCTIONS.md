# Stability reductions and their exact limits

These are prefreeze source/classical reductions accompanying RELATIVE-DERIVATION.md. They are not a nominated new theorem, a substitute for old I286, or a quantitative geometric rigidity claim.

## Fixed ambient compactness gives an implicit modulus in relative filling distance

Fix n≥2, a proper CAT(0) space X, a nonempty closed convex C, c_0∈C and R<∞. Use the convex double D and constants from RELATIVE-DERIVATION.md. Consider relative integral n-cycles T on U=X\C with M_U(T)=1 and support closure contained in B̄_R(c_0). Define

    δ(T)=1−V_rel(T)/K_n ∈[0,1],
    d_rel(T,T')=V_rel(T−T').

This is an integral filling-distance topology on the relative cycles in question. Symmetry and the triangle inequality follow from changing orientation and adding integral fillings. If d_rel(T,T')=0, test T−T' on Lipschitz forms compactly supported in U and use the boundary identity for fillings whose exterior mass tends to zero. Every such test vanishes, so T=T'. Thus it is a metric here, without measuring any cap mass on C.

Let E be the set of cycles in this fixed class for which V_rel=K_n. A sequence T_j with δ(T_j)→0 has a subsequence converging in d_rel to an element of E. Here are all steps.

1. A_j=ΔT_j is an integral n-cycle in the fixed compact D-ball B̄_R(c_0), with M(A_j)=2. AK compactness and closure give a weakly convergent integral subsequence A_j→A with ∂A=0 and M(A)≤2.
2. D is CAT(0), so it satisfies the local cone inequalities needed in Wenger's weak-to-filling convergence theorem. The masses and boundary masses of A_j−A are uniformly bounded. Therefore V_D(A_j−A)→0. The triangle inequality for filling volumes gives V_D(A_j)→V_D(A).
3. The exact identity yields V_D(A_j)=2V_rel(T_j)→2K_n=c_n 2^q. The paid absolute bound for A implies M(A)≥2. Thus M(A)=2 and V_D(A)=c_n2^q. This proves that mass has not been lost; no independent noncollapse assumption was hidden.
4. Reflection σ of D satisfies σ#A_j=−A_j, hence σ#A=−A. On its fixed set C the current must equal its negative and therefore vanish. Off C, the two pieces have equal mass. Set T=A|(X_+\C), interpreted in X. It is locally integral, has zero boundary in U, mass one, and support closure in B̄_R(c_0). The canonical extension construction shows ΔT=A: they agree off C, and both have zero C-supported part. Consequently V_rel(T)=K_n and T∈E.
5. Linearity of Δ and the exact identity give

       d_rel(T_j,T)=½V_D(A_j−A)→0.

If E is empty, this argument instead proves that δ has a positive lower bound on the class. If E is nonempty, define

    ρ_(X,C,R,n)(t)=sup { dist_(d_rel)(T,E): T in the class, δ(T)≤t },

with the supremum over an empty set set to zero. It is bounded by 2K_n, and the sequence argument gives ρ(t)→0 as t↓0. This is an implicit compactness modulus. No explicit power, dimension-only modulus, Hausdorff estimate, or identification of E with geometric hemispheres has been proved. Such identification would additionally invoke the separate absolute current-equality classification; the original r58 full target is not adopted or reoffered here.

The proof uses fixed X,C,R. It cannot be transferred to varying proper CAT(0) spaces simply by asserting compactness. No common ambient embedding, dimension bound, doubling bound or injectivity scale is supplied by small deficit.

## Exact obstruction to diameter or Hausdorff support stability

This obstruction already occurs in Euclidean space, without ambient singularities. Let X=R^(n+1), C={x_(n+1)≤0}. For ε∈(0,1/2), take two disjoint upper half-balls with equatorial centers separated by L, radii

    r_1=(1−ε)^(1/n),  r_2=ε^(1/n),

and boundary orientations induced by their positive volume currents. Let T_(ε,L) be the sum of their curved hemispherical boundaries, as a relative current. Its mass is s_n/2. Euclidean top-dimensional constancy on the connected upper half-space forces every finite-mass relative filling to equal the sum of those half-ball currents there. Thus

    V_rel(T_(ε,L))=(ω_(n+1)/2)[(1−ε)^q+ε^q],
    δ(T_(ε,L))=1−(1−ε)^q−ε^q.

As ε↓0, δ/ε→q. The formula is independent of L. Choosing L→∞ makes the support diameter unbounded, while the normalized deficit tends to zero. Every comparison hemisphere of the same mass has radius one, so its support diameter is two. The Hausdorff distance between two nonempty compact sets is at least half the difference of their diameters; consequently distance to every such normalized hemisphere tends to infinity. This rules out a universal Hausdorff support estimate or diameter estimate from deficit alone.

It does not obstruct relative filling-distance convergence. The small far component has filling cost proportional to ε^q, and the main component's radius differs from one by O(ε). The example therefore distinguishes a mass-based topology from support topology, rather than announcing a gap where a known reduction already works.

## Strict convexity controls a given mass-additive decomposition

Suppose a relative cycle has a finite decomposition T=Σ_(i=1)^N T_i into relative integral cycles, with a=M(T)>0 and M(T)=ΣM(T_i). This is a hypothesis about a supplied decomposition, not an assertion that every metric integral current admits a particular indecomposable structure theorem. Put a_i=M(T_i)/a and δ_i=1−V_rel(T_i)/(K_nM(T_i)^q) for nonzero pieces. Subadditivity and the sharp relative bound imply

    1−δ(T) ≤ Σ a_i^q(1−δ_i).

In particular, with a_* = max_i a_i,

    1−δ(T) ≤ Σ a_i^q ≤ a_*^(1/n),
    a_* ≥ (1−δ(T))^n,
    1−a_* ≤ 1−(1−δ(T))^n ≤ nδ(T).

The same inequality retains the deficits of the pieces:

    Σ a_i^q δ_i ≤ δ(T)−[1−Σa_i^q] ≤ δ(T).

For a maximal piece,

    δ_* ≤ δ(T)/(1−δ(T))^(n+1)       if δ(T)<1.

These exact algebraic estimates pay for the straightforward concentration supplied by a mass-additive decomposition. They do not identify a flat tangent or a metric hemisphere. They cannot be applied across an unproved no-cancellation decomposition.

For a single Euclidean hemisphere current multiplied by an integer k≠0, constancy gives V_rel(kT)=|k|V_rel(T), while M(kT)=|k|M(T). Therefore its normalized deficit is

    δ(kT)=1−|k|^(−1/n).

A near-equality pure multiple must have |k|=1 once δ<1−2^(−1/n). This does not remove cancellation in mixed signed currents, nor establish that a general near-extremizer is such a pure multiple.

## Remaining possible operation, not a frozen claim

The completed deductions do not yield an effective rate to a geometric half-ball in varying CAT(0) spaces. A meaningful version would have to fix a measured deficit, a normalization, a topology and adequate compactness assumptions; then prove a quantitative estimate beyond the implicit compactness modulus. In particular, it would have to control the metric distortion or an appropriate mass-based distance after the source's chord/tangent operations, with a proved no-cancellation step. Equality of total masses under a contraction alone does not give an injective map or a bilipschitz inverse.

No such estimate is established here. The support-diameter formulation above is false as stated; the fixed-ambient filling-distance formulation is already paid by compactness and the exact double identity. The universal quadratic manifold asymmetry direction is an old I286 scope, not reopened. These distinctions leave this round PREFREEZE/no nominee, without an exhaustion or priority claim.
