# r171 prefreeze calculations: an exact relative interface

No nominee is frozen. This is a concrete diagnostic of a proposed strengthening, followed by the strongest compatible reduction. It neither changes an old full target nor asserts that equivariant realization is generally impossible.

## 1. Full-cone compatibility does not force extension of an ideal action

Let D₀=W⊗K and U=⊗_(n≥1)M₂. Set

    D=D₀⊗U,
    P=C([0,1])⊗D,
    I=C₀((0,1])⊗D.

This is an essential ideal I in P. P is exactly in the prescribed nuclear separable W-stabilized class, since the remaining factors can be put into A. No classification assumption about a nonnuclear algebra is involved.

Let z=diag(1,−1) and let b be the involution of D which is the identity on D₀ and ⊗Ad(z) on U. The product is well defined because its finite restrictions agree on the finite tensor stages. It is a point-norm limit of multiplier-inner automorphisms, implemented by the finite products of z. It therefore fixes every extended lsc tracial weight, by the two-sided norm-limit argument in COHERENCE.md.

For a real parameter θ write

    v(θ) = [[cosθ,−sinθ],[sinθ,cosθ]],
    θ(t) = (π/8)(1+sin(1/t)),  0<t≤1.

Put V(t)=1_(M(D₀))⊗v(θ(t))⊗1_tail. This is a bounded norm-continuous unitary multiplier of I. It need not extend continuously to t=0, and no such extension is assumed. Define an automorphism δ of I by

    (δf)(t) = Ad(V(t)) b(Ad(V(t)*)(f(t))).                     (5)

The expression is norm continuous on (0,1]. Its norm at t is ||f(t)||, so it vanishes at 0 for f∈I. Thus it belongs to I. Equation (5) is the conjugate of the honest involution b by the automorphism Ad(V) of I; hence δ²=id exactly. This is not an approximate action with an unverified associator.

Both b and Ad(V) fix all extended traces on I. Multiplier-inner invariance follows from τ(x*x)=τ(xx*) applied to an element of I of the form a^(1/2)V; point-norm closure is handled by both norm limits and lower semicontinuity. Therefore

    Tδ=id_(T(I)).                                             (6)

In particular this action is compatible with the identity action on the full cone T(P), under restriction to I and under the canonical extension of ideal weights. Its induced ideal action is trivial. This conclusion includes weights infinite outside a proper finite domain. It is not merely equality of bounded or densely defined traces.

## 2. The ideal action can still have the Rokhlin property

In a tensor factor M₂ numbered n≥2 define

    p_+ = (1/2)[[1,1],[1,1]],
    p_- = (1/2)[[1,−1],[−1,1]].

These are orthogonal projections summing to 1, and z exchanges them. The oscillating multiplier V uses only the first factor, so δ exchanges these two projections in every tail factor exactly.

For completeness, choose approximate units h_j∈I which are products of scalar cutoffs on (0,1] and a positive contractive approximate unit of D₀, with the U factor equal to 1. They are δ-invariant and commute with all the tail projections. Choose tail indices n_j→∞. Then

    e_(±,j)=h_j p_±^(n_j)

are positive contractions in I, exchanged by δ, with product zero and sum h_j. For every fixed a∈I they commute asymptotically with a, because h_j is an approximate unit and a is approximable by finite tensor sections. Also (h_j²−h_j)a→0 and a(h_j²−h_j)→0. Thus their classes in F∞(I) are projections, orthogonal, and sum to the identity. They provide Rokhlin towers in the nonunital definition. The obstruction below persists even with these towers.

## 3. Failure of extension is a norm-level boundary calculation

Choose a positive d∈D₀ with ||d||=1 and let

    a=d⊗e₁₁⊗1_tail ∈D.

Regard a also as the constant section in P. On the first matrix factor, (5) is conjugation by

    w(θ)=v(θ) z v(θ)*
        =[[cos(2θ),sin(2θ)],[sin(2θ),−cos(2θ)]].

At θ=0, w=z and δ_t(a)=a. At θ=π/4, w is the flip matrix and

    δ_t(a)=d⊗e₂₂⊗1_tail.

There are sequences t_j,s_j→0 with sin(1/t_j)=−1 and sin(1/s_j)=1. The two values above are a distance exactly 1 apart. Consequently the bounded continuous function t↦δ_t(a) on (0,1] has no norm limit at 0.

Suppose an automorphism Δ of P extended δ exactly. An automorphism of an essential ideal has a unique strict extension to M(I). Under the faithful inclusion P⊂M(I), Δ must agree with that multiplier extension on P: for x∈P and y∈I,

    Δ(x)δ(y)=δ(xy).

The right-hand side determines Δ(x) as a multiplier because I is essential. Evaluating on sections supported near any t>0 gives

    (Δ(a))(t)=δ_t(a).

But every element of P has a norm limit at 0. The two sequences above contradict this. Thus δ has no extension to an automorphism of P, regardless of what action one tries to prescribe on P/I. In particular there is no extended involution agreeing exactly with δ.

This diagnostic is elementary. It is not offered as a nonroutine new finding or as an author-proof nominee. It rules out only the asserted implication “full-cone compatibility alone implies exact extension of this prescribed ideal action.” It does not rule out replacing the ideal action by a conjugate or cocycle conjugate one: δ was explicitly constructed by conjugating a perfectly extendible product action with an ideal multiplier that does not preserve P.

## 4. The strongest compatible extension reduction

For an essential extension

    0→I→E→B→0

write its Busby map τ:B→Q(I)=M(I)/I. The algebra E is the pullback

    E = {(m,b)∈M(I)⊕B : q(m)=τ(b)}.

Given honest actions δ on I and γ on B, let δ̃ and δ̄ be the multiplier and corona actions induced by δ. The formula

    Δ_g(m,b)=(δ̃_g(m),γ_g(b))                                 (7)

defines an action on E precisely when

    δ̄_g τ = τ γ_g    for all g.                              (8)

Sufficiency follows immediately from the pullback equation; invertibility and the group law follow from those of δ and γ. Necessity follows by applying q to the image of a lift. Thus the extra datum is exact Busby covariance, not an unnamed “relative classification gap.”

Equation (8), when supplied, already pays this exact extension operation by ordinary extension theory. The full trace cone does not imply it, as Sections 1–3 demonstrate. Corrections implemented by 1+I are the identity in the corona and cannot repair a failure of (8) while leaving the given ideal action fixed. Allowing arbitrary multiplier conjugacies may alter the corona map, but then exact agreement with the prescribed relative data has been lost.

The Source301 J(U)-correction and small-stabilizer method controls cut ranks, local ideal errors, and model equality. Its compact module corrections ultimately yield actual maps and isomorphisms. None of those stated interfaces forces a specified corona equation for an already fixed action on an essential ideal. In the example, equalities of all ideal/quotient cone information coexist with the missing norm-continuity at the boundary. Replacing the precise boundary requirement by a trace error estimate would erase the obstruction instead of resolving it.

## 5. Discovery boundary

A genuinely new relative realization theorem would need a fully specified valid set of hypotheses controlling the fixed ideal action and the extension class, followed by a new operation beyond (7)–(8) and the source/primary compositions. No such nonroutine operation has been closed in this round. I do not nominate a conditional theorem which assumes its missing compatibility, a restricted version of an old target, or the elementary oscillation example. The outcome remains PREFREEZE/no nominee, with a concrete paid range construction and an explicit unpaid relative interface.
