# Candidate full proof of Banica–Nechita Conjecture 6.6

Status: mathematical derivation, requires adversarial checking and literal formalization. No credit claimed. 2026-10-27.

Source: Banica–Nechita, *Flat matrix models for quantum permutation groups*, arXiv:1602.04456v3, p.20, Conjecture 6.6. Projections P,Q,R,S on a finite-dimensional complex Hilbert space; PQ=RS=0; ran(P)∩ran(R)=ran(Q)∩ran(S)={0}; two rank balances. Define P'=(P+R)^{†/2} P (P+R)^{†/2}, and R' similarly, Q',S' from Q+S. Claim Tr(PR)+Tr(QS)≥Tr(P'Q')+Tr(R'S'). Here †/2 means the positive inverse square root on support, zero on kernel.

The proof below in fact does not use the rank balances.

## 1. Frames and grading

Choose orthonormal column frames p,r,q,s for the four ranges. Let E=[p r], F=[q s]. The disjointness hypotheses imply E,F have full column rank. Put G=E*E, H=F*F, U=E G^{-1/2}, V=F H^{-1/2}. Then U*U=I and V*V=I, so K=U*V is a rectangular contraction. Its four blocks, relative to (p,r) and (q,s), are the cross-Gram matrices of the primed projections: this follows from (EE*)^{†/2} E=E(E*E)^{-1/2}. Thus the target right side is the squared Hilbert–Schmidt norm of the block-diagonal part of K.

Let J=diag(I_rankP,-I_rankR), L=diag(I_rankQ,-I_rankS). Put A=G-I and B=H-I. Because p,r and q,s separately have orthonormal columns, JAJ=-A, LBL=-B. Since G,H are positive definite and their grading conjugates are 2I-G,2I-H, the spectra of A,B lie strictly in (-1,1). Also E*F has zero diagonal blocks by PQ=RS=0, hence J(E*F)L=-E*F.

Set K'=JKL. From E*F=G^{1/2}KH^{1/2} and the grading relations,

    G^{1/2} K H^{1/2} = -(2I-G)^{1/2} K' (2I-H)^{1/2}.

In orthonormal eigenbases of A,B, write eigenvalues a_i,b_j and entries k_ij,l_ij of K,K'. Then

    sqrt((1+a_i)(1+b_j)) k_ij + sqrt((1-a_i)(1-b_j)) l_ij = 0.

## 2. Scalar estimate

For a,b in (-1,1), set u=sqrt((1+a)(1+b)), v=sqrt((1-a)(1-b)). For complex k,l with uk+vl=0,

    |k+l|² = [1 - sqrt((1-a²)(1-b²))/(1+ab)] (|k|²+|l|²)
             ≤ (a²+b²)(|k|²+|l|²).

The equality follows by writing l=-(u/v)k. For the inequality set t=a²+b². If t≥1, the bracket is ≤1. If t<1 and ab<0, sqrt((1-a²)(1-b²))≥1-t≥(1-t)(1+ab). If t<1 and ab≥0, use the exact identity

    (1-a²)(1-b²) - (1-a²-b²+ab)² = (a-b)²(1-a²-b²) ≥0

to obtain sqrt((1-a²)(1-b²))≥1-t+ab≥(1-t)(1+ab). Thus the bracket is ≤t in all cases.

## 3. Sum and contractivity

The block-diagonal part of K is (K+K')/2. By the scalar estimate,

    ||(K+K')/2||_HS² ≤ 1/4 Σ_ij (a_i²+b_j²)(|k_ij|²+|l_ij|²).

Both K and K'=JKL are contractions. Each row and column has squared Euclidean norm at most 1, in any orthonormal bases. Consequently the last expression is at most

    (1/2)(Σ_i a_i² + Σ_j b_j²)
      = (1/2)(Tr A² + Tr B²)
      = ||p*r||_HS² + ||q*s||_HS²
      = Tr(PR)+Tr(QS).

This proves the full source inequality. No assertion of strictness or equality classification. All matrix dimensions, including unequal ranks and zero ranks, are allowed; empty blocks/sums have their usual meanings.

## Pending gates

Independent checking of all identities; bounded primary prior-art/subsumption search; full literal Lean endpoint with Moore–Penrose square-root bridge; paper and extracted replay. No acceptance claim. The two projection pairs' frames may have different column counts, which is why rectangular contractivity must be used.

## Appendix: explicit justification of the Moore–Penrose bridge

For a full-column-rank E, choose a reduced singular-value decomposition E=W D Z*, with W*W=I, Z unitary and D diagonal with strictly positive entries. Then EE*=W D² W*. Its positive Moore–Penrose inverse square root is W D^{-1} W* (zero on ran(W)⊥). Thus

    (EE*)^{†/2} E = W Z* = E(E*E)^{-1/2}.

For example p=E I_P, where I_P is the coordinate inclusion of the p-columns; consequently P=E I_P I_P* E* and

    P' = U I_P I_P* U*.

It follows that Tr(P'Q')=||I_P* U* V I_Q||_HS², and similarly Tr(R'S') equals the squared norm of the other diagonal block. This proves the literal normalization bridge, rather than merely choosing some orthogonalization with the same ranges.

For full-column-rank E: if E(x,y)=px+ry=0, the vector px=-ry lies in ran(P)∩ran(R), hence is zero; orthonormality of the columns gives x=y=0. Empty column spaces cause no difficulty; if E or F has no columns, the target right side is zero directly.

For contractivity, ||U*Vz||≤||Vz||=||z|| because U,V are isometries. Similarly K*=V*U is a contraction. A row sum of squared absolute values is ||K*e_i||²≤1, and a column sum is ||Ke_j||²≤1. J and L are unitary involutions, so the same statements hold for JKL before and after either eigenbasis change. No simultaneous diagonalization of A and B on the ambient Hilbert space is required: they act on separate frame-coordinate spaces.
