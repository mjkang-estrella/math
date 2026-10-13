# I317 — full quantitative operation comparison

## 1. Target, frozen evidence and verdict

**TECHNICAL for the entire Q315 package**, including its qualitative consequences. This is an affirmative routine reduction, not an identical-publication claim. Neither I314's negative verdict nor I316's theorem verification is inherited as a contribution verdict.

The frozen input is all 124 lines of `frontier/iterations/i315-quantitative-amplification-gap.md`, SHA256 `53020ac5aa0e859cf48c3746c92adf2ab832f51dc9bdc7ddaf145bc3d400c41d`. For every integer r>=2, the specified A_r must remain finite, explicit, unitarily irreducible, nilpotent with A_r^(r²+1)=0, of dimension (r³+3r)/2, and have w(A_r)<=1. In base-first evaluation Q[A]=sum A^k tensor Q_k it must have attained C_r(A_r)=2 and C_d(A_r)<=2-(1-d/r)/22 for every 1<=d<r. The latter must hold for all size-d matrix Schur functions on the open disk, without degree or boundary assumptions. Uniformity over r at fixed lost channel fraction is part of the target, not optional explicitness.

All supplied I312 and I314 hashes match. Their finalized full reports and analyses were read. I314's authentication and literature records were also read; their external-reading claims were not promoted to my own source reads. The user subsequently authorized finalized I316. Its report and entire analysis match `570824e6ed9ce43829252b182a5fd4d48d7d9eff77874768faca5ddb491563d0` and `b827fa0d77faf2097d67066283d40d0dc921b15d7b62317ebc8f0e6f0f3d8e0b`. This supplement is proof evidence, not a replacement target or another contribution round.

The literal frozen proof has a single necessary repair: in line 96, `a epsilon<5epsilon`, with a=7/2+sqrt(2)<5, is false at epsilon=0. At d=r the specified transpose witness has gamma=2 and h=f, so that comparison asserts 0<0. Replace its last comparison by `<=5epsilon`. I use and prove the weak comparison below; all Q315 conditions and constants survive. The frozen file remains unchanged. I316 calls the literal proof FAIL and independently verifies the theorem with this repair; I do not relabel that as PASS unchanged.

## 2. What the actual primary predecessors do

Gau–Wu (2009), Theorem 5 and its proof, uses the metric sqrt(2) on ker S(phi), 1/sqrt(2) on ker S(phi)* and identity between, with phi=zf and scalar inner f(0)=0. Theorem 8 and its full proof extracts those endpoints from equality through the condition-two similarity. These are old scalar operations. Its scalar cyclicity argument cannot simply prove higher-defect irreducibility, and it states no Q315 quantitative matrix hierarchy. The matrix extension needed here is written in Section 4.

Benhida–Fricain–Timotin (2021), model formulas (2.4)–(2.7), Lemma 3.1 and Corollary 3.2 with proofs, equates reducibility of a C00 contraction to constant nontrivial input/output defect blocks of its characteristic function. For Theta=zPhi, the scalar z leaves this criterion unchanged. Hermitian conjugacy Phi B Phi*=constant is equivalent to the criterion by spectral projections, as I314 correctly explained. This alone gives no uniform stability modulus: irreducible inner functions can approach reducible ones. Q315 therefore requires more than applying I314 and saying “quantify compactness.”

Werner (2000 preprint; 2001 publication), Theorem 1 equations (5)–(6), Proposition 3 with proof, and Section 4's construction statements and proofs, supplies the classical equivalence of orthonormal unitary bases and exact depolarizing averages, and all-dimensional Fourier/shift constructions. The required moment is only the first adjoint moment B -> tr(B)I/r, not a higher unitary-design condition. Werner does not state Q315's analytic delay polynomial, its endpoint model or its Schur hierarchy. Section 3 performs the conversion, preserving finite polynomial size.

DPW's Theorem 2.3, with its proof and Lemmas 2.1–2.2, gives ||rho||_wcb=(||rho||_cb+||rho||_cb^(-1))/2 for unital completely bounded homomorphisms. Its converse starts with a witness at level n and forms a triangular test at level 2n. It does not fix n=1 or force attainment at level two. Its discussion also credits Okubo–Ando's old complete disk bound for numerical contractions. These operations are relevant background, not a replacement hierarchy reduction.

## 3. Exact Fourier averaging and polynomial size are routine here

Let D(s)=diag(s^i), i=0,...,r-1, and U the normalized Fourier matrix. Independent normalized phase averaging of D(s)U D(t) conjugation first kills off-diagonal entries of B by integration in t, then sends the diagonal to entries tr(B)/r using |U_ik|²=1/r, and kills output off-diagonals by integration in s. This is the old dephase–Fourier–dephase implementation of depolarization.

For this bounded-frequency integrand, replace (s,t) by (z^r,z). Its (i,j) entry has exponents

    r(i-j)+k-l,    |k-l|<=r-1.

The exponent is zero exactly when i=j and k=l, so the independent averaging result survives exactly. Multiplying by z cancels in conjugation and ensures vanishing at zero. Thus

    Phi=z diag(z^(ri)) U diag(z^j),
    integral Phi B Phi* d sigma=(tr B/r)I             (T)

for every complex r-by-r B. This is a one-variable analytic lift, not an appeal to an arbitrary discrete design with unspecified delays. Frequency separation, rather than uniqueness of every pair difference, explains why exponential Sidon delays are unnecessary.

A further direct check connects (T) with the classical finite operation. All adjoint-moment frequencies have absolute value at most r²-1, so circle averaging agrees with averaging over the r²-th roots of unity. For z_m=exp(2 pi i m/r²), the unitaries Phi(z_m) form an orthogonal unitary basis: up to a scalar phase,

    tr(Phi(z_m)*Phi(z_n))
      =(1/r)(sum_i z_(n-m)^(ri))(sum_j z_(n-m)^j).

For m!=n modulo r² the first sum vanishes unless n-m is divisible by r; in that remaining case the second sum vanishes. For m=n the trace is r. This illustrates precisely the old first-moment operation being encoded. It does not claim this particular polynomial path was previously published.

Put Theta=zPhi=z² D_M U D_N and L=r²+1. In Theta^-1=z^-2 D_N^-1 U* D_M^-1, every entry of z^L Theta^-1 has exponent L-2-j-ri>=0. Therefore z^L H² is contained in Theta H², H=K_Theta consists of polynomials of degree below L and C=P_H M_z|H satisfies C^L=0.

The elementary decomposition K_AB=K_A orthogonal-sum A K_B for inner A,B gives

    dim H=2r+sum_i ri+sum_j j=(r³+3r)/2.

For exact coordinates use the three orthonormal families z^a e_i (0<=a<2), z^(2+a)e_i (0<=a<ri), and z²D_M U z^b e_j (0<=b<j). Empty index ranges contribute nothing. This is the nominated finite algebraic model, up to orthonormal coordinates. No numerical scan, infinite-dimensional base, direct sum or nonanalytic design substitution is involved.

## 4. The old endpoint model preserves numerical radius and attainment

Constants E and F=Phi C^r lie in H, are orthogonal and each have dimension r. Since H is backward-shift invariant, ker C*=E. If Cf=0, then zf=Theta h, so f=Phi h; orthogonality to Theta H² forces h constant and ker C=F. For f perpendicular to F, testing zf against Theta h with h=h(0)+zh_1 proves zf belongs to H. Thus C is isometric on F-perp and

    C*C=I-P_F,    CC*=I-P_E.

Set G=H orthogonal-minus (E+F),

    X=P_E/sqrt(2)+sqrt(2)P_F+P_G,    A=XCX^-1,
    B=CX^-1/sqrt(2).

Then B*B=P_E+P_G/2. On the range of B, which is perpendicular to E, sqrt(2)sqrt(I-B*B)=X. Hence A=2sqrt(I-B*B)B. Cauchy–Schwarz gives, for a unit a,

    |<Aa,a>|<=2||Ba||sqrt(1-||Ba||²)<=1.

This is the scalar Gau–Wu factorization with endpoint subspaces instead of lines, not a new use of the OpenAI theorem. Similarity preserves C^L=0 and the base dimension.

For every matrix Schur Q, right multiplication by Q^T is contractive on the Hardy space of r-by-d matrix fields. Its compression is Q[C], so ||Q[A]||<=||X||||X^-1||=2 at every level. With P=Phi^T, the unit vector represented by I_r/sqrt(r) at the constant endpoint is carried by P[C] to Phi/sqrt(r) at F. Endpoint weighting multiplies this by two. Therefore P is a finite disk-contractive polynomial and ||P[A]||=2, proving exact attained C_r(A)=2. The transpose is required by base-first vectorization.

## 5. Generic quadratic loss lemma, including all constants

This calculation applies to any contraction S on H tensor C^d with the same endpoint metric, before choosing S=Q[C]. It is the elementary quantitative form of the old similarity equality chase, and contains no dependence on r or d.

Take a unit top singular input x for X S X^-1, and put gamma=||X S X^-1||, epsilon=4-gamma², u=X^-1 x and z=Su. Tensor identities are suppressed. Cancellation gives

    epsilon=2(2-||u||²)+2(||u||²-||z||²)+<(2I-X²)z,z>.

All three terms are nonnegative. The endpoint spectral identities are

    2I-X^-2=(3/2)P_F+P_G >= P_(E-perp),
    2I-X²=(3/2)P_E+P_G >= P_(F-perp).

Consequently ||x_(E-perp)||²<=epsilon/2, ||z_(F-perp)||²<=epsilon and ||u||²-||Su||²<=epsilon/2. For v=P_E u,

    ||u-v||²<=epsilon/2,    ||v||²>=2-epsilon.

For D=(I-S*S)^(1/2), positivity and contractivity give ||Du||²<=epsilon/2 and ||D||<=1. Thus

    ||Dv||<=||Du||+||D(v-u)||<=sqrt(2epsilon),
    ||v||²-||Sv||²<=2epsilon.                       (D)

The square root is the standard defect seminorm. Its triangle inequality turns O(sqrt(epsilon)) vector perturbation into an O(epsilon) quadratic defect. No stability theorem about arbitrary irreducible models is being assumed. Using only norm differences would give a weaker estimate, but choosing the positive defect form is an ordinary Hilbert-space operation.

Now specialize to S=Q[C]. Represent v by the constant V in M_(r,d), let w=Sv, and f=P_F w=Phi W. Set h=VQ^T before compression. Then P_H h=w and contractive multiplication plus Pythagoras gives

    ||h-w||²=||h||²-||w||²<=||v||²-||Sv||²<=2epsilon.

Writing c=(1+1/sqrt(2))²=3/2+sqrt(2), the endpoint tail estimate and ||S||<=1 give ||w-f||²<=c epsilon. Since h-w is perpendicular to H and w-f belongs to H,

    ||h-f||²<= (2+c)epsilon=(7/2+sqrt(2))epsilon<=5epsilon,
    ||W||²=||f||²>=2-(3+c)epsilon>=2-6epsilon.       (E)

Both roundings follow from sqrt(2)<3/2; at zero the first final comparison is weak, as required by I316. The second bound remains valid if its right side is negative. These are Hilbert–Schmidt norms for constant matrices and Hardy Hilbert–Schmidt norms for fields. The 5 and 6 are slack constants; no optimum or delicate dimension cancellation is claimed.

## 6. Exact rank/trace obstruction preserves the fraction gap

Let Pi be the projection onto (ran V)-perp, with q=rank Pi/r>=t=1-d/r. Since Pi h=0 pointwise, (E) implies

    ||Pi Phi W||²<=||h-f||²<=5epsilon.

The integrand involves the polynomial Phi W only. Taking trace against Pi in (T) gives exactly

    ||Pi Phi W||²=q||W||².

Nonnegativity of ||W||² is needed before replacing q by t. In the safe order,

    t(2-6epsilon)<=t||W||²<=q||W||²<=5epsilon.

This remains true when 2-6epsilon<0 or rank V<d. It implies

    epsilon>=2t/(5+6t)>=2t/11,
    2-gamma=epsilon/(2+gamma)>=epsilon/4>=t/22.

This is the target constant and uniformity, not an unspecified compactness modulus. For d/r<=1-alpha with alpha>0, the gap is at least alpha/22 independently of r. For d=r-1 it is 1/(22r), so no uniform gap for a single missing channel is claimed. At d=r the argument permits gamma=2 and the explicit witness attains it.

The only uncertainty/rank fact used is tr(Pi I/r)=rank Pi/r. There is no assertion that W itself is flat, and no stability of spectral projections of WW* is required. This bypasses the potential small eigenvalue spacings that could make a generic quantitative version of I314 nonuniform. The chosen depolarizing moment supplies the entire required mass bound directly.

## 7. The Schur quantifier and irreducibility are retained

For any open-disk size-d Schur Q, each entry lies in H². Radial Parseval proves the multiplier bound without boundary continuity. For Q_s(z)=Q(sz), s<1, the closed-disk Taylor series converges uniformly and compresses to sum_(k<L) C^k tensor s^k Q_k. Radial H² convergence and the fact that vectors of H are polynomials pass this compression identity to s increasing to one. Hence Q[C] and Q[A] are defined by the finite first L jets, while the uncompressed h may have arbitrarily long tails. Sections 5–6 apply to each such Q. Taking suprema immediately preserves the gap; compactness is unnecessary. In particular, bounding all Schur functions bounds the unrestricted-degree polynomial supremum. No inference from one witness or its constant compressions is used.

For irreducibility, a reducing orthogonal projection R of A preserves ker A=F and ker A*=E. It commutes with X and hence with C,C*. Its endpoint restrictions are constant projections V0,W0. Pairing RC^k e=C^k V0 e with Phi a gives V0 Phi_k=Phi_k W0 for every coefficient k; thus V0 Phi=Phi W0. Circle unitarity gives V0=Phi W0 Phi*. Averaging gives V0=(tr W0/r)I. A scalar projection is zero or identity and W0 is the same one. The constants are jointly cyclic for C, since their compressed monomials span H. Therefore R is zero or identity.

This is the classical fixed-defect-block criterion with an exact depolarizing exclusion. Weighting preserves the kernels and their projections, so irreducibility is not lost in passing from C to A. Gau–Wu's rank-one cyclicity argument has not been incorrectly substituted for this proof.

## 8. Why this is TECHNICAL, and why other negative shortcuts fail

Q315 improves I314 in two genuine mathematical respects: the delays are polynomial and the all-level gap is explicit and uniform for a fixed lost fraction. I314 plus generic compactness alone cannot supply either quantitative conclusion. The new calculation nevertheless reduces to (i) bounded-frequency encoding of the classical Fourier depolarizer, (ii) the old endpoint metric with its fixed spectral gaps, (iii) the generic defect-square-root estimate (D), and (iv) exact projection trace. Sections 3–7 preserve every target condition and constant. The residual operation is ordinary Hilbert-space deficit bookkeeping joined to exact first-moment mixing on a freely chosen model. I judge that routine synthesis TECHNICAL under the project distinction between a new structural compatibility bridge and supporting stability estimates. A correct result, a stronger quantifier, a polynomial formula and a useful uniform gap do not alone establish substantiality.

This conclusion does not assert that every quantitative irreducibility argument is routine. An arbitrary near-reducible inner family would require new uniform information; here its required quantitative mixing is an exact classical moment chosen into the model. Nor does the conclusion assert that Gau–Wu or BFT already states the new inequality. Their roles are limited above, and the additional calculation has actually been supplied.

DPW is not an all-level-at-two theorem. Its test [[C^-1 I_n,(1-C^-2)B],[0,C^-1 I_n]] retains n and doubles it. The factor 1/2(C+C^-1) controls the numerical radius of amplified evaluations, not the generator's first attainment rank. For the full one-generator disk algebra, scalar contractivity would force ||A||<=1 and complete contractivity; dividing evaluation by two destroys unitality and multiplicativity. This does not collapse the present threshold-two hierarchy.

Pisier's primary earlier version, Theorem 1.1, Corollary 1.2 and the CAR norm argument, establishes one-generator separation. The published final PDF was inaccessible. Davidson–Paulsen's author-uploaded primary preprint, Theorem 3.1 with proof and Remark 3.6, explicitly documents finite compressions with uniformly bounded scalar polynomial norm and complete norms growing without bound. Their diagonal shifts and finite CAR realization allow finite nilpotence, but no Q315 numerical-radius-one and exact-endpoint claim is supplied. Indeed, the old complete disk bound <=2 for w(T)<=1 implies that such an unbounded complete-norm sequence cannot all satisfy w(T)<=1. Rescaling generators to normalize w alters every power, so it does not preserve complete norm two, its attainment level, or the full smaller-level gap. These are credited predecessors, not the reduction being used.

R019 was read in full and the completed I292 review was read. Their spent rank-two witness on the separately specified old LSS base bounds constant coefficient compressions of that witness, not every scalar Schur function. Their substantial bridge paid compatibility conditions on that original base. Here A is defined to be the weighted model, so no analogous original-base compatibility is unresolved. I309's completed review and its quantitative analysis Section 5 were read: E307 is known and Q310 technical, and its degree-dependent endpoint-deletion modulus does not give Q315's uniform fraction gap. This report neither counts those results again nor infers Q315's verdict from them.

## 9. Source dependence and exact priority boundary

AGENTS.md and upstream.json were read. The actual pinned direct `thm:main` and structural `thm:structural`, `thm:representation`, and full `prop:extremal` with proof were retrieved from immutable raw GitHub URLs at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb and inspected. Their truth is stipulated. The companion endpoint interpolation is credited, but Q315 uses an explicitly prescribed old endpoint model instead of finding an optimal metric for an arbitrary original matrix.

All of Sections 3–7, including the complete upper bound, works without the recent complete Crouzeix theorem. The result is source-motivated and may be new to this project; it is not a deduction whose complete upper bound logically requires that new theorem. That limitation matters for any source-dependent nomination.

The bounded priority search covered the named endpoint models, matrix-model reducibility, unitary averaging, one-generator polynomial/complete separation and quantitative numerical-contraction leads. No identical Q315 theorem was authenticated. This search miss is not the negative verdict's basis and is not positive novelty evidence. The published Pisier body and Holbrook's full proof were inaccessible; no exhaustive matrix-inner stability or operator-space literature search was completed. Unread sources are not claimed to lack the theorem. Precise identities, semantic extents and failures appear in the companion records.

Only the five assigned authored artifacts are finalized. No subagents, numerical scans, git, publication, shared-index changes or acceptance/count edits were made. I313 was not read; I316 was read only after explicit finalization authorization. All r and both qualitative/quantitative variants remain one nomination.
