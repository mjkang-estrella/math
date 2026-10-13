# I291 — independent proof validation of the frozen I287 target

## Verdict on the original artifact

**Main theorem: PASS. Boundary certificate: PASS. Optional Section 10 corollary: PASS with its explicitly credited external dependency. No necessary repair.** These verdicts concern the original 288-line `frontier/experiments/i287_crouzeix_repeated_support/analysis.md`, SHA-256 `8f8eb9a51203ec949356a1e92913447b56766e68496ec2384003c24430bbcd0b`, authenticated both in the working tree and at commit `8c9e63ee`. The candidate was not edited. Expansions below validate its equations; they do not silently replace a false statement.

All OpenAI results at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true. The elementary main proof does not need scalar rigidity or any Kippenhahn theorem. The positive-field bookkeeping is checked against the actual pinned direct manuscript. Section 10 additionally invokes the credited external scalar polynomial theorem. This is a proof gate, with no contribution acceptance, priority certification, or count increment. The supplied count remains twelve toward twenty.

## 1. Exact object, hypotheses and quantifiers

Use standard complex Hilbert spaces, Euclidean operator norms, and base-first evaluation. Put (t=3/4), (r=\sqrt7/4), so (t^2+r^2=1). The nonzero entries of (N\in M_6(\mathbb C)) are

\[
N_{12}=6/5,\quad N_{14}=\sqrt{14}/5,\quad N_{23}=8/5,
\quad N_{43}=-3\sqrt{14}/20,\quad N_{45}=5/4,\quad N_{56}=\sqrt2.
\]

The specified polynomial is

\[
P(z)=\begin{pmatrix}tz^2&rz^3\\rz&-tz^2\end{pmatrix},
\qquad E=P[N]=N\otimes rE_{21}+N^2\otimes t\operatorname{diag}(1,-1)+N^3\otimes rE_{12}.
\]

The main conclusion quantifies over **all constant complex unit vectors** (u,v\in\mathbb C^2). It proves 

\[
\|(v^*Pu)(N)\|\le\sqrt{849}/16<2=\|E\|,
\qquad \max_{W(N)}\|P\|=1.
\]

This defeats R016's unrestricted same-witness extension: the equality demanded there would be (\|p(N)\|=2M=2) and (\max_{W(N)}|p|=M=1). The main estimate by itself is not a claim that every compression has ratio (\|p(N)\|/\|p\|_{W(N)}<2); smaller denominator norms require a separate argument. Section 10 supplies nonattainment for each scalar polynomial using an external theorem. No strict supremum gap, smallest dimension, nondisk equality example, full size-six classification, or near-extremizer theorem is asserted.

## 2. Support spectrum, all directions and the disk

With heights (h=(3,2,1,2,1,0)), every nonzero (N_{ij}) has (h_i-h_j=1). Thus for (U_\theta=\operatorname{diag}(e^{ih_j\theta})),

\[
U_\theta NU_\theta^*=e^{i\theta}N,
\qquad \operatorname{Re}(e^{-i\theta}N)=U_\theta^*(\operatorname{Re}N)U_\theta.
\]

This proves the assertion for every real direction, without relying on finitely many directions. A product of four height-raising maps vanishes, so (N^4=0).

In coordinates ((1,3,5\mid2,4,6)), (\operatorname{Re}N=[0,C;C^*,0]), where

\[
C=\begin{pmatrix}3/5&\sqrt{14}/10&0\\4/5&-3\sqrt{14}/40&0\\0&5/8&\sqrt2/2\end{pmatrix}.
\]

Multiplication gives

\[
CC^*=\begin{pmatrix}
1/2&3/8&\sqrt{14}/16\\
3/8&23/32&-3\sqrt{14}/64\\
\sqrt{14}/16&-3\sqrt{14}/64&57/64
\end{pmatrix}=I-aa^*,
\quad a=(\sqrt2/2,-3\sqrt2/8,-\sqrt7/8)^T.
\]

Here (a^*a=1/2+9/32+7/64=57/64). Consequently the squared singular values of (C) are (1,1,7/64), all positive. The support eigenvalues are exactly (1,1,-1,-1,\sqrt7/8,-\sqrt7/8). In particular, the repeated eigenvalue really is the maximum; the smaller pair cannot be mistaken for it. The support function of (W(N)) is identically one. Compactness, numerical-range convexity, and the intersection description by all supporting half-planes give (W(N)=\overline{\mathbb D}). Multiplicity is exactly two in every direction, so no simple-support arc exists.

## 3. Boundary norm and the singular pair

For (|z|=1), the two columns of (P) have squared norms (t^2+r^2=1). Their inner product is (tr(\bar z^2z^3-\bar z z^2)=tr(z-z)=0). Hence (P(z)^*P(z)=I_2). For fixed unit complex (u,v), the scalar analytic function (v^*P(z)u) is bounded by one on the circle. The scalar maximum principle, followed by the supremum over (u,v), yields (\|P(z)\|\le1) on the entire disk. Circle unitarity supplies equality of the disk maximum with one.

The nonzero products needed for evaluation are

\[
\begin{array}{lll}
Ne_2=(6/5)e_1,&Ne_4=(\sqrt{14}/5)e_1,&Ne_5=(5/4)e_4,\\
Ne_3=(8/5)e_2-(3\sqrt{14}/20)e_4,&Ne_6=\sqrt2e_5,\\
N^2e_3=(3/2)e_1,&N^2e_5=(\sqrt{14}/4)e_1,&N^2e_6=(5\sqrt2/4)e_4,\\
N^3e_6=(\sqrt7/2)e_1.
\end{array}
\]

All other columns of (N^2,N^3) vanish. For example (N^2e_3=(48/25-42/100)e_1=(3/2)e_1). Define

\[
\ell=(\sqrt7/5)e_2-(3\sqrt2/5)e_4,
\quad x=(e_3\otimes f_1+e_6\otimes f_2)/\sqrt2,
\quad y=(e_1\otimes f_1+\ell\otimes f_2)/\sqrt2.
\]

One has (\|\ell\|^2=7/25+18/25=1), (N\ell=0), and (x,y) unit. The (f_1) part of (E x) is ((9/8+7/8)e_1/\sqrt2); its (f_2) part is (((2\sqrt7/5)e_2-(6\sqrt2/5)e_4)/\sqrt2). Thus (E x=2y). The next section supplies the upper bound and simplicity independently of this lower bound.

## 4. Every singular value, block orientation, and the exact complement

Give (e_i\otimes f_j) grade (h_i+g_j), with (g=(0,1)). The coefficient map (E_{21}) adds one to coefficient grade, the diagonal map adds zero, and (E_{12}) subtracts one. Combining these changes with the powers (N,N^2,N^3), each term raises total grade by two. Grade dimensions (0,1,2,3,4) are (1,3,4,3,1). Input grades three and four are annihilated.

The grade-zero basis is (e_6f_1). In grade-two output coordinates ((e_2f_1,e_4f_1,e_3f_2,e_5f_2)), its block column is

\[
(0,15\sqrt2/16,0,\sqrt{14}/4)^T.
\]

The grade-two to grade-four block, using that same input basis and output (e_1f_2), is the row

\[
(3\sqrt7/10,7\sqrt2/20,-9/8,-3\sqrt{14}/16).
\]

The column squared norm is (450/256+14/16=337/128). The row squared norm is (63/100+98/400+81/64+126/256=337/128). Each block is nonzero of rank one.

The middle block, inputs ((e_3f_1,e_5f_1,e_6f_2)) and outputs ((e_1f_1,e_2f_2,e_4f_2)), is exactly

\[
B=\begin{pmatrix}
9/8&3\sqrt{14}/16&7/8\\
2\sqrt7/5&0&0\\
-21\sqrt2/80&5\sqrt7/16&-15\sqrt2/16
\end{pmatrix}.
\]

This verifies the base-first orientation, particularly the two off-diagonal coefficient entries. In the orthonormal basis (b_+=(1,0,1)/\sqrt2), (b_-=(1,0,-1)/\sqrt2), (b_0=(0,1,0)), multiplication yields

\[
B^*B=4\oplus G,
\qquad G=\begin{pmatrix}67/64&33\sqrt7/128\\33\sqrt7/128&301/256\end{pmatrix}.
\]

Here (\operatorname{tr}G=569/256), (\det G=49/64>0), and the characteristic discriminant is (33^2\cdot113/256^2). Both eigenvalues are positive and equal to ((569\pm33\sqrt{113})/512). Since (G\succeq0), its largest eigenvalue is at most its trace, strictly below (337/128=674/256<4).

Thus the complete list of squared singular values of (E) is

\[
4,\quad337/128,\quad337/128,
\quad(569+33\sqrt{113})/512,\quad(569-33\sqrt{113})/512,
\quad0\text{ (seven times)}.
\]

The zero count also follows from ranks (1+3+1=5) in a twelve-dimensional space: grade-two contributes a three-dimensional kernel and grades three and four contribute four more. The top input line is exactly (\mathbb Cx). Its complement has squared restriction norm exactly (337/128), because both outer blocks attain that value. From (E^*E x=4x) and (Ex=2y), (E^*y=2x). The top output line is therefore exactly (\mathbb Cy), unique up to the simultaneous phase of the norming pair. The two orthonormal base vectors in each displayed pair give Schmidt rank two for both (x) and (y).

## 5. Complex product vectors and the uniform compression estimate

For unit (\xi\in\mathbb C^6), (u\in\mathbb C^2), let (\zeta=\xi\otimes u). Directly,

\[
|x^*\zeta|^2=\tfrac12|\xi_3u_1+\xi_6u_2|^2
\le\tfrac12(|\xi_3|^2+|\xi_6|^2)(|u_1|^2+|u_2|^2)\le1/2.
\]

Complex Cauchy–Schwarz applies to this bilinear expression by conjugating either vector; no reality restriction is used. Write (\zeta=\alpha x+\zeta_\perp). Since (x) is an eigenvector of (E^*E), the images of the two components are orthogonal. The exact complement bound gives

\[
\|E\zeta\|^2\le4|\alpha|^2+(337/128)(1-|\alpha|^2)
\le2+337/256=849/256.
\]

For any constant unit (u,v), polynomial evaluation commutes with coefficient compression:

\[
(v^*Pu)(N)=(I_6\otimes v^*)E(I_6\otimes u).
\]

The output factor is a contraction. Taking the supremum over all unit complex (\xi) proves the asserted norm bound. Strictness follows from (849<1024). Also (|v^*P(z)u|\le1) throughout (W(N)). This directly validates the same-witness counterexample independently of the optional scalar corollary.

## 6. Star-cyclicity and unitary irreducibility

The height blocks of (N) have ranks one, two, one; the middle two-by-two block is invertible. Hence (\operatorname{rank}N=4). As (e_1,\ell) are independent kernel vectors, (\ker N=\operatorname{span}(e_1,\ell)). Also

\[
N^3=(\sqrt7/2)e_1e_6^*,\qquad N^3N^{*3}=(7/4)e_1e_1^*.
\]

If an orthogonal projection (Q) commutes with (N,N^*), it commutes with the last rank-one projection. On its one-dimensional range (Q) must act as zero or identity, so (Qe_1=0) or (e_1).

The star-cyclic subspace of (e_1) contains

\[
a_2=N^*e_1=(6/5)e_2+(\sqrt{14}/5)e_4,
\quad a_1=N^{*2}e_1=(3/2)e_3+(\sqrt{14}/4)e_5,
\quad N^{*3}e_1=(\sqrt7/2)e_6.
\]

In the ((e_2,e_4)) plane (a_2\perp\ell), while

\[
Na_1=(12/5)e_2+(7\sqrt{14}/80)e_4,
\qquad \ell^*Na_1=3\sqrt7/8\ne0.
\]

Thus (a_2,Na_1) span that plane, placing (\ell) in the cyclic subspace. Next (N^*\ell=(\sqrt7/2)e_3-(3\sqrt2/4)e_5). Its coefficient determinant with (a_1) is (-2\sqrt2\ne0); these vectors span the ((e_3,e_5)) plane. Together with (e_1,e_6) this is all of (\mathbb C^6). Commutation propagates (Qe_1=e_1) to (Q=I), and (Qe_1=0) to (Q=0). This proves unitary irreducibility, without assuming that irreducibility of the support pencil follows just from a repeated characteristic factor.

## 7. Original field, full isotropy and exact residual

On (|w|=1) put (B_w=wI-N), (R(w)=wB_w^{-1}=\sum_{k=0}^3N^kw^{-k}), (H=R+R^*). Nilpotence makes (B_w) invertible. Direct multiplication, with (R^*=\bar wB_w^{-*}), gives

\[
B_w^*HB_w=wB_w^*+\bar wB_w=2I-\bar wN-wN^*
=2[I-\operatorname{Re}(\bar wN)]\succeq0.
\]

The support spectrum already proved gives nullity two. Congruence preserves inertia and rank, hence (H\succeq0) and (\operatorname{rank}H=4) at every circle point. Its mean is (2I). This is the original-matrix field, not a mass-one density representing a similar matrix. The direct source's strict-domain hypothesis is not silently applied at a boundary: the displayed congruence verifies positivity at this disk endpoint directly, with a polynomial resolvent and no limiting issue.

Take (X=[e_3,e_6]/\sqrt2), (Y=[e_1,\ell]/\sqrt2). Their ranks are two, (X^*X=Y^*Y=I_2/2), (X^*Y=0), and their Hilbert–Schmidt norms are one. Since (\operatorname{ran}Y=\ker N), (X^*N^kY=0) for every integer (k\ge0). The displayed power columns also give (X^*N^kX=Y^*N^kY=0) for all (k\ge1).

The cross moments are

\[
Y^*NX=rE_{21},\qquad Y^*N^2X=t\operatorname{diag}(1,-1),
\qquad Y^*N^3X=rE_{12}.
\]

For instance (\ell^*Ne_3=\sqrt7/2), (\ell^*N^2e_6=-3/2), and the factors (1/\sqrt2) on both sides supply (r,-t). Hence

\[
M(w)=Y^*R(w)X=\begin{pmatrix}tw^{-2}&rw^{-3}\\rw^{-1}&-tw^{-2}\end{pmatrix}=P(w^{-1}).
\]

It is unitary for every circle point. With (W=[X,Y]), (J=\operatorname{diag}(I_2,-I_2)), and (D=WJW^*=XX^*-YY^*),

\[
\Delta=W^*HW=\begin{pmatrix}I_2&M^*\\M&I_2\end{pmatrix}.
\]

Multiplication gives 

\[
\Delta J\Delta=\begin{pmatrix}I-M^*M&0\\0&MM^*-I\end{pmatrix}=0.
\]

Cyclicity of the finite-dimensional trace and positivity of (H) give

\[
\operatorname{tr}(HDHD)=\operatorname{tr}(\Delta J\Delta J)=0
=\|H^{1/2}DH^{1/2}\|_{\rm HS}^2.
\]

Thus (H^{1/2}DH^{1/2}=0), the full matrix identity, at every point. Because (\operatorname{ran}H^{1/2}=\operatorname{ran}H), every pair of vectors in that range has zero (D)-pairing; this is total isotropy, rather than just vanishing of an indefinite trace. On the orthogonal two-planes (\operatorname{ran}X,\operatorname{ran}Y), (D) acts as (1/2,-1/2); it is zero on their two-dimensional orthogonal complement. Its inertia is exactly ((2,2,2)). The maximal isotropic dimension is (2+\min(2,2)=4), attained by (\operatorname{ran}H).

For the disk (h(w)=w,q(w)=w,b_k(z)=z^k). Normalized Haar measure and Parseval give forward energy

\[
a^2=\sum_{k\ge0}\|Y^*N^kX\|_{\rm HS}^2=r^2+2t^2+r^2=2.
\]

The original diagonal fields are (X^*HX=Y^*HY=I_2), each with squared Hilbert–Schmidt energy two. The cross field is (M), of squared energy two. The norming parameter is (\gamma=2). All backward moments and the constant cross moment vanish. In the direct-source/I242 notation,

\[
E_X=4a^2/\gamma^2-2=0,\quad E_Y=0,\quad E_B=2+2-2\cdot2=0,
\quad T_{\rm res}=3\|Y^*X\|_{\rm HS}^2+\sum_{k\ge1}\|X^*N^kY\|_{\rm HS}^2=0.
\]

This checks both the constant three in the backward residual and the reciprocal diagonal normalization. The inherited identity has right side (2(4/\gamma^2-1)a^2=0), as required. No similarity density or unproved equality-limit substitution is used.

## 8. Separate audit of optional Section 10

The height blocks of (N) have outer squared norms (2,2) and middle block

\[
K=\begin{pmatrix}8/5&0\\-3\sqrt{14}/20&5/4\end{pmatrix},
\quad K^*K=\begin{pmatrix}23/8&-3\sqrt{14}/16\\-3\sqrt{14}/16&25/16\end{pmatrix}.
\]

Its trace is (71/16); the eigenvalue discriminant yields eigenvalues ((71\pm3\sqrt{105})/32). The larger exceeds two and is below four because (\sqrt{105}<19). The two nonzero blocks of (N^2) are the row ((3/2,\sqrt{14}/4)) and column ((0,5\sqrt2/4)^T), each of squared norm (25/8). The rank-one formula for (N^3) gives squared norm (7/4). Thus all three formulas in (13) are correct, all are below four, and higher powers vanish.

The actual versioned primary **ACV v3 Proposition 11.1** and its proof were inspected, including its (W(A)\subset\overline{\mathbb D}), nonzero polynomial, and disk-supremum hypotheses. Its necessary conclusion is a nonconstant scalar monomial. Its supporting Proposition 10.1 was also inspected at its domain hypotheses and proof. These are credited external scalar inputs, not stipulated OpenAI results. [Primary source](https://arxiv.org/html/2608.27346v3#S11).

Applying that necessary conclusion to (N), equality for a nonzero scalar polynomial would require (q(z)=cz^m), (c\ne0,m\ge1), hence (\|N^m\|=2). The exact power calculations exclude every such (m); constants have ratio one. The stipulated scalar bound excludes a ratio greater than two. Therefore (14) holds separately for every nonzero polynomial. No uniform gap for varying polynomials follows from this argument: limiting Schur jets may be realized by nonpolynomial functions, so the polynomial implication cannot be extended to them without more work. The original Section 10 keeps that distinction correctly. A scalar spectral supremum below two is neither proved here nor added to the candidate.

## 9. Antecedent consistency, attribution and validation limits

R016 and the completed I242/I245/I246 records concern attained finite polynomial witnesses in base dimension at most four, extracting a constant scalar compression of the specified polynomial. Their rank-one argument requires a simple-support arc. This six-dimensional irreducible example has rank-four (H), signature ((2,2,2)), and both Schmidt ranks two; the relevant dimension bound is saturated rather than forcing rank one. Thus it exposes the precise obstruction to extension without contradicting R016.

The base (N/2) agrees entry by entry with the LSS family reproduced in Lawrence v2 Section 4, at (x_0=3/5,y_0=4/5,c=\sqrt{14}/8,s=5\sqrt2/8,\xi_0=\eta_0=1/\sqrt2). In particular (c^2=7/32<1/4), (s^2=25/32=1-c^2), and all stated positivity and normalization conditions hold. The reproduction was read at the displayed matrix and constraints. [Primary reproduction](https://arxiv.org/html/1809.02779v2#S4). No novelty credit is assigned to the matrix or disk geometry. Historical/search comparisons in Section 8 are not dependencies for the algebraic theorem and do not amount to a contribution-gate conclusion here.

An independent standard-library exact check used four rational coordinates for (\mathbb Q(\sqrt2,\sqrt7)), with radical basis (1,\sqrt2,\sqrt7,\sqrt{14}). Multiplication reduces common radical factors using (2,7), never floating-point values. It checked the support factorization, nilpotence, every graded block, both outer energies, (G) and its determinant, both singular equations, cyclic coupling and determinant, all moments, both circle-unitarity coefficient identities, and all thirteen Laurent coefficients of (HDH=0). All assertions passed. The derivations above are the proof; the exact check is corroboration, not numerical evidence.

The review does not validate global literature priority, award substantiality, certify an acceptance count, or replay the wider research history. Only the named original artifact and necessary source scopes were used. Input hashes authenticate whole bytes; semantic reads are recorded separately in the reading log, literature index, and authentication JSON.
