# I287 — an attained rank-two counterexample to complete-witness scalarization

## Verdict and exact scope

**PROVED COUNTEREXAMPLE; nomination for independent proof/contribution review, not acceptance.** The repeated maximal-support case admits an irreducible six-dimensional attained finite-polynomial equality with both Schmidt ranks two and no constant scalar coefficient compression attaining the same norm. This answers the counterexample alternative in the brief. It does not disprove disk rigidity: the numerical range in this example is the unit disk. No full size-six classification is claimed.

All OpenAI results at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true. The principal counterexample below is nevertheless verified directly by exact finite-dimensional algebra; its norm proof needs no external scalar rigidity theorem and no Kippenhahn reducibility theorem. R016 is used only to identify the question being extended, not recounted as a new result.

## 1. The explicit matrices and statement

Let e_1,...,e_6 and f_1,f_2 be the standard orthonormal bases. Set

\[
N=\begin{pmatrix}
0&6/5&0&\sqrt{14}/5&0&0\\
0&0&8/5&0&0&0\\
0&0&0&0&0&0\\
0&0&-3\sqrt{14}/20&0&5/4&0\\
0&0&0&0&0&\sqrt2\\
0&0&0&0&0&0
\end{pmatrix},\qquad
P(z)=\begin{pmatrix}
(3/4)z^2&(\sqrt7/4)z^3\\
(\sqrt7/4)z&-(3/4)z^2
\end{pmatrix}.
\tag{1}
\]

Evaluation is base first: P[N]=sum_k N^k tensor C_k when P(z)=sum_k z^k C_k. Then:

1. N is unitarily irreducible, N^4=0, and W(N)=the closed unit disk.
2. For every real theta, Re(e^{-i theta}N) has eigenvalues +1,+1,-1,-1,+sqrt(7)/8,-sqrt(7)/8. Thus the maximal support branch has multiplicity exactly two everywhere, and no simple-support arc exists.
3. max_{W(N)}||P(z)||=1 and ||P[N]||=2.
4. For every pair of constant unit vectors u,v in C^2, the scalar polynomial p(z)=v*P(z)u obeys

\[
\|p(N)\|\le \frac{\sqrt{849}}{16}<2.
\tag{2}
\]

In particular there is no same-witness scalarization with ||p(N)||=2 and max_{W(N)}|p|=1. The unique top singular input and output of P[N] both have Schmidt rank two. The original positive boundary field has rank four and is totally isotropic for D=XX*-YY*, of inertia (2,2,2), at every boundary point. The counterexample therefore inhabits the actual exceptional equality system in the question, rather than only a repeated-factor pencil.

## 2. Numerical range and actual extremal multiplicity

Put A=N/2 and assign the integer heights

\[
(h_1,...,h_6)=(3,2,1,2,1,0).
\]

Every nonzero N_ij has h_i=h_j+1. For U_theta=diag(e^{i h_j theta}), U_theta N U_theta*=e^{i theta}N. Consequently all Re(e^{-i theta}N) are unitarily equivalent to Re N.

Reordering the coordinates as (1,3,5 | 2,4,6) gives

\[
\operatorname{Re}N=\begin{pmatrix}0&C\\C^*&0\end{pmatrix},\quad
C=\begin{pmatrix}
3/5&\sqrt{14}/10&0\\
4/5&-3\sqrt{14}/40&0\\
0&5/8&1/\sqrt2
\end{pmatrix}.
\]

With a=(sqrt(2)/2,-3sqrt(2)/8,-sqrt(7)/8)^T, direct multiplication gives

\[
CC^*=I_3-aa^*,\qquad a^*a=57/64.
\tag{3}
\]

Its eigenvalues are 1,1,7/64. The eigenvalues of Re N are therefore the six values in item 2. Equivalently its characteristic polynomial is (lambda^2-1)^2(lambda^2-7/64).

For every direction the support function of W(N) is one. The numerical range is compact and convex, so its intersection-of-supporting-half-planes description identifies W(N) with the closed unit disk. This proves disk geometry and double **maximal** multiplicity together, without mistaking the interior pair for the outer branch. Nilpotence N^4=0 follows either by multiplying or from the height range 0,...,3.

## 3. Boundary norm and the attained singular pair

Write t=3/4 and r=sqrt(7)/4, so t^2+r^2=1. On |z|=1 the columns of P(z) have norm one and their inner product vanishes. Hence P(z)*P(z)=I_2 there. For fixed unit u,v the analytic scalar function v*P(z)u has boundary modulus at most one; the scalar maximum principle and the characterization of operator norm by such pairings give ||P(z)||<=1 throughout the disk. Boundary unitarity makes the maximum exactly one.

Let

\[
\ell=(\sqrt7/5)e_2-(3\sqrt2/5)e_4,\quad
x=\frac{e_3\otimes f_1+e_6\otimes f_2}{\sqrt2},\quad
y=\frac{e_1\otimes f_1+\ell\otimes f_2}{\sqrt2}.
\tag{4}
\]

These are unit vectors and ell is unit. The needed products are

\[
\begin{aligned}
Ne_3&=(8/5)e_2-(3\sqrt{14}/20)e_4,& Ne_6&=\sqrt2e_5,\\
N^2e_3&=(3/2)e_1,&N^2e_6&=(5\sqrt2/4)e_4,\\
N^3e_6&=(\sqrt7/2)e_1,&N\ell&=0.
\end{aligned}\tag{5}
\]

Using C_1=r E_21, C_2=t diag(1,-1), C_3=r E_12 in (5) gives P[N]x=2y. The norm upper bound and simplicity are proved directly next, so equality is not being assumed from the singular-pair calculation.

## 4. Exact singular decomposition and uniqueness of the top vector

Give e_i tensor f_j total grade h_i+g_j, where (g_1,g_2)=(0,1). Every term of P[N] raises total grade by two. The grade dimensions from zero to four are 1,3,4,3,1. Thus its nonzero orthogonal blocks are grade 0 to 2, grade 1 to 3, and grade 2 to 4; the last two input grades map to zero.

The grade 0 to 2 and grade 2 to 4 blocks each have rank one and squared Hilbert--Schmidt norm 337/128, which is also their sole nonzero squared singular value. The middle block, in ordered input basis (e_3 tensor f_1,e_5 tensor f_1,e_6 tensor f_2) and output basis (e_1 tensor f_1,e_2 tensor f_2,e_4 tensor f_2), is

\[
B=\begin{pmatrix}
9/8&3\sqrt{14}/16&7/8\\
2\sqrt7/5&0&0\\
-21\sqrt2/80&5\sqrt7/16&-15\sqrt2/16
\end{pmatrix}.
\tag{6}
\]

Put b_+=(1,0,1)^T/sqrt(2), b_-=(1,0,-1)^T/sqrt(2), and b_0=(0,1,0)^T. Direct multiplication gives B*B b_+=4b_+. In the orthonormal complement (b_-,b_0), B*B has matrix

\[
G=\begin{pmatrix}67/64&33\sqrt7/128\\33\sqrt7/128&301/256\end{pmatrix}.
\tag{7}
\]

It is positive because it is a Gram compression, and tr G=569/256<337/128<4. Therefore every remaining squared singular value is at most 337/128, while the value four has multiplicity one. This proves ||P[N]||=2 and

\[
\ker(P[N]^*P[N]-4I)=\mathbb Cx,
\qquad
\|P[N]|_{x^\perp}\|^2=337/128.
\tag{8}
\]

For additional exact checking, the nonzero squared singular values are 4, 337/128 (twice), and (569 +/- 33sqrt(113))/512. There are seven zeros. The eigenvalue formula is not needed for the inequality. Since P[N]x=2y, (8) also gives P[N]*y=2x and the unique top output line is C y.

## 5. Every constant scalar coefficient compression misses equality

For a unit product vector zeta=xi tensor u, the Schmidt decomposition in (4) gives

\[
|x^*\zeta|^2\le1/2.
\]

Indeed apply Cauchy--Schwarz to the two coefficient components and the projection of xi onto span(e_3,e_6). Decomposing zeta along x and x-perp in (8),

\[
\|P[N]\zeta\|^2
\le4|x^*\zeta|^2+(337/128)(1-|x^*\zeta|^2)
\le849/256.
\tag{9}
\]

For any constant unit u,v and p=v*Pu,

\[
p(N)=(I_6\otimes v^*)P[N](I_6\otimes u).
\]

The output compression has norm one. Taking the supremum in (9) over unit xi proves (2). Also |p(z)|<=||P(z)||<=1 on W(N). This argument covers every complex u,v, not just real or coordinate vectors. It does not invoke Jin, scalar finite Schur interpolation, scalar monomial rigidity, or a numerical maximization.

The weaker qualitative contradiction is already decisive: scalarization at norm two would require a product vector in the one-dimensional top singular input space C x, whereas every nonzero vector there has Schmidt rank two. The explicit bound (2) is merely an exact verification of this particular obstruction, not a nominated positive-deficit theorem.

## 6. Unitary irreducibility of the base matrix

The kernel is span(e_1,ell). Equation (5) and N^3=(sqrt(7)/2)e_1e_6* give

\[
N^3N^{*3}=(7/4)e_1e_1^*.
\]

Suppose Q is an orthogonal projection commuting with N and N*. It commutes with this rank-one projection, so Qe_1 is either zero or e_1. It suffices to show that e_1 is cyclic for the star algebra generated by N.

The vectors

\[
\begin{aligned}
N^*e_1&=(6/5)e_2+(\sqrt{14}/5)e_4=:a_2,\\
N^{*2}e_1&=(3/2)e_3+(\sqrt{14}/4)e_5=:a_1,\\
N^{*3}e_1&=(\sqrt7/2)e_6
\end{aligned}
\]

belong to its cyclic subspace. Both a_2 and N a_1 lie in span(e_2,e_4). The first is orthogonal to ell, while

\[
\ell^*N a_1=3\sqrt7/8\ne0.
\]

They consequently span that two-plane, so ell belongs to the cyclic subspace. Next

\[
N^*\ell=(\sqrt7/2)e_3-(3\sqrt2/4)e_5.
\]

Its coefficient determinant with a_1 in span(e_3,e_5) is -2sqrt(2), hence those two vectors span that plane. Together with e_1 and e_6, the cyclic subspace is C^6. If Qe_1=e_1 then Q=I; if Qe_1=0 apply the same argument to I-Q to obtain Q=0. Thus N is unitarily irreducible.

## 7. The actual rank-two zero-slack system is realized

Use the original mass-two field on the disk, not the structural companion's density for a similar matrix:

\[
R(w)=(I-N/w)^{-1}=I+Nw^{-1}+N^2w^{-2}+N^3w^{-3},\quad
H(w)=R(w)+R(w)^*,\quad |w|=1.
\]

The resolvent is everywhere invertible. Direct congruence gives

\[
(wI-N)^*H(w)(wI-N)=2I-\bar wN-wN^*\succeq0.
\tag{10}
\]

The support calculation shows that this slack has nullity two. Therefore H(w)>=0 and rank H(w)=4 at every w.

In base-first vectorization set X=[e_3,e_6]/sqrt(2), Y=[e_1,ell]/sqrt(2), and D=XX*-YY*. Their ranks are two, their Hilbert--Schmidt norms are one, and X*Y=0. Since ran Y=ker N, all X*N^kY vanish, including k=0. Also X*N^kX=Y*N^kY=0 for k>=1. From (5),

\[
M(w):=Y^*R(w)X=
\begin{pmatrix}
tw^{-2}&rw^{-3}\\
rw^{-1}&-tw^{-2}
\end{pmatrix}.
\tag{11}
\]

This is unitary on the circle. The positive compression by W=[X,Y] is

\[
\Delta=W^*H W=\begin{pmatrix}I_2&M^*\\M&I_2\end{pmatrix},\quad
J=\operatorname{diag}(I_2,-I_2).
\]

It satisfies Delta J Delta=0. In particular

\[
0=\operatorname{tr}(\Delta J\Delta J)
 =\operatorname{tr}(HDHD)
 =\|H^{1/2}DH^{1/2}\|_{\rm HS}^2.
\tag{12}
\]

Thus ran H is totally isotropic for D at every boundary point. D has inertia (2,2,2), so its maximal isotropic dimension is four and is actually attained. This is the substantive algebraic answer to the proposed rank-two reduction: the saturated system is consistent with irreducibility and a genuinely matrix-valued inner channel; it does not force rank one or scalar coefficient compression.

The direct-source residual bookkeeping also checks exactly. Its forward coefficient energy is a^2=||M||_{L2(HS)}^2=2. The two diagonal energies and cross energy are all two, gamma=2, all backward coefficients vanish, and E_X=E_Y=E_B=T_res=0. The field has a regular circular boundary, so no limiting-domain subtlety is needed to verify this example.

## 8. How the old pencil leads to a new equality witness

The **base matrix is credited prior art**. Lawrence, arXiv:1809.02779v2, Section 4, reproduces the Li--Spitkovsky--Shukla family with entries A_12=x_0, A_14=c y_0, A_23=y_0, A_43=-c x_0, A_45=s xi_0, A_56=eta_0, where s=sqrt(1-c^2), x_0^2+y_0^2=xi_0^2+eta_0^2=1 and 0<c<1/2. Equation (1) is twice its member at

\[
x_0=3/5,\quad y_0=4/5,\quad c=\sqrt{14}/8,\quad
s=5\sqrt2/8,\quad xi_0=eta_0=1/\sqrt2.
\]

The new construction is P and the proof that its equality cannot be scalarized. It is not a nomination of the old Kippenhahn counterexample or old disk geometry.

The rank-two lead selected the exact conditions eta_0^2=1/2 and y_0^2=1/(2s^2). They make the orbit of ker H fit inside a fixed four-plane. On that plane the two rank-two signs in D survive; the cross resolvent becomes the polynomial inner channel (11). Transposing/conjugating its coefficient array in the source's bilinear pairing produces P in (1). The explicit proof above replaces this derivation as the correctness certificate.

Nearest contribution collisions: the old LSS pencil itself; ACV v3 Theorem 5.3 (orthogonal rectangular Schmidt supports) and Proposition 5.4 (top-singular simplicity in specified minimal cases); ACV Section 7 and Corollaries 11.4--11.5 (complete equality equivalence only through size three); R016 (specified-witness scalarization through size four). The inspected statements do not furnish this irreducible attained rank-two polynomial counterexample. A bounded duplication search does not establish worldwide priority. Full source extents and hashes are in the authentication record and literature index.

## 9. Validation and remaining scope

A package-free exact arithmetic check in Q(sqrt(2),sqrt(7)), represented by four rational coefficients, independently multiplied the numerical-range factorization, N^4, both singular-pair equations, the total-grade blocks, the Gram complement (7), both 337/128 block energies, and the irreducibility coupling. It passed without any floating-point arithmetic. The generic-family exploratory check recorded in reading-and-failures.md was also a single exact rational linear system, not a scan. The displayed equations give a complete hand-verifiable proof.

No external scalar theorem is a proof dependency for items 1--4. The stipulated direct complete theorem is consistent with the explicitly proved norm two, and its actual resolvent/residual inputs were read to verify the fit to the research question. No quantum amplification is used as a functional-calculus transformation.

Disk rigidity in the repeated-support case remains an independent question: this example preserves a disk while disproving the desired universal scalarization bridge. No all-size-six equality classification, higher-dimensional nondisk example, minimal counterexample dimension, nonattained-supremum result, or quantitative near-equality theorem is asserted. The supplied twelve accepted findings remain twelve pending independent integration.

## 10. Parent's optional scalar-scope check: attained polynomials only

This is a credited downstream scope check, not a second nomination and not a proof that the scalar spectral constant is strictly below two. The exact monomial norms are

\[
\|N\|^2=(71+3\sqrt{105})/32<4,\qquad
\|N^2\|^2=25/8<4,\qquad
\|N^3\|^2=7/4<4,\qquad N^j=0\ (j\ge4).
\tag{13}
\]

For the first formula the height blocks of N have outer squared norms two and the middle block K=[[8/5,0],[-3sqrt(14)/20,5/4]]. Its Gram matrix is [[23/8,-3sqrt(14)/16],[-3sqrt(14)/16,25/16]], with eigenvalues (71 +/- 3sqrt(105))/32. Its maximum exceeds two and is strictly less than four: 105<19². For N² the two nonzero height blocks are (3/2,sqrt(14)/4) and (0,5sqrt(2)/4)^T, each of squared norm 25/8. The N³ formula follows from (5).

The scalar polynomial-on-disk theorem already credited in R016 (also read explicitly as ACV v3 Proposition 11.1) says a scalar polynomial attaining factor two on this disk must be a scalar monomial. Every nonzero monomial evaluation is excluded by (13), and constant polynomials have ratio one. Consequently every individual nonzero scalar polynomial q satisfies

\[
\|q(N)\|<2\max_{|z|\le1}|q(z)|.
\tag{14}
\]

This assertion uses that credited external scalar theorem; the principal compression counterexample in Sections 1–7 does not. It is not a separate substantiality claim.

Equation (14) alone leaves open whether a sequence of different scalar polynomials has ratios tending to two. Compactness of the first four Schur jets would turn such a sequence into a norm-two bounded holomorphic jet extremizer, but that extremizer need not itself be a polynomial. The polynomial monomial conclusion cannot be silently applied to it. No exclusion of all such nonpolynomial Schur-jet extremizers is proved here, so no assertion psi_scalar(N)<2 is added. Same-witness coefficient non-scalarization, nonattainment for each scalar polynomial using credited scalar theory, and a strict supremum gap are kept distinct.
