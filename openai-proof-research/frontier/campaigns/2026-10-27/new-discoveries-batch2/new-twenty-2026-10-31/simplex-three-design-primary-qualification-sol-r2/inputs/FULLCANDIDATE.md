# 362896: all-dimensional ordinary nonexistence proof; SCIENTIFIC HOLD

Author's ordinary proof only, not independent PASS, novelty clearance, root acceptance or credit. No formal execution or dispatch. Full literal: no equal-weight d-point simplex 3-design for ANY integer d>=3 in the probability simplex with d coordinates. Repeated points, if allowed as a multiset, are also ruled out. The proof even allows arbitrary real coordinates summing to one, so positivity is not an implicit restriction.

Primary binding: Gonzalez Avella–Czartowski–Goyeneche–Zyczkowski, Quantum 9,1763 (2025), DOI10.22331/q-2025-06-04-1763. Actual final PDF sources/simplex-final.pdf, Definition4 p4, Eq5 p5, Conjecture7 p8; relevant final p8 visually inspected. Current official arXiv record lists v4 May30 2025 and this final DOI. Actual final rather than inferred version equivalence was read. Appendix B.1 p16 treats d=3 by a one-angle cost; p8's general argument is a degrees-of-freedom heuristic. No extra unistochastic, cyclic, orthonormal-basis, or quantum hypothesis belongs to the simplex conjecture. The corpus d-point notation means dimension d-1, as Definition4 explicitly says.

## Exact theorem and elementary moment input
Let d>=3, let e_i be the standard coordinate vectors in R^d, let 1=(1,...,1), c=1/d *1, P=I-J/d, and u_i=e_i-c. Let X be uniform on {x_i>=0, sum x_i=1}. Suppose p_1,...,p_d are real vectors with coordinate sum one and their uniform empirical averages match E f(X) for every polynomial of total degree <=3. We prove a contradiction.

The needed simplex moments are
E X_i=1/d;
E X_i X_j=(1+delta_ij)/[d(d+1)];
E X_i X_j X_k=[1+delta_ij+delta_ik+delta_jk+2 delta_ij delta_jk]/[d(d+1)(d+2)].
These follow from E product X_i^{a_i}=(d-1)! product(a_i!)/(d-1+sum a_i)!. For completeness, the latter is the elementary Dirichlet integral: integration over the standard (d-1)-simplex of product x_i^{a_i}, including x_d=1-sum_{i<d}x_i, is product a_i!/(d-1+sum a_i)!. Induct on the number of free variables; integrate the last variable after scaling by the residual mass, using int_0^1 t^r(1-t)^s dt=r!s!/(r+s+1)!, itself obtained by r integrations by parts followed by the integral of (1-t)^{r+s}. Divide by the volume 1/(d-1)!. Coordinate hyperplane surface measure differs by a constant Jacobian, which cancels on normalization. Thus these moments are exactly those of the source flat probability measure, not an assumed different law.

Set q_a=p_a-c and Y=X-c. The first and second moments give sum_a q_a=0 and
sum_a q_a q_a^T=P/(d+1).
Every q_a lies in U=1^perp. Write Q for the square matrix with columns q_a. Thus Q1=0, 1^TQ=0, and QQ^T=P/(d+1). On U, Q is invertible, since QQ^T is the positive scalar 1/(d+1) times the identity. Hence Q^TQ=P/(d+1): indeed on U the equality QQ^T=lambda I implies Q^T=lambda Q^{-1}, so Q^TQ=lambda I, and both sides kill 1. Consequently
q_a dot q_b=(delta_ab-1/d)/(d+1).
This is an exact regular-simplex Gram matrix, with no classification assumption or rotation chosen.

## Cubic invariant of any such d-node second design
For a third-order array A, write ||A||^2=sum_{i,j,k} A_ijk^2, an ordinary finite sum. Set T_emp=(1/d)sum_a q_a^{tensor3}. Expanding the sums gives
||T_emp||^2=(1/d^2)sum_{a,b}(q_a dot q_b)^3.
There are d diagonal ordered pairs and d(d-1) off-diagonal ordered pairs, whence
||T_emp||^2=(d-1)(d-2)/[d^3(d+1)^3].                 (A)
Explicitly the sum before dividing by d^2 is
[d(d-1)^3-d(d-1)]/[d^3(d+1)^3]
=(d-1)(d-2)/[d(d+1)^3]. No sign or unordered-pair factor is omitted.

## Cubic invariant of the uniform continuous simplex
Let S=sum_a u_a^{tensor3}. Entrywise expansion shows
S_ijk=delta_ij delta_jk-(delta_ij+delta_ik+delta_jk)/d+2/d^2.
Centering the three raw moments above gives
T_cont=E Y^{tensor3}=2 S/[d(d+1)(d+2)].
For instance the three index patterns i=j=k, i=j!=k and all distinct follow directly from the raw moment formula; equivalently expand (X_i-1/d)(X_j-1/d)(X_k-1/d) and collect the Kronecker deltas.
Since u_a dot u_b=delta_ab-1/d, expansion as before gives
||S||^2=sum_{a,b}(u_a dot u_b)^3=(d-1)(d-2)/d.
It follows that
||T_cont||^2=4(d-1)(d-2)/[d^3(d+1)^2(d+2)^2].      (B)

Matching every cubic polynomial requires T_emp=T_cont entry by entry. Equating (A) and (B), multiplying positive denominators and cancelling (d-1)(d-2)>0, forces
(d+2)^2=4(d+1), i.e. d^2=0,
contradicting d>=3. This proves the full conjecture. There is no asymptotic or finite-range unpaid mathematical lemma in this ordinary proof.

Boundary self-check by algebra: at d=2 the cancelled factor d-2 vanishes, so the proof correctly does not rule out the known two-point interval Gaussian rule. At d>=3 no denominator vanishes. d=1 is outside the conjecture. The argument needs exactly equal weights, as specified by Definition4, and makes no weighted-cubature claim.

## Failed routes and sustained mechanism
1. The source fourth-moment rank bound proves only t>=4 nonexistence; using its rank as a degree-three obstruction would be invalid. Rectangular degree1-by-degree2 moment matrices have insufficient rank for this shortcut.
2. Matching the diagonal cubic moments or comparing a particular cyclic orbit fails to control arbitrary rotations of the regular second-design simplex. The 2018 construction only matches selected symmetry averages; the full 2025 correction paper confirms that mixed cubics are essential.
3. The successful invariant simultaneously contracts ALL mixed cubic constraints. It removes the rotation variable before comparison; it is neither one changed scalar estimate in an existing all-d proof nor an endpoint/domain correction. The source only dimension-counts remaining constraints and solves d=3 by an angle. The new obstruction is equality of the full cubic tensor norm for every rotation. This is a substantive significance argument, not a claim that shortness establishes novelty.

## Prior and significance limits
Actual complete 2505.05894v1 (May9 2025), Comment and correction for On Explicit Construction of Simplex t-designs, was read. Its Theorem1 repairs full-symmetric averaging; Theorem2 constructs d(d-1)-point (pseudo)designs. It does not supply an all-d d-point nonexistence theorem. It identifies why the older alleged three-point example fails, which is consistent with the proposed theorem. Its displayed construction has no direct implication to this nonexistence endpoint.
Three charged searches/nine strings are saved completely and immediately. They identify classical Gaussian cubature nonexistence and Fritsch1970 as SPECIFIC relevant prior leads. Fritsch primary DOI returned challenge-bearing HTML; actual theorem/proof unread, all new deliveries closed, NETWORK-STOP.md. A triangle-only absence claim does not by itself settle all-d nonexistence; no routine/public exclusion is asserted from excerpts. Classical general cubature might nevertheless subsume this proof, so this is a real prior/significance HOLD, not merely generic worldwide uncertainty. The corpus-listed 1308.3188 predecessor is also unread and not compared. Current four registry roots are inherited unavailable; no refresh/reconstruction. No worldwide novelty or current registry clearance.

No independent author-proof review, 96-family comparison, formal endpoint, paper, strict replay or root adjudication is claimed. One prospective family only: pseudodesign extension, cubic-invariant helper and quantum corollaries receive no separate credit. Preserve this author ordinary proposal with scientific HOLD; do not dispatch.


## Finite-sum Gram proof avoiding invertibility and heavy linear algebra
Here is a replacement for the U-invertibility paragraph, useful for an elementary certificate. Put lambda=1/(d+1), C_ab=sum_i Q_ia Q_ib. From QQ^T=lambda P and Q1=0, by interchanging finite sums:
sum_a C_aa=lambda(d-1),
sum_ab C_ab^2=lambda^2(d-1),
sum_ab C_ab=0,
sum_ab P_ab^2=d-1,
sum_ab C_ab P_ab=sum_a C_aa-(1/d)sum_ab C_ab=lambda(d-1).
Therefore sum_ab (C_ab-lambda P_ab)^2=0. Every summand is nonnegative over R, so every summand is zero, giving C=lambda P. The second identity uses sum_ab C_ab^2=sum_ij (sum_a Q_ia Q_ja)^2=lambda^2 sum_ij P_ij^2. These are exact distributive finite sums, no spectral, rank, square-root, determinant or matrix inverse theorem. This also makes duplicate-node impossibility automatic from the positive diagonal/negative off-diagonal Gram entries. The invariant proof remains full ordinary mathematics without programs or numerical checks.
