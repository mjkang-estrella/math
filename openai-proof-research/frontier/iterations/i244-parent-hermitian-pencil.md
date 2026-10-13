# I244 — parent lemma on four-dimensional Hermitian pencils

2026-10-12. **Independent parent calculation; partial research note, not an accepted finding.** It does not prove complete Crouzeix rigidity or close the boundary-limit issue in I242. No claim of literature novelty is made.

## Lemma and proof

Let A=H+iK be a complex 4 by 4 matrix, with H,K Hermitian. Suppose W(A) has nonempty interior and, for every real theta, the largest eigenvalue of H cos(theta)+K sin(theta) has multiplicity at least two. Then A is unitarily equivalent to two identical 2 by 2 blocks. In particular W(A) is an ellipse.

Consider the monic real homogeneous polynomial
P(lambda,x,y)=det(lambda I-xH-yK).
If P has no repeated irreducible factor of total degree at least two, its repeated factors are real linear forms. A repeated linear factor must have nonzero lambda coefficient: a nonconstant factor depending only on x,y cannot divide the monic polynomial P. Thus each has the form lambda-a_j x-b_j y. At most two distinct such factors can be repeated, because P has degree four.

Away from the finitely many exceptional directions where distinct factors have coincident roots or a square-free factor has a multiple root, every multiple eigenvalue comes from a repeated factor. This finiteness follows by the one-variable resultant after restricting to projective directions; an identically vanishing resultant would instead give a common or repeated irreducible factor. The assumed top eigenvalue is therefore one of the at most two repeated linear roots. Since each such root is also an eigenvalue, the support function is exactly max_j(a_j cos(theta)+b_j sin(theta)) at every nonexceptional direction, and by continuity at all directions. This is the support function of a point or a segment, contradicting nonempty interior.

Consequently P has a repeated irreducible factor Q of degree at least two. Degree four and monicity force P=Q^2, after real monic normalization, and Q has total degree two and lambda degree two. Subtract the scalar matrix aI, where a=tr(A)/4. For H_0=H-tr(H)I/4 and K_0=K-tr(K)I/4 the resulting polynomial is
det(lambda I-xH_0-yK_0)=(lambda^2-q(x,y))^2
for a real homogeneous quadratic q. Hermitian diagonalization, rather than merely Cayley–Hamilton, gives
(xH_0+yK_0)^2=q(x,y)I
for every real x,y. Thus
H_0^2=alpha I, K_0^2=beta I, H_0K_0+K_0H_0=gamma I.
Nonempty interior means q is positive definite: otherwise its square-root support function describes a segment. In particular alpha>0 and delta=beta-gamma^2/(4alpha)>0.

Set J=H_0/sqrt(alpha) and L=(K_0-gamma H_0/(2alpha))/sqrt(delta). These are anticommuting Hermitian involutions. Relative to the plus/minus eigenspaces of J, L is a unitary off-diagonal map between them. Those spaces have equal dimension two. After a unitary basis change,
J=diag(I_2,-I_2), L=[[0,I_2],[I_2,0]].
Both H_0 and K_0 are therefore the same two by two Pauli pair tensored with I_2. Permuting the tensor factors makes A the direct sum of two identical 2 by 2 matrices. The numerical range is the corresponding nondegenerate ellipse.

## Limits of this note

This is the elementary repeated-eigenvalue branch of a possible complete-rigidity proof. It does not show that an extremal matrix-valued witness has a well-behaved limiting boundary certificate. It also does not justify scalarization at a simple support eigenvalue, remove boundary-spectrum singularities, or infer equality of scalar and complete norms in general. Those are separate analytic steps.

In particular, no nonexistent scalar nilpotent reducing block of P[A] is used. The I238 weighted-chain example remains valid. The lemma above concerns the Hermitian support pencil of the base A.

The argument has not received independent proof or contribution review. No source-truth audit, research code, numerical experiment or parameter scan was performed.
