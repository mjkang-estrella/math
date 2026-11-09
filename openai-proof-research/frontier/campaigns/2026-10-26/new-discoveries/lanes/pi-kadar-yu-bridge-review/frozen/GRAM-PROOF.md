# The arbitrary-head Gram/gcd argument — prospective source resolution

This argument replaces the cyclic-compression portion of the earlier hand proof.
It is not yet independently reviewed. It is not a newly counted generic spectral
theorem. The ONLY proposed discovery is its exact application to all partitions
in Morris–Martin Conjecture4.5.1 / MathDB372352, subject to the source-scope review
in SOURCE-BRIDGE.md. The accepted tally is unchanged at16/30.

Let G be ANY real symmetric m-square matrix, m>=1, with a distinguished coordinate
placed last. Append s vertices in a path, with zero new diagonal and coupling+1
between adjacent path vertices and from the first new vertex to the attaching
coordinate. Call the resulting real symmetric matrix G_s and put
f_s(X)=det(XI+G_s). Put g=monic-gcd(f_0,f_1), p_s=f_s/g, and p_-1=Xp_0-p_1.
Every matrix and quotient here is literal in GramModel/ComplexGram. The real
and complex normalized gcd quotients are proved to agree by coefficient mapping.

## Reduction and the boundary

The border determinant gives f_(s+2)=X f_(s+1)-f_s. Thus g divides every f_s.
Every quotient is monic, and p_(s+2)=X p_(s+1)-p_s. The initial pair is coprime
by removal of the actual gcd; Bezout propagation proves every consecutive pair
coprime. The first border identity is f_1=X f_0-f_minor, with f_minor the
characteristic polynomial of -G after deleting the attaching coordinate. Hence
f_minor=g p_-1, p_-1 is monic, and p_-1,p_0 are coprime. There is no hypothesis
that g and p_0 are coprime; overlap and repeated factors of g are retained.

## Squarefreeness without Lanczos

For a real symmetric matrix H and a principal submatrix B of codimension one,
write N_H^+(t), N_H^-(t) for the numbers of eigenvalues strictly above/below t,
and m_H(t) for the multiplicity of t. The proven dimension argument gives

    0 <= N_H^±(t)-N_B^±(t) <= 1.

Because N_H^+(t)+N_H^-(t)+m_H(t)=dim H, it follows that
|m_H(t)-m_B(t)|<=1. These are literal polynomial-root multiplicities, not
multiplicities assigned to a surrogate list.

If t is a root of p_s, coprimality excludes it from p_(s+1). Subtract the common
g multiplicity in f_s=g p_s and f_(s+1)=g p_(s+1). The bound above gives
multiplicity_t(p_s)<=1. The quotient splits over R because it divides the
characteristic polynomial of a real symmetric matrix. Therefore p_s is
squarefree. The minor/initial-head pair gives exactly the same argument for
p_-1. This covers the source's boundary k=-1 without assuming a cyclic head.

## Exterior count

The added s-path is a principal submatrix of -G_s. Its spectrum lies strictly
inside(-2,2), by the exact cosine formula (the sign of the unit coupling is
irrelevant to its characteristic polynomial). For every threshold t, the count
of eigenvalues of -G_s above t lies between the tail count and that count+m;
the same is true below t. At t=2 and t=-2, this bounds both exterior counts by m.
Appending a vertex makes each count nondecreasing by principal comparison.
Bounded integer monotone sequences eventually stabilize. Roots(f_s) is the
multiset sum Roots(g)+Roots(p_s), so subtracting the FIXED exterior count of g
proves eventual stabilization for p_s, with all multiplicities retained.

## Density, including both endpoints

For every -2<a<b<2 and every R, a sufficiently fine cosine grid provides R
DISTINCT roots of one finite free path inside(a,b). The proof constructs
consecutive grid indices using a natural floor and an Archimedean bound; this
is an exact finite existence argument, not a numerical mesh.

The head/tail count sandwich implies that adding the fixed m-dimensional head
can lose at most m eigenvalues from any half-open interval(a,b]. Therefore choose
a path with more than m+deg g roots in a smaller interval(a,B), a<B<b. The full
matrix then has more than deg g roots in(a,B], counted with multiplicity. The
factor g cannot account for all of them, so p_s has a root in(a,b). Equivalently,
the implemented proof uses card(Roots(g))+1 as the number the full matrix must
retain, avoiding any unnecessary degree equality.

Every open subinterval of(-2,2) is hit. Metric closure gives the full interior,
and closure((-2,2))=[-2,2] gives BOTH endpoints. The complex coefficient bridge
also proves that every complex root of each reduced polynomial is real, that
exterior counts agree, and that evaluation at a real alpha agrees exactly.

## Proposed source application

SOURCE-BRIDGE.md identifies the source's one-varying-tail mixed Gram matrix with
the literal G_s construction, preserving arbitrary couplings among different
heads. Source Proposition3.25 gives f_s=F P_(N+s), F=C P_N^(d-1) fixed monic;
ramping/reducedness gives the initial coprimality. Monic factor uniqueness forces
P_(N+s)=p_s. The complex uniqueness theorem is proved as well, so this step does
not assume that the source first chose real rather than complex coefficients.
The source recurrence identifies P_(N-1)=p_-1. The three conjectured clauses
then follow at every source parameter, provided the universal Gram encoding is
accepted as the faithful source bridge. The source-scope question remains for
independent review; no premise or representation-theoretic assumption is hidden
inside a theorem named after the source.

All spectral tools, gcd facts and Chebyshev identities are classical, and none
receives separate credit. Prior-art and eligibility of the explicit source
resolution still require renewed independent scrutiny. No manuscript, final
review, packet extraction or acceptance has yet been completed for this lane.
