# Prospective full Kadar–Yu root-distribution theorem — credit 0

26 October 2026. Proposed complete hand argument for MathDB372352,
Morris–Martin arXiv2512.24535v1 Conjecture4.5.1, p35. **No acceptance or complete source formal
verification claimed.** Source, mathematical, bounded novelty and eligibility
review must assess the reduction below before formalization is prioritized.

## 1. Exact question and source facts

Fix l≥−1, λ⊢l+2, d=dim S^λ≥1 and N=l+4. Write P_n=P_n^(λ) for the
source's monic reduced Chebyshev series. The conjecture asks:

1. P_(N+k) is square free for **every k≥−1**, not only the physical n≥N range.
2. The number of its roots outside [−2,2] is eventually constant.
3. The union of its roots in [−2,2] for k≥0 is dense in [−2,2].

The actual conjecture was visually inspected in the p35 PDF render. The
following are established SOURCE statements, not hypotheses invented here:

- §3.13, Eq(3.2.3): after an orthonormal Specht basis is chosen, the one-cup
  Gram matrix is αI+B with B a **real symmetric constant matrix**.
- Eq(3.2.4): each tail is a chain with diagonal α and successive off-diagonal
  entries 1. A tail beyond the head has no coupling to another tail.
- §3.17: tails may have independently chosen lengths n_i≥N; let Γ_(n_1,…,n_d)
  denote this mixed-length real symmetric Gram pencil.
- Eq(3.2.17), p26: extending one chosen tail by one appends a single row and
  column whose unique off-diagonal entry is 1 in the coordinate at that tail's
  old endpoint, and whose diagonal entry is α.
- Proposition3.25: det Γ_(n_1,…,n_d)=C(α)∏_(i=1)^d P_(n_i)(α).
- P_n is reduced: consecutive polynomials are coprime. The tail determinant
  recurrence is P_(n+1)=αP_n−P_(n−1), as explicitly in Eqs(3.2.7)/(3.2.9). The printed
  plus sign in Eq(3.1.1) conflicts with that determinant recurrence and the
  classical sine formulas; no credit is sought for correcting that typo.

No explicit polynomial conjectures of §3.3, no conjectured integrality of C,
and no unproved arm formula of §5 are used.

## 2. A general cyclic-compression lemma (classical machinery)

Let A be any finite real symmetric matrix and e any unit coordinate vector.
Let K=span{e,Ae,A²e,…}; its orthogonal complement is invariant under A.
Write r=dim K≥1. Gram–Schmidt on e,Ae,… gives a real Jacobi matrix J on K:
its subdiagonal entries are nonzero until dimension r, and e can be
placed at its final coordinate by reversing the basis order. On K^⊥ write A₀.

Now append s new vertices to A by a path: the first is coupled to e with
weight 1, successive new vertices are coupled with weight 1, and each new
diagonal is zero. Denote the extended matrix A_s. Then

    A_s ≅ A₀ ⊕ J_s,

where J_s is the (r+s)×(r+s) irreducible Jacobi matrix formed by appending a
zero-diagonal, unit-off-diagonal path to J. Thus

    D_s(x):=det(xI−A_s)=g(x) q_s(x),
    g=charpoly(A₀), q_s=charpoly(J_s).

Every q_s is monic with distinct real zeros. Successive q_s strictly interlace,
so gcd(q_s,q_(s+1))=1. These are standard Jacobi facts: an eigenvector whose
last component is zero must vanish successively along the tridiagonal rows;
therefore each eigenspace has dimension at most one, and symmetry identifies
algebraic and geometric multiplicity. Strict interlacing follows from Cauchy
interlacing plus the impossibility of a common eigenvalue of successive
principal Jacobi matrices. In particular the above factor g is exactly the
monic gcd of D_0 and D_1, including multiplicities.

The principal (r−1)×(r−1) submatrix obtained by deleting e from J has monic
characteristic polynomial q_(-1). For r=1 this is the constant polynomial 1.
The determinant recurrence gives q_1=xq_0−q_(-1). Accordingly q_(-1) is also
square free, and strictly interlaces q_0 when its degree is positive.

An equivalent proof uses the spectral measure of e. If θ ranges over the
distinct eigenvalues with nonzero e-projection, put
w_θ=‖Proj_θ(e)‖²>0. Then ∑w_θ=1 and

    D_1/D_0 = x − ∑_θ w_θ/(x−θ).

The derivative of the right side is 1+∑w_θ/(x−θ)²>0 away from its poles.
Its numerator has exactly one simple zero in each intervening interval and
one in each exterior interval; no zero is a pole. Its denominator is the
square-free support polynomial. This also verifies gcd removal and avoids
confusing a repeated eigenvalue of the unreduced head with a repeated root
of a reduced P_n.

## 3. Literal identification of the source polynomials

Freeze the d−1 unchosen tails at length N, and extend the chosen one to N+s.
Let M_s(x)=Γ_(N,…,N,N+s)(x). By the established mixed-tail matrix formulas,
M_s=xI−A_s for some fixed real symmetric A=A_0^(full), a unit endpoint e,
and its ordinary unit-weight path extensions. Here A is minus the constant
part of M_0; the off-diagonal sign of a newly appended edge is immaterial,
because a diagonal ±1 similarity changes all path signs to +1.

By Proposition3.25,

    det M_s = F P_(N+s),   F=C P_N^(d−1).

F is a nonzero monic polynomial and is independent of s. Coprimality of
P_N and P_(N+1) implies

    gcd(det M_0,det M_1)=F.

On the other hand the cyclic-compression lemma identifies that same monic
gcd with g=charpoly(A|K^⊥). Thus **F=g**, and cancellation in ℝ[x] gives

    P_(N+s)=q_s   for every s≥0.

There is no assumption here that F and P_N are coprime; they need not be.
Only coprimality of consecutive reduced P's is used, and multiplicities are
retained in the common factor F.

The source series is fixed in all integer indices by its recurrence, so

    P_(N−1)=xP_N−P_(N+1)=xq_0−q_1=q_(-1).

This explicitly handles the conjecture's k=−1 boundary. All P_(N+k) for
k≥−1 are therefore characteristic polynomials of irreducible Jacobi matrices,
or the constant 1 in the dimension-zero boundary case. They are square free
and real-rooted. No interpretation of P_(N−1) as a physical standard module
is required.

## 4. Eventual stability of exterior root counts

For s≥0 let h_s^+ and h_s^- count eigenvalues of J_s strictly above 2 and
strictly below −2, respectively. Strict interlacing implies both sequences
are nondecreasing: each already exterior eigenvalue forces an exterior
eigenvalue of the next, larger principal extension.

The s newly appended vertices induce the path adjacency matrix T_s, whose
eigenvalues are 2cos(jπ/(s+1)), j=1,…,s, all in (−2,2). It is a principal
submatrix of J_s of codimension r. Cauchy interlacing therefore implies

    0≤h_s^+≤r,  0≤h_s^-≤r.

Each bounded nondecreasing integer sequence is eventually constant. Their
sum, which is exactly the number of roots of P_(N+s) outside [−2,2], is
therefore eventually constant. This proves the second source assertion,
without claiming an explicit stabilization index or any particular exterior
count. Roots exactly at ±2 are treated correctly by the strict inequalities.

## 5. Density in the full closed interval

For any nonempty open interval I⊂(−2,2), the number of eigenvalues of T_s
in I tends to infinity as s→∞, by the explicit cosine formula. Cauchy
interlacing for its codimension-r embedding into J_s shows that the counts
in any interval differ by at most 2r (the sharper r is unnecessary).
Hence J_s has an eigenvalue in I for every sufficiently large s.

Thus the union of the zeros of P_(N+s) in [−2,2], s≥0, meets every open
subinterval of (−2,2). For either endpoint and any epsilon>0, choose 0<delta<min(epsilon,1).
The interval (2−delta,2−delta/2) lies inside the band and contains a root
for all sufficiently large s, at distance less than epsilon from2; likewise
(−2+delta/2,−2+delta) supplies a root near−2. Thus its closure contains
both endpoints, proving density in [−2,2] exactly as Conjecture4.5.1 requests. The same reasoning
gives a stronger known-mechanism consequence: the empirical zero measures
converge to the arcsine law on [−2,2], with only boundedly many exterior
zeros. This consequence is **not separate discovery credit**.

## 6. Status, risks, and formal scope

This is a prospective complete source-conjecture resolution, one outcome
only. All generic cyclic-compression, Jacobi, and interlacing results are
classical; the proposed contribution is the identification in §3 and the
full consequence for the source's arbitrary-partition question. An
independent eligibility/novelty review must decide whether it is a genuinely
unresolved application or is already explicitly/immediately subsumed by
existing work. No count is claimed from an empty MathDB record or search.

Load-bearing checks for an adversarial reviewer:

- M_s really is a fixed real symmetric head plus ONE scalar unit-weight
  tail, after all other Specht-component tails are frozen. Source3.2.17
  and3.25 supply exactly this; a scalar surrogate replacing all d tails
  simultaneously would not suffice.
- Removal of the monic gcd must include multiplicities. Repeated eigenvalues
  in the full head are not themselves an obstruction, and F may overlap P_N.
- Cyclic compression must retain e at the attaching endpoint, which yields
  q_(-1) and handles k=−1 without an added hypothesis.
- No theorem is claimed merely for fixed l, a row/column/hook partition,
  bounded degree, or a numerical list: the proposed argument is universal.
- Formalizing a generic head-tail theorem alone is not yet a complete literal
  source endpoint. The actual source identification, all quantifiers, the
  boundary index, and the two asymptotic clauses need an honest Lean bridge.

Independent preliminary review supports SOURCE/MATH and bounded NOVELTY/
ELIGIBILITY, with its access limits documented. The parent has14 strictly
replayed classical Jacobi supporting declarations, not a full source endpoint.
No manuscript, final review, packet, or extracted replay yet. Credit remains0.
