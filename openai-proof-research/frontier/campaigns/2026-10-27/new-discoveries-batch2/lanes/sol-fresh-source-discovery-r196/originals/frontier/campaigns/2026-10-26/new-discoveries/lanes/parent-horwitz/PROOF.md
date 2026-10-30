# Proposed all-dimensional identification of Horwitz's osculating mean

Credit0. This is a complete mathematical proposal, with no Lean certificate,
independent eligibility verdict or novelty PASS yet. Its final interpolation step
is classical. The exact osculating-plane calculation, not a new interpolation
theorem, is the proposed resolution of the explicit source question.

## Source statement

Horwitz, arXiv:1404.1489, Conjecture1, p.19. The published J. Classical Analysis
4(1) (2014), 41–61, DOI10.7153/jca-04-02, p.61, retains the same unnumbered
conjecture. For the curve alpha(t)=(t,t^2,...,t^(n-1),log(t)) and pairwise distinct
positive nodes a_i, let P=(y_1,...,y_(n-1),z) be the intersection of its n
osculating hyperplanes. The associated last-coordinate mean is exp(z). The source
asks whether it equals the Xiao–Zhang multivariate identric mean

    exp(sum_i a_i^(n-1)*log(a_i)/prod_(k!=i)(a_i-a_k)-H_(n-1)).

This is the source Vandermonde-minor expression written in barycentric form.
The source explicitly credits the three-variable case as already known. We seek
ONE all-dimensional outcome, not separate credit for that case or the helpers.

## 1. The exact osculating hyperplane

Put m=n-1>=1 and H_m=sum_(k=1..m)1/k. Define

    C_j=(-1)^(j-1)*binomial(m,j)/j,  1<=j<=m.

Every C_j is nonzero. The Taylor polynomial of log(t) about a>0, through degree m,
is

    T_a(t)=log(a)+sum_(k=1..m)(-1)^(k-1)*(t/a-1)^k/k
          =log(a)-H_m+sum_(j=1..m)C_j*t^j/a^j.             (1)

To check the constant use sum_(k=1..m)(-1)^(k-1)*binomial(m,k)/k=H_m,
which follows by integrating [1-(1-u)^m]/u on [0,1]. The coefficient of t^j is
(-1)^(j-1)*sum_(k=j..m)binomial(k,j)/k. The identity
binomial(k,j)/k=binomial(k-1,j-1)/j and the hockey-stick sum give C_j.

It follows that the osculating hyperplane at a is precisely

    z=log(a)-H_m+sum_(j=1..m)C_j*y_j/a^j.                (2)

Here is an explicit bridge to the source's Wronskian definition. The functional
normal v_a=(-C_1/a,...,-C_m/a^m,1) annihilates alpha'(a),...,alpha^(m)(a),
because log(t)-T_a(t) has zero derivatives through order m at a. These m tangent
vectors are independent: their first m coordinates form the triangular derivative
matrix with diagonal 1!,2!,...,m!, whose determinant is nonzero. Thus their
annihilator is one-dimensional. The source cofactor normal belongs to this
annihilator (Laplace expansion with a repeated row); its last component is
(-1)^(n+1)*prod_(j=1..m)j!, hence is nonzero. It is exactly that nonzero scalar
times v_a. Therefore the source's hyperplane equation and (2) are equivalent,
not merely tangent at some order or conditionally identified.

## 2. Intersection as ordinary polynomial interpolation

For coordinates (y_1,...,y_m,z) introduce

    Q(t)=(z+H_m)*t^m-sum_(j=1..m)C_j*y_j*t^(m-j).        (3)

Multiplying (2) by a_i^m shows that membership in all n=m+1 hyperplanes is
equivalent to Q(a_i)=a_i^m*log(a_i) for every i. Conversely, (3) is a bijection
from R^n to polynomials of degree<=m: the leading coefficient determines z and
each lower coefficient determines its unique y_j since C_j!=0. Ordinary Lagrange
interpolation at n distinct real nodes therefore proves existence and uniqueness
of the actual intersection point, without relying on an unverified Chebyshev
system hypothesis.

The interpolating polynomial is

    Q(t)=sum_i a_i^m*log(a_i)*prod_(k!=i)(t-a_k)/(a_i-a_k).

Taking its coefficient of t^m gives

    z+H_m=sum_i a_i^m*log(a_i)/prod_(k!=i)(a_i-a_k).       (4)

Exponentiating (4) proves the conjectured mean identity for every n>=2.
The barycentric weights equal the source signed Vandermonde-minor ratios,
(-1)^(n+i)*V_i/V=1/prod_(k!=i)(a_i-a_k), by cancellation of the factors involving
a_i. Thus the exact source displayed expression is recovered as well.

## 3. The last coordinate is indeed a strict mean

For completeness, let f(t)=t^m*log(t), and let Q be its interpolating polynomial.
The function f-Q has n=m+1 distinct zeros in the positive interval between the
smallest and largest nodes. Applying Rolle's theorem m times gives a point xi
strictly between those endpoints with f^(m)(xi)=Q^(m)(xi). Induction gives

    f^(m)(t)=m!*(log(t)+H_m),   Q^(m)(t)=m!*(z+H_m).

Hence z=log(xi), so min(a_i)<exp(z)<max(a_i). This proves the relevant mean
property directly, including the two-variable base case. No assertion about the
other coordinate means is needed or counted.

## 4. Verification, formal scope, and novelty limits

The checker symbolically verifies (1) for dimensions2..12, then independently
computes the literal Wronskian cofactors and their intersection at distinct
positive nodes for dimensions2..8. Those finite checks support the reasoning;
they are not its universal proof.

A full Lean endpoint must define the actual derivative/cofactor hyperplanes,
prove the normal equivalence, existence and uniqueness of the intersection,
and identify exp(last coordinate) with the literal source Vandermonde expression.
An interpolation identity conditional on the unproved plane formula is insufficient.
No such Lean endpoint is claimed yet.

The original 1996 Horwitz construction paper is the closest subsumption risk.
Actual full text remains unavailable: the publisher PDF returns403, the public
Elsevier core endpoint returns metadata only, and view=FULL returns401. Its
abstract reports monomial curves and a different Pittenger logarithmic-mean
case, not this identity, but that is NOT a substitute for inspecting theorem
bodies. The 2014 published source still calls this an open conjecture. Initial
specific searches found no resolution; the stored OpenAlex record has zero
identified citing works, which proves no novelty. A bounded independent review
must still assess prior art and whether this short calculation is substantive
under the campaign standard. No priority or discovery claim at present.
