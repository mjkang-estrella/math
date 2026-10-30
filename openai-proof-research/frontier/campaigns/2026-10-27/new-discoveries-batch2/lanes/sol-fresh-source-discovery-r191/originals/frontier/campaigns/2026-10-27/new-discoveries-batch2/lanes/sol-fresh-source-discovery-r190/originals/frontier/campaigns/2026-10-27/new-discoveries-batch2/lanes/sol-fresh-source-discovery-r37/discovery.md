# r37: bivariate Hahn irreducibility remains unresolved

Credit 0. No candidate nomination, acceptance, count change, or Lean investment.

## Primary target and exact scope

Iliev–Xu, *Hahn polynomials for hypergeometric distribution*, arXiv:2012.12168v1,
22 December 2020, pp19–20, Conjecture4.5. The current arXiv landing page lists
only v1 and gives Adv.Appl.Math.139(2022),102364,34pp,
DOI10.1016/j.aam.2022.102364. The publisher article endpoint returned403;
the DOI landing page is only a redirect, not the published article. Published-version
comparison remains HOLD. Both authors' current publication lists link this paper;
no later title explicitly resolving this question was identified in those lists.
That is bounded followup coverage, not an assertion that no followup exists.

For positive integers n,a,b with n<=min(a,b), set

R_n(x;a,b,y) = sum_{k=0}^n
 (-n)_k (n-a-b-1)_k (-x)_k (-y+k)_{n-k} / ((-a)_k k!).

Here (z)_k is the rising factorial. The denominator is nonzero for k<=n<=a.
The literal ambient ring in the primary body is Q[x,y]. The question is whether
R_n is irreducible unless a=b and n is odd; in that case the source predicts
(y-2x) times an irreducible degree n-1 polynomial, up to a rational unit.
The n=1 constant residual factor is not investigated as an endpoint issue.
The source's reflection identity explicitly supplies the exceptional linear factor.
The full all-n,a,b statement, including irreducibility of the residual exceptional
factor, remains open in this lane. No finite specialization resolves it.

## Screen of actual statements and early prior-body checks

1. Selected Hahn Conj4.5, with its definition, symmetry identity, surrounding
factorization examples and proposed Eisenstein discussion actually read.
The source's Example2.5 gives reducible **univariate fixed-N** Hahn polynomials;
these do not refute the bivariate conjecture. The 1707.03843 companion's §2
constructs the hypergeometric orthogonal basis and its lattice conditions; it
is not an all-parameter bivariate irreducibility theorem.
2. Grosset–Veselov math-ph/0508066, §5 Definition(21), Propositions6/7,
§7 Conjecture2: the elliptic Bernoulli periods admit the indicated alternating
coefficient-positive pair of g2,g3 polynomials. Proposition4 already establishes
positivity for the power periods K_n; derivative-square periods have additional
signed terms, so simply invoking Proposition4 is insufficient. This was screened,
not selected; no positivity theorem or counterexample is claimed.
3. Costas classification, published2015 Conjecture4.4 and Corollary4.2 in the
author-hosted PDF: already screened in r34, so excluded from further work.
A larger factorial census is not a new mechanism.
4. clopen OP-00215: full reduced degrees 2d and 6(d-1) for isotropic/nonisotropic
Rayleigh–Ritz discriminants. The actual pinned Colbrook TR-26 manuscript
Theorem1 and binary-Wronskian correspondence/proof bodies give precisely
these degrees. Public11September2026 claim, earlier than this lane; no rediscovery.
5. clopen OP-00231: all-order pole-free |z|<=3 bound |1-r_m(z)|<=2 for diagonal
Pade approximants to cosh(sqrt z). Actual pinned Colbrook MF-03 Theorem1,
Schur-denominator formula, tail-bound mechanism and finite-range treatment
read. Full public11September2026 claim; no rediscovery or truth audit.
6. MathDB377060 Umemura identity has a posted explicit public counterexample.
Excluded before investment; not nominated and not independently certified here.
Gregory405418 was only a reconnaissance listing, not a cleared primary target.
The Gatzweiler–Krattenthaler lead was immediately recognized as prior r23;
its unavailable HTML endpoints did not justify returning to that family.

Closest classical body: Cullinan–Hajir–Sell2009, correct DOI10.5802/jtnb.659,
Theorems1.1/1.2 and Proposition3.1. It proves results for
J_n(x,t)=sum binom(t+j,j)x^j and a transformed family whose reduction at t=0
is a pure power, enabling Eisenstein. The full body does not give the selected
R_n. Its almost-all rational-specialization theorem cannot imply the required
all integer (a,b) assertion. No valid transformation identifying these families
was obtained. An initial erroneous DOI658 download is retained but not relied on.

## Route 1: leading homogeneous form; exact obstruction

Write H_n for the degree-n homogeneous part of R_n. It is

H_n=(-1)^n sum_{k=0}^n [(-n)_k(n-a-b-1)_k/((-a)_k k!)] x^k y^{n-k}.

If H_n is irreducible over Q, then R_n is irreducible: a nontrivial polynomial
factorization induces one of its highest homogeneous part (degrees add in a
domain). This is a useful sufficient condition, not an all-parameter proof.

On the perfectly admissible diagonal a=b=n, cancellation of (-n)_k and the
finite binomial theorem give the **all-order identity**

 y H_n(x,y) = x^(n+1) - (x-y)^(n+1).

Indeed (-(n+1))_k/k!=(-1)^k binom(n+1,k); summing k=0..n is the full
(n+1)-st binomial expansion with its last term removed. The change of variables
u=x,v=x-y is invertible over Q. Thus H_n is the product of the homogenized
cyclotomic factors Phi_d(u,v), d|n+1,d>1. For n=9^r-1, r>=1, n is even,
so there is **no** permitted odd-symmetry exception, while H_n has at least
two positive-degree rational factors. This defeats a uniform proof based
solely on irreducibility of H_n. It does NOT prove R_n reducible.

For example n=a=b=8 gives

H_8=(3x²-3xy+y²)
 (3x⁶-9x⁵y+18x⁴y²-21x³y³+15x²y⁴-6xy⁵+y⁶).

The bounded exact factor check reports R_8 itself irreducible over Q. This
finite computation corroborates the distinction, without proving the conjecture.

## Route 2: lattice and boundary constraints; insufficient on their own

Every R_n vanishes at (i,j) for 0<=i<=j<n. In a summand with k>i, (-i)_k=0;
with k<=i<=j, (-j+k)_{n-k} contains zero. Moreover

R_n(0,y)=(-y)_n,
R_n(y,y)=C(-y)_n, C=(-1)^n(-b)_n/(-a)_n,

the second being the primary reflection identity at x=0. These are substantial
interpolation constraints but do not imply irreducibility. For any n>=2 and the
same nonzero C,

F(x,y)=(-1)^n (y-(1-C)x) product_{j=1}^{n-1}(y-j)

is reducible and satisfies **both** boundary values and every triangular-grid
zero. Its leading form generally differs from H_n, so this is a failed-invariant
example, not a source counterexample. The exact checker uses even n=4,a=4,b=5.
For general n the displayed (-1)^n factor is necessary to match (-y)_n.

Combining the complete leading form with all grid constraints uniquely
specifies the polynomial: a degree<=n-1 difference vanishing on this triangular
grid is zero, by restricting successively to y=n-1,n-2,...,0 and factoring those
horizontal lines. This observation explains why arbitrary interpolation
perturbations cannot preserve all the information. It supplies no irreducibility.

## Route 3: specialization and direct Eisenstein transfer fail

A full-degree irreducible specialization in y would imply bivariate
irreducibility, but the tempting uniform y=-1 choice fails. The admissible
nonexceptional case n=2,a=2,b=8 is

R_2=36x²-9xy-27x+y²-y,
R_2(x,-1)=2(3x-1)(6x-1).

The bivariate polynomial remains irreducible: its discriminant as a quadratic
in x is -63y²+630y+729, with two distinct roots, hence is not a square in Q(y).
Leading coefficient36 is a rational unit; Gauss's lemma applies. The example
is an obstruction to this specialization strategy, not a source refutation.

The direct classical Eisenstein-at-x=0 imitation also fails: reduction of R_n
modulo x is (-y)_n, with n distinct roots. No affine translation of y can turn
that into the pure nth power needed for a totally ramified Eisenstein reduction
when n>=2. Other primes/coordinate changes have not been ruled out.

## Route 4: projective smoothness, still a viable but unproved bridge

A smooth projective plane curve of positive degree is geometrically irreducible:
distinct positive-degree components meet over an algebraic closure by Bezout,
creating singularities. One could apply this to R_n outside the symmetry case,
and to the residual factor in that case. Five capped exact diagnostic examples
(n,a,b)=(3,3,4),(4,4,4),(4,4,5),(5,5,6),(6,6,6) have affine gradient ideal(1)
and squarefree binary leading form, hence smooth projective closure. No argument
excludes affine singularities uniformly, and no proof for the exceptional residual
family was found. An arithmetic irreducible curve can be singular, so a singularity
alone would not refute the actual source question. Do not launch a larger smoothness
census as a substitute for the missing uniform mechanism.

## Strongest objection / falsifier / formal feasibility

The hardest unproved step is a uniform irreducibility mechanism for all admissible
(a,b,n), particularly when the leading form factors and in the odd symmetric
residual family. A factorization R=A B in Q[x,y] with both degrees positive outside
the source exception, or two nonconstant residual factors inside it, would be an
in-scope falsifier. None was found. The diagnostic grids cannot exclude one.

A fixed rational factorization would be practical to formalize by coefficient
identities plus positive-degree witnesses; a universal smoothness/monodromy proof
would require substantial algebraic geometry. There is presently no complete
ordinary endpoint to formalize. No PROOF.md, helper Lean, new axiom, paper,
formal certification, or request for acceptance was produced. Independent root
review must precede any substantial formal investment.
