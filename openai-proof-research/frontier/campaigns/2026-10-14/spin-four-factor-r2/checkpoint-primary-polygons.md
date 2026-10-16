# Primary polygon and arity audit

Myeongjin Kang; no affiliation. Original prose CC BY 4.0; code MIT.
Third-party inputs private, original rights. Author research, no independent PASS.

The unchanged target remains Q4. This checkpoint supplies exact paid
reductions, not a proof that a suitable unscaled quadrilateral exists.

## KKM was actually read

Kapovich--Kumar--Millson, arXiv:math/0607454v1, Introduction,
Definition 1.3, Theorems 1.4--1.5 and 2.5, and the complete proof of
Theorem 5.3 were read in the original PDF's text representation.
The semigroup in Theorem 5.3 is explicitly a semigroup of TRIPLES.
The proof chooses a basis of the lattice of triples with root-congruent
sum, computes its Hilbert basis (82 elements, ten symmetry types), and
checks tensor occurrence on those generators. It invokes semigroup
addition in that same three-weight space. It does not establish an
integral common diagonal for a fourfold product. The quadrilateral
Gauss-map illustration in Section 2 concerns real polygon feasibility.
It is not an integer-diagonal lemma. Its source references KLM1--3 and
KM1--2 were followed below; the Maple notebooks were not executed.

## What KLM's polygon theorems actually preserve

KLM, arXiv:math/0406305v2, Main Theorem 1.1 and Theorems 1.2--1.4
have arbitrary polygon arity. Transfer Theorem 3.2, with its complete
proof, transfers refined side lengths between thick buildings modeled
on the SAME Euclidean Coxeter complex. It starts with an actual polygon,
transfers triangular subdivisions with their endpoint data, and uses
links to preserve straight angles. This is a paid gluing operation once
the refined data exist. It does not turn arbitrary real endpoint types
into special vertices. Addendum 3.3 enlarges the affine Weyl group; it
does not preserve a smaller lattice that was not present initially.

KLM, arXiv:math/0311486v3, Theorems 1.1--1.2, Section 5.2/Theorem
5.3 and Lemma 5.4 identify polygon side lengths in the infinitesimal
symmetric space with zero-sum compact-orbit data, and with the real
polygon cone. Zero labels are allowed (zero mass in the configuration).
No scale-one assertion about special building vertices is present in
these interfaces.

KLM, arXiv:math/0210256v4, Lemma 7.9 and Theorem 7.10 are the crucial
arithmetic boundary. With side labels in L and total in Q, the push map
can fix a VERTEX. A vertex is not necessarily SPECIAL. Theorem 7.16(2)
and Corollary 7.17(2) obtain special vertices after dilation by k_R.
Their proofs use multiplication of affine-alcove vertices by k_R and
the refined transfer theorem. In D_n, n>=4, k_R=2, from the coefficients
of the highest root. There are nonspecial vertices omega_i/2 at the
interior nodes 2<=i<=n-2. Replacing the word "vertex" by "special
vertex" would erase the precise operation still needed for Q4.

## A paid reduction using the stipulated triple theorem

Let G=Spin(2n) and H its adjoint Langlands dual, of type D_n, and let X
be the building of split H over a nonarchimedean local field. Its
cocharacter lattice is P(D_n); affine translations form Q(D_n). Fix a
special base vertex o. Write m(alpha,beta;t) for the nonnegative Hecke
structure constants and c(alpha,beta;t) for tensor multiplicities of G.

For every dominant integral alpha,beta,t,

    m(alpha,beta;t)>0  iff  c(alpha,beta;t)>0.                 (1)

The right-to-left implication is KLM Theorem 8.19, together with Lemma
8.5 to switch between output t and a triple invariant with t*. For the
other implication, the Hecke occurrence supplies a triangle of special
vertices, by Theorem 8.6. Its side labels satisfy the root congruence:
the class in P/Q of an oriented special-vertex edge is the difference
of its endpoint classes, since W acts trivially on P/Q. Their sum
around the triangle is zero. The triangle lies in the real triangle
cone by KLM's real-cone comparison. Rational moment/occurrence then
supplies some dilated triple invariant; stipulated thm:main supplies
the original triple invariant. This proves (1), with all spin cosets
and singular labels retained. No reverse Satake positivity principle
is assumed for general groups.

Both products have nonnegative coefficients. Associativity therefore
extends equality of binary SUPPORTS (1) to the support of every finite
product. Explicitly, a coefficient is positive precisely when there is
a finite sequence of intermediate labels for which all binary
coefficients are positive. The same sequence works in the other ring.
This operation uses an already integral intermediate sequence. It
does not create such a sequence from scaled data.

In particular, for any four original dominant integral labels,

    (V(a) tensor V(b) tensor V(c) tensor V(d))^G != 0
      iff there is a quadrilateral in X, with special vertices,
          having successive oriented side labels a,b,c,d.     (2)

One can also see (2) geometrically. Triangulate a special quadrilateral
from its first vertex. The diagonal t is a weight, and the two triangle
root congruences are automatic. Apply the stipulated triple theorem
to these triangles and contract V(t) with V(t*). Conversely, decompose
a fourfold invariant along an integral t, use KLM 8.19 to obtain its
two special triangles, then identify their common oriented edge.
KLM Lemma 8.7 (transitivity on a fixed vector-distance sphere), or the
refined transfer construction, justifies this identification. It is
not a demand that two independently chosen triangles happen to share
an edge in their original positions.

Scaled occurrence gives the original real polygon side data. Consequently
full Q4 is equivalent, relative to these paid interfaces, to:

    Every real-feasible P(D_n)-labeled quadrilateral with total in
    Q(D_n) has a realization with special vertices.            (3)

This is the geometric form of the same missing junction-coset theorem.
It does not follow from (1), associativity, or normality of the triple
semigroup. KLM 7.10 pays an affine vertex, not (3). KLM 7.16 pays the
dilated version of (3); this is a localization of the scale loss,
not a factor-two substitute for Q4 or a substantial nomination.

## KM's generalized paths do not erase the junction

KM, arXiv:math/0411182v2, Section 5.3 distinguishes LS1 and LS2.
Definition 5.11 requires a comparison between the terminal direction
of one piece and the initial direction of the next. LS2 imposes its
own local chain/regularity conditions. Theorem 5.21 and the proof of
Theorem 1.6/Proposition 7.1 use those conditions when replacing ONE
side by a sequence of fundamental pieces. They are not a free reset
between the independent factors b and c. The special-vertex conversion
in Section 7 still dilates by k_R. Theorem 7.4's minuscule-sum hypothesis
and special-vertex assumption must both be retained.

KM, arXiv:math/0508186v1, Section 2.6/Theorems 2.11--2.12 and their
proofs concern triples and these same building/path scale factors.
They do not supply (3). This bounded source reading establishes no
general impossibility of an arity reduction and no worldwide absence
claim. It identifies what these actual cited reductions pay.
