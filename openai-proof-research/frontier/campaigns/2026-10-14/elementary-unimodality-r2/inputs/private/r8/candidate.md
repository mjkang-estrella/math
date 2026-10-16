# Elementary unimodality: structural discovery r8, unresolved

Myeongjin Kang; no affiliation. 2026-10-16.
Original prose CC BY 4.0; original code MIT. Private third-party sources
retain their original rights.

**Disposition: UNRESOLVED.** The frozen full target U is neither proved nor
refuted. No theorem is nominated as a substantial campaign result. This is
a research report, not a manuscript or independent review. The campaign
count remains 4/10. H and B were not pursued.

## 1. Full original target

For every n>=1 and every weakly increasing integer function h on [n] with
i<=h(i)<=n, let G have the edges {i,j} with i<j<=h(i), and put M=|E(G)|.
For a proper coloring f:[n]->positive integers set

    asc_G(f)=#{i<j<=h(i): f(i)<f(j)},
    X_G(x;q)=sum_(f proper) q^(asc_G(f)) product_i x_(f(i)).

This is a symmetric function. For every partition lambda of n, define

    c_(G,lambda)(q)=[e_lambda]X_G(x;q)=sum_(d=0)^M a_(lambda,d)q^d.

**U:** for every such n,h,lambda, the coefficients satisfy

    a_(lambda,d)=a_(lambda,M-d)       (0<=d<=M),
    a_(lambda,d+1)>=a_(lambda,d)     (integers 0<=d<M/2).

The middle comparison for odd M is an equality by symmetry. This is the
remaining elementary-unimodality part of the Shareshian–Wachs conjecture,
not a newly invented question. All sizes, partitions, zero coefficients
and disconnected graphs are retained. Elementary nonnegativity is already
a stipulated pinned theorem. Schur-unimodality, unimodality after summing
over partitions, or a special family would not resolve U.

Scope was frozen in original-scope.md before proof work. Catalogue screening
included algebraic Betti/saturation families, but no claims about their
theorems were used. Family 169 was selected after reading its actual
statement and its explicit exclusion of unimodality. The complete pinned
preprint tree was searched for chromatic-quasisymmetric/Hessenberg/theta
companions; this mathematical family has one manuscript directory. Other
hits concern unrelated chromatic homotopy or graph coloring.

## 2. Exact source interface

The stipulated input is *Elementary Positivity of Chromatic Quasisymmetric
Functions*, openai/math at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb.
All ten retained TeX/bibliography/README blobs match the complete pinned
tree. Only the exact reading extents in source-contracts.md are claimed.
Upstream truth is accepted, not re-audited.

The main theorem gives a partition-valued rule theta_G on graph-nondescent
permutations and

    X_G(x;q)=sum_sigma q^(ginv_G(sigma)) e_(theta_G(sigma))(x).

The source also gives an abstract degreewise decomposition of Hessenberg
cohomology into Young permutation modules M^lambda, whose multiplicities
are a_(lambda,d). It explicitly supplies no preferred isomorphism or
compatibility with multiplication.

The more useful lower interface is the source's triangular chart. It has
anchors d_1,...,d_D at integer times and bridges b_(j,i) at times
i+theta_(j,i), with 1<=j<=i<=D-1. Phases increase by decreasing row j,
then increasing level i within each row. Edges join times differing by
less than one. If a precedes b, set Omega(b,a)=1 on an edge and zero on a
nonedge. The torus uses X_a X_b=v^(Omega(a,b))X_(a+b).

The **simple scattering roots are forward differences of consecutive
vertices**, not the vertex vectors themselves. Write C for these roots;
they form a basis of the total-weight-zero lattice. Each carries
D_p=product_(j>=0)(1+v^(-1-2j)X_p). The completed wall system and sections
are defined by the source's incoming-coefficient conditions. In particular,
A_n(Theta_m)=delta_(n,m).

For an embedding of G among selected bridges, let u be their sum, pad
lambda to length D, and set x_lambda=sum_i lambda_i d_i. The exact identity
in the all-negative chamber is

    P_(G,lambda)(v):=[X_u]Theta_(x_lambda)
                   =v^(-M)c_(G,lambda)(v^2).                 (2.1)

This follows from graph:kernel, graph:reciprocity and tri:monomial, and is
stated explicitly in tri:positivity. Thus the source has already paid the
ambient embedding, shape selection, parity and normalization. Merely
repeating its theta identification would not be a new contribution.

## 3. The exact missing inequality

Let [r]_v=v^(-r+1)+v^(-r+3)+...+v^(r-1), r>=1. Call a Laurent polynomial
Lefschetz if it is a finite nonnegative integer combination of these
centered strings; zero is allowed.

For a symmetric polynomial c(q)=sum_(d=0)^M a_d q^d, put a_-1=0. Direct
telescoping gives the unique expansion

    v^(-M)c(v^2)
      =sum_(d=0)^floor(M/2) (a_d-a_(d-1))[M-2d+1]_v.         (3.1)

To verify it, at exponent 2j-M in the lower half, the strings with d<=j
contribute sum_(d=0)^j(a_d-a_(d-1))=a_j; symmetry pays the upper half.
The largest remaining outer exponent recursively determines every string
coefficient, proving uniqueness. Therefore U is **exactly** the assertion
that every target coefficient in (2.1) is Lefschetz. This equivalence is
elementary and is not presented as progress resolving U.

Here is a sufficient propagation statement, with its hypothesis unpaid.
The source's wall:recursion writes a coefficient at exponent n in chamber H
as its incoming coefficient plus terms

    J_i(n-jp_i,j) [X_(n-jp_i)]F(I_i),  j>0.                 (3.2)

Only a finite cone interval is involved, every predecessor is strictly
smaller, and the number of crossings at the required truncation is finite.

**Conditional lemma.** If every J_i needed on that interval is a finite
Lefschetz polynomial, then coefficients of every Theta_m on that interval
are finite Lefschetz polynomials.

**Proof.** Incoming coefficients are zero or one. Finite sums of Lefschetz
polynomials are Lefschetz. Their products are too: explicitly
[a]_v[b]_v=sum_(j=0)^min(a,b)-1 [a+b-1-2j]_v, as is checked by comparing
coefficients. Induction on the sum of nonnegative C-coordinates in (3.2)
therefore proves the claim. Every step is finite; no infinite sum of strings
is being silently converted into a finite one. ∎

The pinned theorem pays positivity of J_i in a Laurent-series completion,
not the displayed stronger hypothesis. Its finite polynomial conclusion
for (2.1) alone does not supply that hypothesis. Proving it for all relevant
cyclic charts, or finding a more selective proof of (3.1), is the unpaid
mathematical step. It is not inserted as an axiom.

## 4. A direct acyclic-scattering application fails in the actual roots

Davison–Mandel's primary Theorem 2.18 establishes Lefschetz wall factors for
unit incoming data when the skew matrix **of the incoming vectors** is
acyclic. Their Lemma 3.5 gives Lefschetz coefficients for the corresponding
positive monomial adjoints. Their general Lefschetz extension is recorded
as Conjecture 2.17, distinct from general positivity. Section 3 also
distinguishes ordinary broken-line theta functions from the weaker
pre-Lefschetz conclusion. These exact interfaces were read directly.

The vertex skew matrix of every ordered graph is acyclic. Applying that
observation to the source's scattering system uses the wrong vectors.
The following is a rigorous all-chart obstruction to this direct route.

**Lemma.** For every triangular chart with D>=3, its forward-gap skew
matrix has the principal block

     0 -2  0  1  0
     2  0 -1 -1  1
     0  1  0 -1 -1
    -1  1  1  0 -1
     0 -1  1  1  0.                                      (4.1)

In particular it is not acyclic, regardless of the permitted phases.

**Proof.** The first six vertices in time order are

    a0=d1, a1=b11, a2=d2, a3=b22, a4=b12, a5=d3.

The phase prescription gives theta22<theta11<theta12. Their edges are
exactly

    01, 12, 13, 23, 24, 34, 35, 45.

For instance b11 is adjacent to b22, but not b12, by the two phase
inequalities; b22 and b12 are on one level. Edges involving the anchors
follow immediately from the integer times. These assertions do not depend
on other bridges. With p_i=a_(i+1)-a_i for 0<=i<=4, bilinearity gives

    Omega(p_i,p_j)=Omega(a_(i+1),a_(j+1))-Omega(a_(i+1),a_j)
                  -Omega(a_i,a_(j+1))+Omega(a_i,a_j),

which is (4.1). Its entries B01=-2, B13=-1 and B30=-1 give a directed
three-cycle under either global orientation convention. ∎

Adding directions to make the form nondegenerate leaves this induced
cycle intact. Replacing the root cone by the vertex cone changes the
incoming wall data: the former roots have total weight zero, whereas the
latter have weight one. No equality of the two scattering problems was
proved. A coordinate change preserving the prescribed vectors and form
cannot change their pairings in (4.1).

This does **not** prove that the charts are mutation-cyclic. An exact
bounded search on (4.1) found no acyclic matrix within mutation depth ten
and entry bound ten, visiting 21,092 labelled matrices. A separate depth
eight/entry six search found no Markov 2,2,2 triangle. Every four-root
principal deletion did have an acyclic mutation in a small search. None
of these finite observations is an all-mutation result. In particular no
non-mutation-acyclicity or impossibility theorem is claimed.

Even a future acyclic mutation route must preserve the target coefficient
or its Lefschetz property under the chart change. Mutation compatibility
alone is not an assertion that an individual old-chamber coefficient
retains a new-chamber Lefschetz decomposition.

## 5. Hard Lefschetz plus degreewise permutation modules is insufficient

The other attempted route combined the pinned degreewise decomposition
with the older equivariant hard Lefschetz operation. Here is an exact
countermodel to that **abstract inference**, not to U.

Let the group be S_3, T its trivial representation, and W its standard
two-dimensional representation. Then

    M^(3)=T,       M^(2,1)=T direct-sum W.

For example their characters on identity, transposition and three-cycle
are (1,1,1), (3,1,0) and (2,0,-1), respectively. Define

    V_0=T,        V_1=M^(2,1),       V_2=T.

Choose trivial basis vectors a,b,c in consecutive degrees and set
L(a)=b, L(b)=c, L(W)=L(c)=0. It commutes with S_3 and L^2:V_0->V_2 is an
isomorphism. This is a centered Lefschetz string plus W in the middle, so
the complete degreewise Lefschetz condition holds. All V_d are Young
permutation modules. Nevertheless their h_3 coefficient is 1,0,1, which
fails unimodality. Equivalently the middle primitive representation is
W=M^(2,1)-M^(3): Schur positive, with a negative Young coefficient.

This example can also carry an equivariant graded Poincaré algebra, so
adding a formal cup product alone does not repair the inference. Take a
as unit, c as top degree, b^2=c, bW=0, and ww'=-<w,w'>c for an invariant
nondegenerate form on W. Higher products vanish. Associativity follows
from grading, the pairing is nondegenerate, and multiplication by b is
the stated L. No claim is made that this algebra is actual Hessenberg
cohomology. Its purpose is to expose the missing geometric specificity.

The original Shareshian–Wachs proof operation concludes Schur-unimodality
from equivariant hard Lefschetz. That operation is valid and credited.
The pinned positivity theorem supplies Young permutation modules in each
degree, but it supplies no Young-positive description of the primitive
Lefschetz quotients. Those quotients are the exact extra information
needed. Replacing them by their dimensions would discard the partition
quantifier in U.

There is another weaker-property trap. For odd r put
P_r(v)=v^(r-2)+v^r, the primary paper's pre-Lefschetz generators. Then

    P_-3+2P_-1+2P_3+P_5
      =v^-5+3v^-3+2v^-1+2v+3v^3+v^5.                      (5.1)

It is positive, bar invariant, parity pure and has no support gaps, but
its coefficients 1,3,2,2,3,1 are not unimodal. Thus even transferring
general pre-Lefschetz positivity from standard theta functions would not
pay (3.1). No such transfer is assumed in this report.

## 6. Other source mechanisms examined

The source packet switch matches finite sets at **one fixed energy**. Its
exact-mask refinement follows alternating paths in finite matchings,
again preserving that energy. Neither interface compares neighboring
degrees. A degree-raising injection preserving the final partition was
not obtained from these operations.

Likewise the insertion-digit bijection gives a product of chains for the
entire admissible permutation family. It does not assert that the
partition fibers of theta_G are unions of centered chains. Forgetting the
partition may yield unimodality of a total enumerator, which does not
imply U.

The source's positive domination of a monomial section by a multiple of
U^N provides finite support, not monotonicity of coefficient differences.
Even two nonnegative palindromic polynomials with common center can obey
1+q^2 <= 1+q+q^2 coefficientwise while only the latter is unimodal.
No use of domination was found that pays the first differences in (3.1).

## 7. Exact computations and their scope

checks.py constructs every nondecreasing Hessenberg sequence through n=6.
For each partition mu it computes the coefficient of the particular
monomial x_1^(mu1)...x_r^(mur) by recursively choosing ordered independent
color classes of those sizes, adding ascents exactly once per edge.
It computes the elementary-to-monomial conversion independently by
expanding products of elementary polynomials in ordinary variables, then
uses rational matrix inversion. Every output is integral and reconstructs
every input monomial coefficient. Selected reversed color-size sequences
give 68 additional symmetry checks. Four negative controls are included.

The run checks 196 graphs, 1,836 elementary polynomials and 5,543 lower-half
comparisons. No counterexample appears. Its aggregate exact-enumeration
digest is c8b3ada345f8b25a2382326e8ec3eec426fa6b7cd2bda2c60287954cfa5934d3.
The receipt also records all coefficients for the six-vertex chart with
h=(2,4,5,6,6,6). Five rational triangular charts check (4.1), and exact
character and polynomial checks reproduce Sections 5's obstructions.

mutation_probe.py reproduces the bounded searches and their scope. It
checks involutivity of the mutation formula; it performs no floating-point
optimization. These searches are not an isomorphism census. They do not
establish mutation-cyclicity, and no finite check proves U.

## 8. Contribution and remaining work

A full proof of U would settle an explicitly stated primary conjecture
beyond the stipulated positivity result. The bounded primary screen did
not supply such a proof. No worldwide-priority claim is made. The broad
quantum-scattering Lefschetz extension read in Davison–Mandel is a
conjecture; its acyclic theorem has a hypothesis violated by the actual
source roots. Calling the target a routine application would leave that
gap unpaid.

Conversely, the results actually proved here are elementary structural
diagnostics: a five-root skew calculation, an abstract representation
countermodel, a pre-Lefschetz example, and conditional finite induction.
They are technical supporting work, not substantial frontier nominations.
No independent proof or contribution PASS is claimed. No manuscript or
Lean packaging was attempted.

The remaining full task is to prove the nonnegative first differences
in (3.1) for every target (2.1), or to give one exact graph/partition/degree
violating them. A sufficient stronger route is Lefschetz-positive jumps
in the relevant gap-chart intervals. A geometric alternative must show
Young-positive primitive Lefschetz quotients, not just degreewise Young
permutation decompositions. Neither assertion was established here.

All writes were within the assigned r8 directory. No nested agent,
shared-index or sibling edit, staging, commit, upload, external message,
submission or publication occurred. Parent integrates. Private source
copies are not relicensed. The manifests, detached seal and read-only
verifier authenticate bytes and replay finite diagnostics only; they
are not mathematical signatures or independent certification.
