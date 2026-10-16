# Elementary unimodality U: focused second attempt, unresolved

Myeongjin Kang; no affiliation. 2026-10-16.
Original prose CC BY 4.0; original code MIT. Private third-party sources
retain upstream rights.

**Disposition: UNRESOLVED.** No full proof or counterexample to U is
obtained. No result is nominated or counted; the campaign remains 4/10.
The new support below is a finite, centered description of the wall jumps
that actually contribute to an elementary coefficient, and a precise
limitation of a cluster-monomial shortcut. These do not solve U, form a
replacement target, or constitute independent proof/contribution review.

## 1. Full original scope

For every n>=1 and weakly increasing integer h:[n]->[n] with
 i<=h(i)<=n, let G have edges {i,j} for i<j<=h(i), and put M=|E(G)|.
For every proper coloring f:[n]->positive integers set

    asc_G(f)=#{i<j<=h(i):f(i)<f(j)},
    X_G(x;q)=sum_f q^asc_G(f) product_i x_f(i).

For each partition lambda of n write

    c_(G,lambda)(q)=[e_lambda]X_G(x;q)=sum_(d=0)^M a_(lambda,d)q^d.

The full target U is

    a_(lambda,d)=a_(lambda,M-d)                    (0<=d<=M),
    a_(lambda,d+1)>=a_(lambda,d)                  (integer 0<=d<M/2).

All sizes, elementary partitions, disconnected graphs and zero
coefficients are retained. In odd total degree the middle comparison is
an equality by symmetry. This is the elementary-unimodality part of the
Shareshian--Wachs conjecture, not a newly named conjecture. The scope was
persisted before sustained proof work in original-scope.md. Pinned
positivity, total or Schur unimodality, a graph subclass, or a conditional
statement is not a solution.

The frozen r8 seal authenticates to SHA256
`6db6112bf4297450c063652b5cc415d8a4f2d20b8b5138753349fcbafbfd3600`.
All 24 inputs and 19 outputs, the exact 47-file tree including metadata,
and all ten pinned Git blobs were authenticated. No r8 program was
executed. Frozen originals were preserved. Input copies and source
contracts identify exactly what is reused.

## 2. Exact stipulated interfaces

The source is OpenAI, *Elementary Positivity of Chromatic Quasisymmetric
Functions*, at revision `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`.
Its theorems are accepted as instructed; none is audited for upstream
truth. The following interfaces, with their actual hypotheses, are used.

* `main:theorem`, `route:witness`: on all natural unit interval graphs,
  an individual partition-valued permutation rule gives each elementary
  coefficient as a nonnegative graph-inversion enumerator.
* `graph:digits`: admissible words have independent insertion digits
  0<=j_a<=l_a, with graph inversions sum_a j_a. It does not assert a
  centered-chain decomposition of any partition fiber.
* `graph:kernel`, `graph:reciprocity`: the graph-alphabet coefficient
  identity and partitionwise symmetry, including disconnected graphs.
* `wall:incoming-prescription`, `wall:three-factors`: normalized simple
  units and root-degree uniqueness of the entire wall system and its
  sign factorization. All coefficients needed at bounded root order
  are rational functions of v before their Laurent expansion.
* `wall:recursion`, `wall:positivity`: a coefficient is its incoming
  value plus finitely many positive jump series times coefficients at
  strictly lower free-cone exponents. Positivity is in N((v^-1)).
* `tri:embedding`, `tri:monomial`, `tri:positivity`: for an embedding
  among bridges, u their sum and x_lambda=sum_i lambda_i d_i,

      P_(G,lambda)(v):=[X_u]Theta_(x_lambda)^(H_-)
                      =v^(-M)c_(G,lambda)(v^2).           (2.1)

  The coefficient is a polynomial supported on -M,-M+2,...,M.
* `route:history-recursion`, `route:history-series`, `route:finite`:
  the common path choices depend on chamber/exponent, not on packet
  composition or energy. Histories have independent jump decorations,
  and their energy enumerator at terminal x_lambda is (2.1).
* `route:switch`, `route:exact`: the packet and exact-mask bijections
  preserve one fixed energy. Neither supplies an adjacent-energy map.
* `main:hessenberg`: each cohomological degree has an abstract Young
  permutation-module decomposition. The proof explicitly supplies no
  preferred isomorphism or cup-product compatibility.

Simple roots are the forward differences of consecutive chart vertices.
They are not vertex vectors. The r8 cyclic-root obstruction and abstract
S3 countermodel remain in force: the first does not prove global mutation
cyclicity, and the second is not actual Hessenberg cohomology. Neither
invalid inference is retried here.

## 3. Live histories have finite individual jumps

This is a supporting deduction in the actual source recursion. Fix G and
lambda, choose the finite source interval B={y:nd_1<=y<=u}, and all its
prescribed finite chamber/path data. If x_lambda is outside B its target
coefficient is zero by the support cone; there are no contributing
histories for it.

A skeleton node is a pair (H,y). An edge records a specified crossing in
the selected line for (H,y), its smaller predecessor z, and the recursive
state (I,z). Its weight is the **full** jump series

    J_e(v)=[X_y]W(X_z) in N((v^-1)) intersect Q(v).

Retain nonzero weights only. Every edge strictly decreases the sum of
free-cone coordinates of y-nd_1. Thus there are finitely many skeleton
paths, all with bounded length. Stop at incoming label x_lambda. An edge
is *live for this target* if it belongs to at least one complete path
from (H_-,u) to that label. This is a definition, not an assumed
positivity or unimodality property.

The source's energy-independent choices and jump decorations give

    P_(G,lambda)(v)=sum_(complete skeleton paths pi) product_(e in pi) J_e(v).
                                                               (3.1)

There are finitely many paths; each path product includes every choice
of its edge energies and indices. No matching constraints between the
energies on distinct edges have been added. This last point is needed
for the following argument.

**Finite-jump lemma.** Every live J_e is a finite Laurent polynomial
with nonnegative integer coefficients. If P=0 there is no complete
nonzero path and hence no live edge.

*Proof.* A product of nonzero series in N((v^-1)) is nonzero. Each path
product is bounded coefficientwise by P, because (3.1) has no negative
terms. Fix one path containing e and one nonzero monomial in every other
factor on that path. Their product has some fixed degree b and positive
integer multiplicity. If k is in the support of J_e, the degree k+b
occurs in the path product and in P. Since P is supported in the finite
interval [-M,M], k lies in the finite interval [-M-b,M-b]. Its coefficient
is finite by the source Laurent-series contract. This proves finiteness.
The zero-target assertion follows from absence of cancellation. The
empty path, when present, has weight one and causes no exception. ∎

This conclusion concerns live edges, not all walls or even all edges of
the ambient cone interval. It is derived from the pinned finite target,
not inserted as a new hypothesis. It strengthens the working interface
but supplies no coefficient monotonicity.

## 4. The live polynomials are centered and parity pure

One must not apply v->v^-1 to an arbitrary one-sided Laurent series.
Instead work over Q(v), where the source constructs each coefficient,
and complete only in root degree. At each bounded root order all
coefficient operations below are finite rational operations.

Define the anti-involution

    bar(v)=v^-1,   bar(X_a)=X_a,   bar(FG)=bar(G)bar(F).

It respects X_a X_b=v^Omega(a,b) X_(a+b). For the normalized unit
D_p=product_(j>=0)(1+v^(-1-2j)X_p), its logarithm at X_(jp) is

    (-1)^(j+1) / (j*(v^j-v^(-j))).

This changes sign under bar, so bar(D_p)=D_p^-1 as a root-completed
rational identity. In particular it is not a statement about reversing
an infinite energy expansion term by term.

Put tau(g)=bar(g)^-1. This is a multiplicative automorphism of the
positive group, preserves root supports and each sign subgroup in the
source three-factor decomposition, and preserves the incoming equations.
Indeed, its logarithmic coefficient is minus the bar of the original
one; the simple prescribed coefficients are fixed by this operation,
and the other prescribed coefficients are zero. Incoming uniqueness
therefore gives tau(g)=g. Three-factor uniqueness then gives

    bar(g_0(h))=g_0(h)^-1

for every wall factor. Consequently each wall adjoint and its inverse
commute with bar. Apply this to X_z, whose centered monomial is bar
fixed: every scalar jump coefficient satisfies

    J_e(v^-1)=J_e(v)                                (4.1)

as a rational identity. The finite-jump lemma now makes it an ordinary
palindromic Laurent-polynomial identity on every live edge.

For completeness its parity can also be tracked without a new premise.
Let Q:M->F_2 be the quadratic refinement of Omega modulo two which is
zero on vertex basis vectors; extend it to added dual directions using
any chosen basis. Thus

    Q(a+b)=Q(a)+Q(b)+Omega(a,b) mod 2.

Consecutive chart vertices are adjacent, so every forward-gap simple
root p has Q(p)=1. The map

    sigma(v)=-v,   sigma(X_a)=(-1)^Q(a) X_a

is an algebra automorphism. The coefficient of X_(jp) in D_p has
v-parity j, which cancels (-1)^Q(jp)=(-1)^j. Hence sigma fixes D_p.
The same incoming/sign-factor uniqueness argument fixes the total and
all wall elements under sigma. A jump from z to y consequently satisfies

    J_e(-v)=(-1)^(Q(z)+Q(y)) J_e(v).                 (4.2)

Every live jump is therefore parity pure. Along a path the endpoint
signs telescope. Since the anchors are independent, Q(x_lambda)=0;
since u is the sum of the distinct selected vertices, Q(u)=M modulo two.
Every path product has parity M, matching (2.1).

There is a useful uniform bound: if rho_e is the greatest v-degree of a
nonzero live jump, its smallest degree is -rho_e by (4.1), and rho_e>=0.
On any complete path, positivity makes the largest product degree the
sum of its rho_e. Formula (3.1) gives

    sum_(e in pi) rho_e <= M.                       (4.3)

In particular every live jump is supported in [-M,M]. The live skeleton
is decidable using rational zero tests and finite reachability; its
weights can then be read in this bounded energy window. This uses the
source wall coefficient algorithms, not the desired elementary
coefficient list. No implementation of that full algorithm is claimed.

These conclusions still fall short. Positive, centered, parity-pure
polynomials need not be Lefschetz: v^-2+v^2=[3]_v-[1]_v. This polynomial
is an abstract arithmetic example, not an actual computed chart jump
or a graph counterexample. The r8 stronger pre-Lefschetz example remains
another warning; none is used to refute U.

## 5. A different theorem applies to cluster monomials, but recognition fails

Davison's *Positivity for quantum cluster algebras*, published Theorem
2.4 (`mainThm` in the retained primary TeX), proves centered Lefschetz
Laurent coefficients for a cluster monomial expressed in a mutated toric
frame of a compatible skew-symmetric quantum cluster algebra. It does
not assume an acyclic quiver. This is a different interface from the
acyclic wall theorem considered in r8.

It suggests realizing Theta_(x_lambda), or the specific target
coefficient, inside that class. To make this a proof one must supply a
compatible seed, the cluster-monomial or Lefschetz-positive expression,
and an exact preservation of X_u extraction and the centered v
normalization. The pinned incoming-section identity alone provides none
of those extra assertions. A general theta basis element is not thereby
a cluster monomial.

Here is a source-based test of the blanket recognition step. Take the
D=2 chart with anchors a=d1,c=d2 and bridge b. Its graph is a--b--c,
with Omega(b,a)=Omega(c,b)=1 and Omega(c,a)=0. The actual source identity
`tri:linear`/`tri:monomial` gives

    Theta_a=U=X_a+X_b+X_c.

The monomial X_(a+c) is central, since a+c pairs to zero with every
vertex. First specialize v=1 and then X_(a+c)=1. Write the resulting
commuting variables as A,B,C with AC=1. The map

    A=x/y,  B=1/(xy),  C=y/x                         (5.1)

is injective on Q[A^±1,B^±1,C^±1]/(AC-1): the exponent vectors
(1,-1),(-1,-1) are linearly independent. It sends the two forward-root
monomials B/A and C/B to x^-2 and y^2, the natural two-arrow exchange
monomials, and sends the actual section U to

    z=(x^2+y^2+1)/(xy).                             (5.2)

**Claim.** In the ordinary coefficient-free two-arrow rank-two cluster
algebra with initial cluster x,y, z is not a cluster monomial.

*Proof.* Mutations are involutions. After cancelling neighboring repeated
mutations, every word on the two indices alternates. Thus all clusters
occur as adjacent pairs of variables satisfying

    x_(k-1) x_(k+1)=x_k^2+1,  x_1=x, x_2=y.

At x=y=1 their forward values start 1,1,2,5; backwards they give the
same sequence. Thereafter if a>b>0 are consecutive values, the next is
(a^2+1)/b>a. So every variable value is 1, 2, or at least 5. A monomial
with nonnegative powers in any cluster has value either a power of two
or at least five, and cannot equal three. But z(1,1)=3. This proves the
claim for all mutation sequences, not a bounded search. ∎

This is a precise obstruction in the specified natural rank-two
realization. It does not prove that no higher-rank realization, positive
combination, or other chart transformation could work. Specialization
(5.1) merges monomials (AC=1) and is **not** claimed to preserve the
coefficient target (2.1). It is used only to disprove the indicated
blanket cluster-monomial identity. It neither disproves U nor repairs
the r8 acyclic inference. The actual coefficient-preserving cluster
realization for the full U remains unpaid.

## 6. Exact remaining operation

Put [r]_v=v^(1-r)+v^(3-r)+...+v^(r-1). With a_(lambda,-1)=0,
partitionwise symmetry gives the unique centered-string expansion

    P_(G,lambda)(v)
      =sum_(d=0)^floor(M/2)
          (a_(lambda,d)-a_(lambda,d-1))*[M-2d+1]_v.  (6.1)

The coefficients telescope in the lower half and symmetry determines
the upper half. The outermost surviving exponent determines each string
coefficient successively, proving uniqueness. Zero targets satisfy it
with an empty sum.

The **exact unpaid operation** is nonnegativity of every coefficient
in (6.1) for every original G and lambda. In the present route, it is
nonnegativity of the primitive string multiplicities of the **whole**
finite path sum (3.1). Sections 3--4 pay finite support, centering and
parity of its individual factors. They do not pay those primitive
multiplicities. Showing every live jump is Lefschetz would suffice:
products and sums of centered Lefschetz strings are Lefschetz, by
[a]_v[b]_v=sum_(j=0)^min(a,b)-1 [a+b-1-2j]_v. This is a stronger sufficient
condition, not a proved hypothesis, a necessary condition, or a
conditional substitute nominated as U.

Equivalently one may construct an injection from the source's
partition-lambda witnesses of rank d to those of rank d+1 for every
lower-half d. The existing energywise finite-rank matchings do not
specify that injection. No compatibility of their arbitrary same-energy
indexings with a centered-chain operator was found. Similarly the
primitive strings in `alg:strings` satisfy a Weyl relation [D,T]=1 and
have degrees h,h+1,... without an endpoint; they do not provide the
required finite centered strings. No descent of these operators to a
partition-preserving target Lefschetz action was obtained.

A compatible primitive Young filtration would also solve the missing
step, but the source degreewise module isomorphism does not construct
one. The r8 S3 countermodel rules out the abstract inference, not a
Hessenberg-specific construction. None is supplied here.

## 7. Primary-literature operation comparison and validation

This is a bounded comparison, not a novelty or worldwide-priority claim.
The credited full target already appears in Shareshian--Wachs,
*Chromatic quasisymmetric functions*, Conjecture 5.1 (`quasistan`). Their
representation argument pays Schur-unimodality, with a different basis.
Their Appendix B supplies centered sum/product closure. The pinned
OpenAI theorem pays elementary positivity and exact partition selection.
Neither is recounted as a new campaign contribution.

Davison--Mandel, *Strong positivity for quantum theta bases*, Theorem
2.15 and its bar-invariance proof already establish the general
scattering symmetry principle in their conventions; Lemmas 3.4--3.5
separate bar-invariance from the stronger Lefschetz conclusion. Conjecture
2.17 is the general Lefschetz extension; Theorem 2.18 assumes the actual
incoming-vector quiver is acyclic. The proof in Section 4 above is the
normalization-specific rational version of that symmetry operation,
not a new general scattering theorem. The live-edge finite-support lemma
is cancellation-free support bookkeeping on the pinned finite target.

Davison (2018) Theorem 2.4 pays Lefschetz for cluster monomials in all
compatible skew-symmetric seeds, but not the missing recognition here.
Abreu--Nigro, *Chromatic symmetric functions from the modular law*,
`prop:csfunimodal`, prove the abelian-family case through centered
unimodal network contributions and cancellation of the network
denominators. Its hypotheses and proof do not provide an all-graph
positive centered path decomposition. No special family is adopted as
this round's target or nominated as a result.

checks.py performs exact supporting arithmetic, with standard-library
integers only: ten normalized dilogarithm inverse identities after
clearing denominators; 65 simple-unit Gaussian jump polynomials and
their centered-string expansions; 729 quadratic-refinement identities;
and 18 Laurent-polynomial rank-two exchange checks. The rank-two
values are 1,1,2,5,13,34,89,233,610,1597,4181. Deliberate wrong inverse
and missing-term controls fail the tested identities; a positive
non-Lefschetz polynomial is correctly rejected as a centered-string
positive object. These are the author's supporting checks only. The
all-mutation rank-two claim is proved above by recurrence, not by those
finite values. There is no new full-U graph census, no actual cyclic
jump computation, and no implementation of the full source witness.

The checks receipt has aggregate arithmetic digest
`57388dd52c378a36b180305236a81199b802499ce817e578e1970a1f7690ce5b`.
No finite check, integrity PASS, or supporting proof is an independent
full proof or contribution PASS. No manuscript or Lean packaging was
attempted.

## 8. Integrity, rights and handoff

inputs-manifest.json and outputs-manifest.json bind every retained file
by SHA256 and byte size. seal.json binds the manifests; seal.sha256 is
the detached external trust anchor. verify.py authenticates the supplied
anchor, manifests, exact inventory, copied r8 provenance, ten pinned
Git blobs and original frozen r8 inventory **before** executing the
one authored checker in an isolated, bytecode-disabled subprocess.
It imports no candidate or third-party code. The checker reads no
inputs and writes no files. Its stdout must match the immutable receipt.
Independent whole-tree hashes before/after cover both the current and
frozen r8 trees on checker success and checker failure. No receipt,
fixture, manifest or source is regenerated by verification.

rejection_tests.py uses disposable copies inside this owned directory to
test candidate corruption, a missing pinned source, and an authenticated
checker failure after resealing only that disposable copy. It confirms
both frozen trees are unchanged; copied tests are then removed. These
are integrity/failure-path checks, not mathematical reviews. Hashes are
integrity commitments under a trusted anchor, not signatures.

All writes are confined to elementary-unimodality-r2/. No nested agents,
shared-index/sibling edits, staging, commits, uploads, external messages,
submissions, publication or count changes occurred. Parent integrates.
Author Myeongjin Kang, no affiliation; original prose CC BY 4.0 and
original code MIT. Third-party retained reading copies remain private
with upstream rights. Full U remains UNRESOLVED.
