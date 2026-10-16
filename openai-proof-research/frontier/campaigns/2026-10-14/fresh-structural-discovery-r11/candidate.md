# Root closure of Artin parabolics: full target unresolved

Myeongjin Kang; no affiliation. 2026-10-16.
Original prose CC BY 4.0; original code MIT. Third-party inputs remain
private and retain their original rights.

**UNRESOLVED.** This round neither proves nor refutes the full frozen
target R. Nothing is nominated or counted; the accepted count remains
**4/10**. The useful outcome is an exact account of the finite-orbit
operation still needed, and a source-algebra calculation invalidating an
unrestricted direct-sum shortcut. The calculation is not a counterexample
to R. No manuscript or Lean package was prepared.

## Full scope and selection

For every finite set S, every symmetric Coxeter matrix M with diagonal 1
and off-diagonal entries in {2,3,...} union {infinity}, let A=A_M have its
usual Artin presentation. For X subset S let A_X be the standard parabolic.
The target, frozen in original-scope.md before sustained proof work, is

> **R.** For every X subset S, u,g in A and nonzero integer m,
> if g^m belongs to P=u A_X u^{-1}, then g belongs to P.

Empty diagrams, trivial and whole-group parabolics, arbitrary labels,
all word signs and all powers are included. There is no restriction to
spherical, FC, large, right-angled or two-dimensional type. No subclass
or conditional bridge replaces R in the disposition.

The stipulated input is family 254 of openai/math at
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. The actual parabolic-intersection
and categorical interfaces were read, together with the K(pi,1)
companion's main statement and structural consequences and the geometric
CAT(0) companion's introduction. Upstream truth is accepted, as instructed.

The catalogue's numbered headings were surveyed and selected interfaces
in families 204, 210, 254 and 310 read. The complete preprint tree, not
sources/tree.json, identified companions. Word and parabolic membership
algorithms and finite intersection witnesses are already source results.
Quillen coefficient changes are already in that source's introduction.
The Foulkes primary and project-local screen exposed the earlier
I198/I199/I202/I206 polarization and quotient work; that family was
rejected before nomination. No linear-stabilization theorem was frozen
or pursued. Spin multifactor saturation was not developed into a target.

R was selected because its extra operation is specific: pass from a power
fixing a framed object to the element fixing it. Existing source
stabilizer/intersection theorems do not state this. Established root
closure for important subclasses uses additional geometry, as discussed
below. Desirability of the extension is not evidence for its truth.

## Exact source contracts

Write P_f for the unit-label framing projective in the source category
attached to X, and E(x)=B_x P_f. The following are the stipulated
interfaces used here, in their original general finite-rank scope.

* Parabolic paper thm:main, stab:parabolic and its proof: intersections
  are parabolic, with an inside-parabolic description. In particular an
  ambient parabolic contained in A_Y is c^{-1} A_R c for R subset Y and
  c in A_Y. A strict containment has R proper.
* cor:arbitrary-intersections: every subset has a unique smallest
  parabolic PC, and arbitrary intersections have finite witnesses.
* cat:action, cat:family and stab:single-detector: the B_x are invertible
  graded bimodule homotopy classes, E(x) is indecomposable, has exactly
  one framing generator in placements (0,0), and
  B_w P_f is equivalent to P_f exactly when w is in A_X. Label tensoring
  gives the full-family version. Thus the stabilizer of E(x) is
  x A_X x^{-1}.
* lay:structure and null:hom: a generator in cochain/internal placements
  (c,u) has level c+u. Linear differentials preserve that level and token
  differentials lower it by one. For two layers of members E_L(x),E_H(x)
  with the **same** x, linear Hom has zero length-one cohomology.
* ht:minima, ht:containment and sph:containment: connected harmonic minima
  and spherical positive-height arguments give the stabilizer containment
  used in the parabolic theorem. They are not stated for unordered finite
  sets of differently transported objects.
* K(pi,1) companion thm:main and cor:artin-structural: the full Salvetti
  complex is aspherical and A is torsion free. This already pays the
  empty-parabolic case of R. Its center, monoid and braid-tail stability
  conclusions do not assert R.

The third companion's thm:main excludes a geometric CAT(0) action for
one 116-generator group. It neither gives R nor rules out all CAT(0)
Deligne metrics: proper cocompact actions and that separate metric
question have different hypotheses. No such inference is made.

Exact private paths, immutable raw URLs, Git blob identities, SHA256
values and byte sizes are in retrievals.json. source-contracts.md states
the actual semantic reading extents. Authentication of all retained
bytes is not a claim to have read every retained source.

## Equivalent full-strength gaps

First, conjugation carries the family of parabolics containing a subset
onto the corresponding family for its conjugate. Taking intersections
therefore proves

    PC(a E a^{-1}) = a PC(E) a^{-1}.                    (1)

R is equivalent to PC(g^m)=PC(g) for all g,m!=0. One inclusion follows
because every subgroup containing g contains g^m. R applied to the
parabolic PC(g^m) gives the reverse inclusion. Conversely equality of
the closures puts g in every parabolic containing g^m. Negative powers
reduce to positive powers by inversion inside the subgroup.

There is a second exact equivalence:

> R holds for all inputs if and only if N_A(Q)/Q is torsion free for
> every parabolic Q of every original A.

If R holds and a normalizes Q with a^m in Q, R gives a in Q, proving
one direction. For the other, suppose g^m is in P and put Q=PC(g^m).
Then Q is contained in P. Equation (1) says g normalizes Q, since g
centralizes g^m. The coset gQ has finite order, so the asserted
torsion-freeness puts g in Q and hence P. This reformulation retains
every original quantifier; it does not prove the normalizer assertion.

For comparison, intersections alone allow the construction

    Q' = intersection_{i=0}^{m-1} g^i P g^{-i}.

It is parabolic and contains g^m. Since g^m is in P, conjugation by g
cyclically permutes these factors and normalizes Q'. This still gives
only a finite cyclic extension <Q',g>/Q'. Nothing in that construction
proves the extension trivial. Using PC(g^m) instead makes the same
remaining issue more transparent.

## Proper parabolic inclusions have infinite index

This supporting fact is standard in character, not a nomination. Here is
a proof from the stipulated interfaces to make the later use explicit.

Suppose A_R is a proper standard parabolic of A_Y, and choose s in Y-R.
The inside-parabolic intersection description shows that A_s intersect
A_R is either {1} or A_s. The latter is impossible: the Coxeter quotient
sends A_R into W_R and sigma_s to s, and s is not in W_R. To see the last
assertion directly, in the geometric representation every reflection
from R acts trivially on V/span{alpha_r:r in R}. Reflection s sends the
nonzero class alpha_s to its negative, so cannot be in W_R.

Thus A_s intersect A_R={1}. The standard embedding gives A_s infinite
cyclic. All cosets sigma_s^k A_R are distinct: an equality would put the
nonzero power sigma_s^{k-l} in that intersection. Hence [A_Y:A_R] is
infinite. An arbitrary proper inclusion Q<E of parabolics is conjugate
inside E to just such an inclusion by the source description, so its
index is infinite as well.

Consequently, if an overgroup K of a parabolic L inside A has L of finite
index, proving that K is parabolic would force K=L. The missing assertion
here is parabolicity of that overgroup, not the index argument.

## The finite-orbit route and the precise unproved extension

Fix one X and its framed category. For a finite nonempty set O of
isomorphism classes of transported unit objects E(x), let K be its
setwise stabilizer under A and L its pointwise stabilizer. The action
on O gives L normal in K and [K:L] finite. Each point stabilizer is
x A_X x^{-1}, so L is parabolic by the pinned intersection theorem.

If K were parabolic, the preceding infinite-index argument would give
K=L. In particular, if B_{g^m}P_f is equivalent to P_f, its finite orbit
O={E(1),E(g),...,E(g^{m-1})} has g in K. Equality K=L would put g in A_X,
which is R for standard P. Conjugating covers the original P.

In fact the proposed assertion

    every such finite-set setwise stabilizer K is parabolic             (2)

is equivalent to full R, under the source premises. If R holds, for
a in K some positive power of a lies in L, so R applied to L gives
a in L. Thus K=L is parabolic. The reverse direction was just proved.
This is an exact diagnostic bridge, not a smaller theorem offered as
success and not a source consequence assumed without proof.

I tried to apply the source height construction to a direct sum of the
objects in O. Minimal complexes have unique indecomposable summands, so
the stabilizer of the direct sum of the distinct representatives is
exactly K. Generator counts, exterior invariance, finite level support
and label folding all add. The difficulty occurs in the null-layer
argument, before the global height proof can be transported.

The source null:hom proof uses the actual Hom cohomology of two
projectives transported by the same B_x. Their identity and token
classes exhaust the relevant actual diagonal Hom dimensions, so no
permanent middle class remains. A sum of different transports introduces
cross Hom terms with no such same-transport contract. The following
calculation shows that their vanishing cannot simply be added as a
formal property of all transported sums.

## An actual source-algebra obstruction to blanket sum vanishing

Take S={s}, X=empty. The source adds f and o, all three pairwise labels
are 3, and the label category has one simple object. Its algebra has a
unit and token at each vertex, one arrow in each direction between
different vertices, nonzero backtracks equal to tokens after normalization,
and all other positive-length products zero. In particular paths of
length greater than two vanish. Work over C; all displayed matrices
have a rational form.

Let P=P_f and F=F_s. With cochain placements displayed, the evaluation
cone gives

    FP = [ P_s<1>  --arrow-->  P_f ]          (-1,0).                (3)

Cancellation of the identity part of the evaluation on P_s gives
F P_s equivalent to P_s<2>[1]. Apply F to the defining triangle for
(3). The resulting nonzero map from P_s<3>[1] to FP has just one possible
degree-preserving component, a token into P_s<1> in cochain degree -1.
It is nonzero: the original arrow is a nonzero morphism between
projectives, and an equivalence preserves its nonzero homotopy class.
Rescale the first summand to normalize it. Its cone therefore gives

    F^2 P = [ P_s<3> --token--> P_s<1> --arrow--> P_f ]
                     (-2,             -1,              0).        (4)

The token-arrow composite is zero, and every entry is radical, so (4)
is already minimal. Its first term has level 1 and its last two terms
have level 0. Thus Y^1(F^2P) consists of the single summand P_s<3> in
cochain degree -2, with zero linear differential.

Linear Hom from Y^0(P)=P_f to this upper layer has a one-dimensional
length-one space and no length-zero or length-two spaces. Its nonzero
class has bidegree

    (cochain,internal)=(-2,4),

using the source formula n=c'-c and v=u'+length-u. Hence

    h_1(Y^0(P),Y^1(F^2P))=1.                                    (5)

For the direct sum Z=P direct-sum F^2P, the source P-summand still gives
this independent class in h_1(Y^0(Z),Y^1(Z)). The F^2P source summand
has zero middle cohomology, consistently with the pinned same-transport
lemma. Explicitly its arrow term maps isomorphically to its token term.
Thus the aggregate middle term has dimension two, outgoing rank one,
incoming rank zero, and homology dimension one. Full actual Hom(P,F^2P)
has the identity-target class in bidegree (0,0) and the class (-2,4).
The latter survives because the outgoing composition with the token
has length three and is zero; its incoming space is zero.

This is a counterexample to extending null:hom to arbitrary direct sums
of different transports. It is not a periodic orbit for an element
whose power fixes P. Indeed s acts freely on these successive framed
objects in this rank-one example. No assertion that actual finite
periodic orbits violate (2), or that every possible orbit-specific
argument fails, follows from (5).

The lost hypothesis also enters null:separation through the weighted
Euler identity: removing the h_1 term uses that vanishing. Positivity of
the aggregate counts does not remove a nonzero cross h_1 term. I did
not prove a replacement cancellation or inequality using periodicity.

## Two other shortcuts do not close the gap

Torsion-freeness of A, already supplied by the K(pi,1) companion, is
weaker than torsion-freeness of N_A(Q)/Q. It also does not give unique
roots. In the Artin group B_3=<s,t | sts=tst>, put Delta=sts=tst.
Direct multiplication using the two expressions gives

    (st)^3=Delta^2=(ts)^3.

But st differs from ts: send s to (12) and t to (23) in S_3; their
products are the two distinct 3-cycles. This is compatible with R
in spherical type. It only invalidates an attempted appeal to unique
roots of arbitrary elements.

At the abstract level, intersection closure, finite height, torsion-
freeness and infinite index of proper inclusions do not imply root
closure. In the additive group Z^2 take the conjugation-invariant family
{0, 2Z times {0}, Z^2}. It is a finite complete intersection lattice;
every proper inclusion has infinite index. Yet (1,0) is outside the
middle subgroup and its double is inside. This is not an Artin
parabolic family and refutes no Artin theorem. It isolates why the
listed lattice/index properties alone cannot finish the argument.

## Primary-literature comparison at the operation level

This is a bounded screen, not a worldwide novelty certificate.

Cumplido--Martin--Vaskou, [*Parabolic subgroups of large-type Artin groups*](https://doi.org/10.1017/S0305004122000342),
Proposition 37 and Corollary 39, already prove root closure in large type.
Their Lemma 38 and full Proposition 37 proof were read: a finite orbit in
the systolic Artin complex yields an invariant simplex; the action has
no inversions, so the element lies in a proper parabolic, enabling rank
induction. The missing general step here is precisely such a finite-orbit
reduction. The pinned harmonic-minima connectedness theorem does not
state its equivariant analogue for the orbit sum.

Hagen--Martin--Sartori, [arXiv:2503.20620v1](https://arxiv.org/html/2503.20620v1), Definition 5.9 and Theorem 5.10,
state the same root-closure property and credit its two-dimensional
case to Godelle Corollary 3.8. Lemma 5.11 uses it to identify stable and
ordinary fixed trees. Those interfaces and the lemma proof were read.
Godelle's full original proof was not obtained/read in this round;
the two-dimensional scope is reported as the theorem explicitly credited
by HMS, not a new independent reconstruction.

Garnier--Heng--Licata--Yacobi, *Normalisers of parabolic subgroups of
Artin--Tits groups and Tits cone intersections* ([primary PDF](https://ogarnier.github.io/pub/norm_artin_tits_cone.pdf)), Theorem 1.8, gives
classifying spaces for the normalizer quotients when the ambient Coxeter
group is finite. Their Conjecture 1.10 requests its extension to arbitrary
type; the arbitrary-type atomic Matsumoto theorem 1.4 is a different
statement. The introduction and these exact interfaces were read. One
cannot substitute the pinned classifying space for A for the required
classifying space of its normalizer quotient. The full later proof was
not audited here.

The source's arbitrary intersections, algorithm and asphericity results
are paid operations. None of the read statements supplies the periodic-
orbit Hom control or the arbitrary normalizer-quotient conclusion. The
reductions and obstruction above are technical supporting work, not a
substantial result under the campaign standard. No known subclass is
renamed as a new theorem.

## Exact unpaid step and verification limits

The full remaining assertion can be stated without any changed scope:
for every original X,M,g,m, B_{g^m}P_f equivalent to P_f must imply
B_gP_f equivalent to P_f. Equivalently prove (2), or prove torsion-
freeness of every N_A(Q)/Q. For the attempted height proof, one must
control the actual cross-transport Hom terms using the finite periodic
orbit, and then justify the null-layer and two-point steps, or supply
a different equivariant descent. None was established. No actual Artin
counterexample was found. Full R remains UNRESOLVED.

hom_checks.py supports only the displayed finite algebra: exact rational
linear elimination, all 192 composable triples of algebra basis paths,
the complexes' d^2 equations, six same-transport layer pairs, the cross
and aggregate middle classes, full Hom(P,F^2P), and the two S_3 images.
Its immutable receipt has arithmetic digest
bc55fb006568e08897d0def99e800cdfc91fbcda803b5e79580af6de2ebb0a7b.
It includes rejection of blanket middle vanishing and a spurious
length-three path. It does not implement general categorical transport,
decide R, or provide an independent mathematical/contribution review.

The first run failed because an assertion compared the aggregate
chain-term dictionary to the single cross-term dictionary: aggregate
dimension/rank are 2/1, not 1/0, although both homology dimensions are one.
The original code, authentication record and failure outputs remain
retained. The assertion was corrected before the successful run; no
failed run is relabelled successful.

The complete mandatory historical brief was read: 119315 characters,
119730 bytes, SHA256 97f5b23fcd79fa6abc3850e6efdd3e001530665e26e9811fc5a4e61dcef9fb57.
The current ledger, full structural-r10 and relative-CI-r2 candidates,
both C dispositions and the specified F/G parent dispositions were read.
The r10 and r2 frozen trees authenticate to the supplied seals, with
91 and 34 exact files respectively. No historical code was executed.
Earlier targets and objections remain retained; no third C attempt,
U/H/B continuation, crossing manuscript work or F/G extension occurred.

Input/output manifests bind exact membership, sizes and SHA256. The
external reference manifest records the complete two historical trees
without copying them, plus the exact other consulted fixed files.
verify.py authenticates its externally supplied seal, all inventories,
the selected pinned Git blobs and those historical trees before running
the one checker under a write/network-denying audit hook with isolated
Python and bytecode disabled. It compares immutable stdout/stderr and
regenerates nothing. Whole-tree snapshots cover own and historical
trees on success and failure. External siblings are required; no
standalone portability claim is made. Four controls rejected a wrong anchor,
payload corruption, an authenticated checker failure and an authenticated
write attempt in disposable copies. Original and historical trees were
unchanged; integrity-controls.json retains the receipts. Hashes establish integrity under
the caller's anchor, not mathematical truth or independent acceptance.

All new writes are inside this uniquely owned r11 directory. No nested
agents, shared edits, staging, commits, uploads, external messages,
submissions or publication were performed. Parent integration and any
future independent gates are separate. The count remains 4/10.
