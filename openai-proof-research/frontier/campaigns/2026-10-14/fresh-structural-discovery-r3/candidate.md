# Universal subgroup congruences for finite iterated extensions of Z_p

Author: **Myeongjin Kang**, no affiliation. 2026-10-15.
Original prose: CC BY 4.0. Original code: MIT. Third-party rights reserved.

**Research status:** complete proposed proof of Theorem A, with a precise
stipulated-source characterization in Theorem B. No independent proof,
contribution, manuscript, or Lean gate has run. No acceptance, campaign-count
change, publication, or worldwide-priority claim is made. The contribution
gate must assess whether the action-removal argument below is substantial
rather than a technical application of classical orbit counting.

## 1. Exact statements

All groups and subgroups below are profinite, all homomorphisms and actions
are continuous, and all subgroup series have closed terms. Fix any prime p,
including 2. For a finitely generated pro-p group E put

    a_h(E) = #{ V <=_open E : [E:V] = p^h }  (h = 0,1,2,...).

These count actual subgroups, not conjugacy classes. They are finite: the
coset actions embed the enumeration in the finite set of homomorphisms from
E to the symmetric group on p^h letters.

Call E *poly-Z_p of length t* if it admits a subnormal series

    1 = K_t normal K_(t-1) normal ... normal K_0 = E,
    K_(i-1)/K_i isomorphic to the additive group Z_p  (1 <= i <= t).

The empty series is allowed only for E=1. No nilpotence, powerfulness,
uniformity, splitting of every closed subgroup, integral Lie model, lower
bound on p, or restriction on the actions in the extensions is imposed.
An extension with quotient Z_p does split; its proof is recalled below.

For t >= 1 define integers A_h(t) by

    sum_(h>=0) A_h(t) z^h = product_(i=0)^(t-1) (1-p^i z)^(-1),
    c_t = product_(i=1)^(t-1) (1-p^i)^(-1) in Z_p^times.

Empty products are 1. A_h(t)=a_h(Z_p^t). Congruence to c_t means congruence
in Z_p; its denominator is prime to p.

**Theorem A (universal finite-precision counts).** For every prime p, every
integer t>=1, and every poly-Z_p group E with a series of length t,

    a_h(U) = A_h(t) mod p^(h+1),
    a_h(U) = c_t    mod p^(h+1)                         (A)

for every open subgroup U of E and every integer h>=0. More generally,
every closed subgroup J of E is poly-Z_p of some length r in [0,t]. If
J!=1, the same assertions hold for all open U<=J, with r in place of t.
For J=1, a_0(J)=1 and a_h(J)=0 for h>0.

Consequently, for every open U<=E, every finite continuous U-set X, and
every h>=0,

    sum_([U:V]=p^h) ( |X^V| - |X| ) is divisible by p^(h+1).       (SC)

The precision h+1 is optimal as a uniform statement over this class: the
Heisenberg example in Section 5 fails with h+2 at h=1 for every p. This
does not assert optimality separately for every h or every group.
The limit lim_h a_h(U)=c_t exists in Z_p, is the same for every open U,
and determines t uniquely. All assertions of Theorem A are proved here
without using the stipulated OpenAI theorems.

**Theorem B (arithmetic characterization, relative to the pinned source).**
Fix p and l>=1. Let Gamma be a finitely generated pro-p group with infinite
abelianization. Assume that every finite quotient F of every closed
subgroup of Gamma has generator number d(F)<=l. Then the following are
equivalent:

1. Gamma is poly-Z_p, of a length t in [1,l].
2. Gamma satisfies (SC), for every open U, every finite continuous U-set X,
   and every h>=0.
3. There exists t in [1,l] such that, for every open U and h>=0,
   a_h(U)=c_t modulo p^(h+1).

The implication 2=>1 uses precisely the source's `lem:shrinking-action`
and `lem:kernel-abelianization` in its Section 5, with their full hypotheses
and proofs read. It is the source's existing series-extraction mechanism,
with the first Z_p quotient supplied by the stated infinite-abelianization
hypothesis. It is not claimed as another new result. The new proposed
completion is the universal quantitative converse 1=>3=>2.

Theorems A and B form one package. In particular we do not separately
count action removal, the p-adic limit, length recovery, fixed-point sums,
or the characterization. We do not claim a converse for arbitrary
torsion-free analytic groups, or remove the finite-section bound or the
infinite-abelianization hypothesis from Theorem B.

## 2. The action-removal lemma

**Lemma 1.** Let N be any finitely generated pro-p group and let
alpha:Z_p->Aut(N) be any continuous action. For every h>=0,

    a_h(N semidirect_alpha Z_p) = a_h(N x Z_p) mod p^(h+1).       (1)

The kernel N may have torsion and need not be soluble or of finite rank.
This unrestricted-kernel statement is useful for isolating the actual
counting operation from the poly-Z_p induction.

**Proof.** Write T for the chosen generator 1 in Z_p and alpha for its
action. For b>=0 let S_b be the finite set of N-conjugacy classes of open
subgroups V<=N of index p^b. Let k_b=|S_b|, and let f_b(q) count the classes
fixed by alpha^q. The Z_p action on S_b has finite p-power orbits.

Here continuity on S_b is worth checking. Intersect the kernels of all
continuous homomorphisms N->Sym(p^b). There are finitely many of them, so
their intersection O is open and characteristic and is contained in
every index-p^b subgroup. The continuous action on the finite quotient
N/O induces the action on S_b. In particular alpha permutes S_b with
p-power order.

We claim the exact, integer-valued formula

    a_h(N semidirect_alpha Z_p)
       = sum_(a+b=h) p^b f_b(p^a).                              (2)

To prove it, let H be an open subgroup. Its projection to Z_p is p^a Z_p
for a unique a>=0. Set V=H intersect N and [N:V]=p^b. The index formula
gives [N semidirect Z_p:H]=p^(a+b). Since H surjects to its closed
projection, it contains an element gT^(p^a) over p^a. This element must
normalize V, equivalently

    g alpha^(p^a)(V) g^(-1) = V.                              (3)

Conversely every V and every left coset Vg satisfying
(3) determine the closed subgroup generated by V and gT^(p^a).
Its intersection with N is exactly V: modulo V in the normalizer, the
closed procyclic group generated by gT^(p^a) maps isomorphically to
p^a Z_p. Indeed an infinite procyclic pro-p group is Z_p, and its
surjection to Z_p has zero kernel. Its product with V is compact, hence
closed. Thus no extra norm or finite-order relation is being assumed.
The subgroup has the required projection and index, and its fiber over
p^a is exactly the specified V-coset. This proves bijectivity of the
parametrization, not merely a bound on possible subgroups.

For a fixed V, (3) has solutions precisely when its N-conjugacy class is
fixed by alpha^(p^a). When it does, the number of cosets of possible g
is [N_N(V):V]. There are [N:N_N(V)] actual subgroups in that conjugacy
class. Their contributions are therefore

    [N:N_N(V)] [N_N(V):V] = [N:V] = p^b.

This proves (2), including the factor p^b and the use of conjugacy
classes rather than actual subgroups in f_b. In the trivial-action case
it gives the exact formula

    a_h(N x Z_p) = sum_(a+b=h) p^b k_b.                        (4)

Every alpha-orbit in S_b not fixed by alpha^(p^a) has length divisible
by p^(a+1). Hence k_b-f_b(p^a) is divisible by p^(a+1). Multiply this
by p^b in (2), use a+b=h, and sum. Each term in the difference of
(2) and (4) is divisible by p^(h+1). This proves (1). QED.

This proof does not replace finite subgroup counts by conjugacy-class
counts without their weights, or replace alpha^(p^a) by alpha. Both
changes can fail in the finite diagnostics.

## 3. Proof of the universal congruences

First recall the splitting fact. If a pro-p group K surjects to Z_p,
choose x mapping to 1. The closed subgroup generated by x is procyclic
and infinite, hence Z_p. Its map to Z_p is injective, since a nonzero
closed subgroup of Z_p has finite-index quotient. This provides a
continuous section. Therefore each step of a poly-Z_p series can be
written as K_(i-1)=K_i semidirect Z_p.

Such groups are finitely generated, by induction on the series, so
Lemma 1 applies throughout. For each i=0,...,t put E_i=K_i x Z_p^i.
The decomposition at step i+1 writes

    E_i = (K_(i+1) x Z_p^i) semidirect Z_p,

where the last factor acts trivially on the displayed free abelian
factor. Lemma 1 gives a_h(E_i)=a_h(E_(i+1)) modulo p^(h+1), with
exactly the same modulus at every step. Since E_0=E and E_t=Z_p^t,
we obtain a_h(E)=A_h(t) modulo p^(h+1).

For completeness, projection of a sublattice of Z_p x Z_p^(t-1)
to the first coordinate, with image p^a Z_p and intersection index
p^b in the other coordinates, has p^b choices of lift. Thus

    A_h(t)=sum_(a+b=h) p^b A_b(t-1),

which proves the displayed generating function by induction, starting
with A_h(1)=1. This is the classical lattice count of Tamanoi's
Lemma 5-5, reproduced here rather than treated as new.

Write product_(i=1)^(t-1)(1-p^i z)^(-1)=sum b_j z^j. Each b_j is
divisible by p^j and A_h(t)=sum_(j=0)^h b_j. Evaluation at z=1 is
p-adically convergent and equals c_t. Its omitted tail is divisible
by p^(h+1), proving the second congruence in (A).

An open subgroup U of E intersects the given series in a series with
exactly t factors Z_p. To check that none of the factors disappears,
U intersect K_(i-1) has finite index in K_(i-1); its image in
K_(i-1)/K_i=Z_p is therefore open and nonzero. The kernel of this
image is U intersect K_i. Normality and closedness persist on
intersection. Apply the preceding argument to U.

For any closed J<=E, intersections with the series give factors
isomorphic to closed subgroups of Z_p. Each is either zero or Z_p.
Delete the zero factors. This proves the claimed series of length
r<=t for J, including finite generation. The same open-subgroup
argument applies inside J. No classification of p-adic Lie groups is
needed.

To prove (SC), first take a transitive U-set X=U/W, where
[U:W]=p^m. Count pairs (V,xW) with [U:V]=p^h and V fixing xW.
For a fixed coset xW, its stabilizer is xWx^(-1). If h>=m, the
number of such V is a_(h-m)(W); if h<m it is zero. Consequently

    sum_([U:V]=p^h) |(U/W)^V|
       = p^m a_(h-m)(W)  if h>=m, and 0 otherwise.             (5)

If h<m, subtracting |X|a_h(U) gives -p^m a_h(U), which is
divisible by p^(h+1). If h>=m, the difference is

    p^m [a_(h-m)(W)-a_h(U)].                                 (6)

Both W and U have the same length t. Their second congruences in
(A) show that the bracket is divisible by p^(h-m+1). Equation
(6) has the required divisibility. Every finite continuous U-set
is a finite disjoint union of these transitive sets, so additivity
proves (SC), including X empty and m=0.

Finally the p-adic limit is c_t uniformly over the indicated open
subgroups. Since

    c_(t+1)-c_t = c_t p^t/(1-p^t),

this difference has valuation t. For s>t, summing these differences
shows v_p(c_s-c_t)=t; hence all c_t are distinct. This also proves
uniqueness of the series length without importing Hirsch-length
theory. Theorem A is proved.

## 4. Proof and dependency boundary of Theorem B

Theorem A proves 1=>3. Equations (5)-(6) prove 3=>2 under the
quantifiers of Theorem B, without a poly-Z_p assumption.

For 2=>1 the infinite abelianization, being a finitely generated
Z_p-module, has a Z_p quotient. Let K_0=Gamma and choose its
epimorphism to Z_p with kernel K_1. Use the source's
`lem:shrinking-action` to infer that K_1 x Z_p has (SC) on all
its open subgroups and retains the same bound l on generator
numbers of finite sections. This is exactly its hypothesis with
K=Gamma and d=0, not an unproved reverse implication.

Inductively suppose E_d=K_d x Z_p^d has these two properties. The
source's `lem:profinite-elementary` ensures K_d is finitely
generated. If d>=1 and K_d!=1, its
`lem:kernel-abelianization` gives infinite abelianization of K_d.
Choose K_d->Z_p, put K_(d+1) equal to its kernel, and apply
`lem:shrinking-action` again. Thus E_(d+1) has both properties.
If K_d!=1, a nontrivial finite p-group quotient supplies a quotient
C_p of K_d. Hence E_d has an elementary abelian quotient of rank
d+1, which forces d+1<=l. The process therefore terminates by
step l, with K_t=1 and all successive factors Z_p. This is the
source's existing termination argument. It proves 2=>1 with all
the original section and open-subgroup hypotheses retained.

We do not use the source's additional homomorphism-integrality
hypothesis to prove a new all-finite-target assertion. The present
characterization assumes infinite abelianization explicitly. Its
replacement in this source extraction is immediate from the proof
and earns no separate contribution credit.

## 5. Exact sharpness and supporting computation

Let E be the three-dimensional p-adic Heisenberg group, with elements
(x,y,z) in Z_p^3 and multiplication

    (x,y,z)(x',y',z') = (x+x', y+y', z+z'+xy').

The central z-coordinate, followed by the x- and y-coordinates,
gives a length-three poly-Z_p series. The commutator subgroup is
the full central Z_p: commutators with x=1 produce every central
coordinate. Thus E has elementary abelian quotient E/Phi(E)=C_p^2.
Every subgroup of index p is the kernel of a nonzero linear form
on this quotient, modulo its p-1 nonzero scalar multiples. Therefore

    a_1(E)=p+1,
    A_1(3)=1+p+p^2,
    a_1(E)-A_1(3)=-p^2.

This proves sharpness of the uniform modulus and explicitly rules
out strengthening the theorem to equality of subgroup-count sequences.

`checks.py` independently enumerates all subgroups of nine small
finite groups (including the three direct-product comparison groups).
It verifies the exact conjugacy-weighted formula and compares it with
literal subgroup counts. It also enumerates quotient groups of the
actual Heisenberg and nonnilpotent poly-Z_2 examples, and checks 378
fixed-coset flags directly, plus 320 exact abelian residues. Four
deliberately incorrect variants are rejected: omitting p^b, omitting
conjugacy, freezing alpha^(p^a) at alpha, and overstating the modulus.

For the finite-kernel tests we quotient the procyclic factor by p^L,
with L at least every tested h and divisible enough to kill its finite
action. Every degree-p^h coset action kills that p^L-power, so these
quotients capture exactly the tested open subgroups. For the
torsion-free examples, the coordinate p^L-powers normally generate
the congruence kernel and are likewise killed by every such coset
action. These statements explain the finite/profinite interfaces;
the diagnostic still proves no universal assertion.

The receipt is `checks.json`. The verifier authenticates all inputs,
the frozen receipt, and the whole output inventory *before* compiling
the checker, then compares its stdout payload with the authenticated
receipt. It never rewrites a receipt, manifest, seal, or output.

## 6. Selection, comparison, and contribution limits

Three families were initially screened: elementary unimodality
(169), nonsingular systems of group equations (256), and cyclic
length (314). The actual hypotheses and source proofs, not their
abstracts, determined the choice.

* Elementary unimodality was vetoed after reading I19/I24 and the
  actual forward-difference root quiver. The source root basis is
  cyclic already in the D=3 chart, so acyclicity of the original
  graph orientation is irrelevant. Davison--Mandel's general
  Lefschetz statement is conjectural; the acyclic theorem has an
  unmet hypothesis. No duplicate symmetry lemma, capped mutation
  search, or partial graph family is nominated here.
* The nonsingular-equation source already includes its infinite-system
  extension by a finite-relation argument, and its companion proves
  the Kervaire statement. No credible new preservation-class bridge
  was found at this bounded screen; it was not developed into a
  purported theorem or conditional corollary.
* Family 314's actual Section 5 proves a one-way arithmetic criterion
  and a shrinking-action passage to a limit. It does not state the
  universal finite-precision converse (A). This concrete gap was
  selected. The complete family directory is retained and its other
  sections were searched for overlapping statements; the complete
  preprint path listing has no second family-314 manuscript. This is
  a bounded companion check, not a reading of every manuscript.

**Operation-level comparison.** The source's `thm:procyclic` assumes
finite-section rank, homomorphism-count integrality for every finite
target, and (SC), and extracts a poly-Z_p series. Its
`lem:shrinking-action` transfers qualitative (SC) and rank bounds
from every open slowed-action subgroup to a limiting direct product;
it does not transfer them back. Lemma 1 instead compares exact
subgroup counts in an arbitrary action and the trivial action at
each finite index, modulo an explicit p^(h+1). The p^b normalizer
weight and the p^(a+1) length of the missed conjugacy-class orbits
are the mechanism. Iterating it gives a converse to (SC), without
assuming that property on the original group or its slowed actions.

The abelian generating function and c_t limit already occur in the
source's `lem:lattice-limit` and in Tamanoi (2001), Lemma 5-5; no
novelty is claimed for them. Gordon--Rodriguez-Villegas (2012),
Proposition 3.1/Corollary 3.2, give the closely related torsor count
for homomorphisms from a discrete semidirect product with Z. Their
Section 5 already counts conjugacy classes of subgroups in the
direct-product case and proves adjacent subgroup congruences
u_(p^(k+1))=u_(p^k) modulo p^(k+1). These are strong antecedents;
the orbit-count method here must not be advertised as originating
from scratch. Their stated congruence is within one discrete group,
not comparison of every continuous action to the trivial action,
nor a universal residue determined solely by the length of a
poly-Z_p series.

Kisilevsky (1997), Proposition 1, is a direct antecedent for the
fixed-point orbit divisibility used in Lemma 1. We apply the same
elementary observation to a *weighted family of conjugacy classes*
with complementary index parameters a+b=h. Tamanoi (2003),
Theorem 5-5 and (5-7), supplies the general automorphism-weighted
exponential formula and the actual-subgroup/conjugacy normalization.
Neither selected primary passage states (A) or the poly-Z_p converse.

The literature screen was bounded to these exact mechanisms and
their cited primary sources. It is not a worldwide priority
certificate. The finite-precision congruence may still be known in
specialist subgroup-growth literature, or may be judged a technical
combination of standard orbit counting and the stipulated series
criterion. That is a material unresolved *contribution* question,
not an unproved mathematical step concealed as an assumption.
Independent proof and contribution reviews must receive this objection
and the GRV/Kisilevsky operations, not only the theorem statement.

## 7. Source contracts, reproducibility, and rights

`source-contracts.json` records exact pinned paths, labels, read
extents, hypotheses, and uses. `literature.md` records primary URLs,
read extents, and the corrected mistaken PDF retrieval. All applied
OpenAI source interfaces are accepted true at
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` as authorized; no attempt
is made to audit their truth. Theorem A is independent of those
interfaces. Theorem B exposes its two substantive source lemmas.

Run `python3 -B verify.py` from this directory. It is read-only and
offline. Verify the detached SHA256 of `seal.json` supplied in the
handoff before using it as a trust anchor. Input and output manifests
record SHA256 and byte lengths; pinned blobs additionally have Git
blob identities. A reproducible checker replay is not independent
review. No full Lean formalization or compiled Lean support is claimed.

All third-party reading copies and context snapshots are under
`inputs/` and are excluded from the releasable-original inventory.
They retain their own rights and are private/local reading material.
The new prose and code are separately licensed; those licenses do
not cover these inputs. No external messages, uploads, submissions,
shared edits, staging, commits, or count changes were performed.
