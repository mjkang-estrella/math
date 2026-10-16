# Full Artin parabolic root closure: a normalizer proof

Myeongjin Kang; no affiliation. 2026-10-16.
Original prose CC BY 4.0; original code MIT. Third-party inputs remain
private and retain their own rights.

**Disposition: proposed complete proof of unchanged R, relative to the
stipulated pinned theorems and the primary retraction theorem below.**
This is an author proof, not an independent proof PASS. No result is
nominated as a substantial frontier contribution or counted. The campaign
remains **4/10**. The decisive operation is already available in
Digne–Godelle–Michel's arbitrary-type retraction formula. The new assembly
is short and elementary; it should not be promoted as a new substantial
mechanism. No manuscript or Lean package was prepared.

## Original scope

For every finite set S, including the empty set, every symmetric Coxeter
matrix M with diagonal 1 and off-diagonal entries in
{2,3,...} union {infinity}, let A=A_M be the Artin group with its usual
alternating braid presentation. For every X subset S and every u,g in A,
put P=u A_X u^{-1}. The full target is

> **R.** For every nonzero integer m, g^m in P implies g in P.

All diagram types, labels, signs, ranks, trivial and whole parabolics,
conjugators and exponents are retained. `original-scope.md` is byte-for-byte
the frozen r11 scope. No extra hypothesis about normalizers, periodic
orbits, labels, geometry or categorical Hom is imposed on R.

## Exact mathematical inputs

The two stipulated inputs are at openai/math revision
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, family 254:

1. *Parabolic intersections in Artin groups*,
   `cor:arbitrary-intersections`: every subset of A has a smallest
   parabolic closure PC. The exact statement and its finite-rank proof in
   `08_stabilizers.tex` were read. Pairwise closure alone is not silently
   substituted for arbitrary closure.
2. *Harmonic heights and the Artin K(pi,1) conjecture*,
   `cor:artin-structural` (i): A is torsion free for every original
   finite-rank matrix. Its statement and finite-dimensional classifying
   space argument were read. Upstream truth is stipulated, not audited.

The additional established primary interface is Digne–Godelle–Michel,
[*Retraction to a parabolic subgroup and applications*,
arXiv:2407.07459v2](https://arxiv.org/html/2407.07459v2#S2),
Proposition 2.6(1),(7) and **Lemma 2.7**. Their versioned original TeX
was retrieved separately from the HTML; the statements and proofs agree.
The TeX labels are `fourre-tout`, items `ft6`,`ft2`, and `mult2`.

Write theta:A -> W for the Coxeter quotient, I subset S, and Q=A_I.
The source gives a **set retraction** rho_I:A -> Q, with rho_I(q)=q
for q in Q. If theta(a) normalizes W_I, its minimal representative in
W_I theta(a) is an I-ribbon-I in the Coxeter group. The induced
permutation of I preserves its Coxeter matrix and gives an automorphism
alpha_a of Q. Lemma 2.7 states the product rule

    rho_I(a b) = rho_I(a) alpha_a(rho_I(b))       for every b in A.   (1)

There is no spherical or FC hypothesis in this lemma. In particular,
alpha_a is injective and alpha_a(1)=1. We do not assert that rho_I is a
homomorphism on all of A. Nor do we assume an arbitrary-type Artin
ribbon-generation conjecture: the ribbon used to formulate (1) belongs
to W and is supplied by the cited lemma itself.

To check the automorphism assertion explicitly, the ribbon bijection of
I comes from conjugating its generating reflections in W. Conjugation
preserves the order of each product of two of them, hence every Coxeter
label, including infinity. The same permutation therefore preserves
every defining Artin relation; its inverse permutation does too. It
induces an automorphism of A_I, as required in the inverse-closure step.

For clarity about this precise source boundary, Lemma 2.7's proof writes
theta(a)=v w with v in W_I and w the minimal Coxeter ribbon, lifts w to
the positive simple braid a_w, and puts a_1=a a_w^{-1}. Proposition
2.6(7) applies to a_1 because theta(a_1) lies in W_I. Proposition
2.6(8) applies to a_w. Their product formulas give
rho_I(a b)=rho_I(a_1) alpha_a(rho_I(b)); putting b=1 identifies
rho_I(a_1)=rho_I(a). These are established source operations. Definition
1.14 explains the ribbon's permutation, Proposition 1.16 proves its
word product formula, and Proposition 2.4 descends the retraction to
group elements. These interfaces and their displayed proofs were read.

## The missing normalizer operation

**Lemma.** For every original A and every standard parabolic Q=A_I,
N_A(Q)/Q is isomorphic to a subgroup of A. This assertion does not need
torsion-freeness or parabolic intersections.

**Proof.** Let N=N_A(Q). If n is in N, then

    theta(n) W_I theta(n)^{-1}
       = theta(n Q n^{-1}) = theta(Q) = W_I.

Thus (1) applies to every n in N and every right factor b in A. Define

    K = { k in N : rho_I(k)=1 }.                                  (2)

We check all subgroup operations, rather than calling this a kernel of
a homomorphism that has not been established.

The identity belongs to K. For k,l in K, (1) gives
rho_I(kl)=1 alpha_k(1)=1, so kl belongs to K. For k in K, apply (1)
to k k^{-1}:

    1 = rho_I(1) = alpha_k(rho_I(k^{-1})).

Injectivity of alpha_k gives rho_I(k^{-1})=1. The inverse also lies in N.
Consequently K is a subgroup of A.

Since rho_I fixes Q pointwise, K intersect Q={1}. Given n in N, set
q=rho_I(n) in Q and k=q^{-1}n in N. Proposition 2.6(7), whose left
factor q^{-1} has Coxeter image in W_I, gives

    rho_I(k) = rho_I(q^{-1}n) = q^{-1}rho_I(n)=1.                   (3)

Thus k belongs to K and n=qk. The quotient homomorphism N -> N/Q,
restricted to the subgroup K, is injective because its kernel is
K intersect Q, and surjective because of this factorization. Hence

    K  -->  N_A(Q)/Q

is a group isomorphism. This also gives N=Q semidirect K. No normality
of K, and no global multiplicativity of rho_I, was required. ∎

If Q is any conjugate of a standard parabolic, conjugate the entire
normalizer and its quotient. The lemma therefore covers every original
parabolic Q.

**Corollary.** Under stipulated torsion-freeness of A, N_A(Q)/Q is
torsion free for every parabolic Q.

**Proof.** It is isomorphic to the actual subgroup K of the torsion-free
group A. A torsion element of K would be a torsion element of A. ∎

This is the inference missing from r11. Torsion-freeness of A by itself
does not imply torsion-freeness of arbitrary quotients. The new-to-this-
round input is the product law that proves the quotient embeds in A.
This argument neither assumes unique roots in A nor derives them.

## Complete proof of R

Conjugation permutes the parabolics containing any subset E of A, so
their defining intersections give

    PC(a E a^{-1}) = a PC(E) a^{-1}.                              (4)

Let m>0 and suppose g^m belongs to the original P. Set
Q=PC({g^m}). The stipulated closure theorem makes Q parabolic and
Q subset P. Since g centralizes g^m, equation (4) gives
g Q g^{-1}=Q. Thus g belongs to N_A(Q), and the coset gQ satisfies

    (gQ)^m = Q.

The corollary makes this normalizer quotient torsion free, so gQ=Q.
It follows that g belongs to Q subset P, as required. If m<0, then
g^{-m}=(g^m)^{-1} belongs to P, and the positive-exponent argument
applies. This includes m=1 and m=-1.

For S empty the group is trivial. The argument also allows Q={1}
and Q=A: the former quotient is A, and the latter is trivial.
Therefore trivial and whole input parabolics, disconnected and infinite
types, arbitrary labels, and every conjugator are included. There is no
remaining periodic-orbit or equivariance hypothesis. ∎

One can express the logical content more sharply: given the primary
retraction theorem and existence of all the required parabolic closures,
root closure for every parabolic of A is equivalent to torsion-freeness
of A. The forward direction uses the trivial parabolic; the reverse
direction is the proof above. This is a deduction with all its inputs
present, not a conditional criterion left unpaid in place of R.

## What happens to the r11 objections

All three r11 equivalences remain correct. The normalizer-quotient
assertion is now supplied by (1)--(3) and stipulated torsion-freeness.
The finite-set stabilizer statement follows afterward from R and the
intersection theorem; it was not assumed to prove R.

The direct-sum categorical shortcut remains invalid. Same-transport
`null:hom` and `null:injection` still cannot be applied to differently
transported summands. The rank-one pair P_f,F_s^2 P_f is not periodic;
its cross h_1=1 and aggregate dimension/rank 2/1 remain as recorded.
`research-notes.md` independently reconstructs the cone and shift
calculation used in retaining that objection. No archived checker was
executed, and no finite matrices certify categorical transport.

Individual connected harmonic minima, additive counts and folding still
do not prove an equivariant null-layer or two-point statement for sums.
Our initial cyclic Hom and frame-map analysis is retained in the research
notes, with its limitations, but is unnecessary for the proof.

Proper parabolic inclusions still have infinite index, and that argument
still needs parabolicity of a proposed finite extension. It is not used
here. B3 still has distinct st,ts with equal cubes. The Z^2 family
{0,2Z times {0},Z^2} still separates lattice/index/torsion assumptions
from root closure. Neither contradicts the new proof: the latter family
has no retraction satisfying the needed product law. No CAT(0) action
or Deligne metric is inferred from asphericity.

## Contribution and primary comparison

This is a bounded operation-level comparison, not a worldwide novelty
certificate. Digne–Godelle–Michel have already paid the arbitrary-type
twisted product rule. Showing that its zero fiber inside a normalizer is
a complementary subgroup is elementary group theory. The pinned inputs
already pay existence of PC and torsion-freeness. Their assembly above
provides a full proof relative to these inputs but does **not** establish
a substantial new mechanism under the ten-result campaign standard.
Nothing is nominated or counted on this worker's authority.

CMV Proposition 37/Corollary 39 already give large-type root closure via
finite-orbit systolic fixation. HMS Definition 5.9/Theorem 5.10 credit the
two-dimensional result to Godelle. Those antecedents remain credited;
this proof uses the general retraction instead of extending their
geometry. Their exact retained interfaces are identified in r11's
authenticated source contracts; no fresh full proof reading of those
two articles is claimed in this round.

GHLY Theorem 1.8 gives a specific normalizer-quotient arrangement model
in spherical ambient type, with general extension Conjecture 1.10.
Embedding the abstract quotient in A proves neither that specific model
nor its general asphericity. The arbitrary-type atomic Matsumoto theorem
1.4 is a different interface. These distinctions survive unchanged.

The newly screened Heng–Licata–Yacobi Theorem 1.1 concerns finite-type
central-power periodic elements and fixed points in a stability space
modulo C. Its full-twist shift and covering inputs do not supply the
arbitrary-type framed-object assertion by themselves. It is a screened
alternative, not a dependency of the proof.

## Review and integrity limits

The whole frozen r11 tree authenticated against external seal
`10fd62265feb74bac5d90b1001346699071e4a80d747b7e6f8ae5df6726c0e5c`:
115 files, 90 inputs/21 outputs, 78 pinned Git blobs. Its two exact
historical inventories, totaling 125 files, also matched. The complete
119315-character historical brief and the specified prior candidates,
parent dispositions, ledger and F/G corrections were read; no vetoed
lane was reopened. Authentication is not a claim to read all retrieved
upstream bodies.

This round needs no finite-case search to support the universal subgroup
argument. `verify.py` authenticates exact own/external inventories,
versioned primary bytes and pinned Git identities, and writes nothing.
Its immutable receipt is an integrity receipt only. It executes no
historical or third-party code and regenerates no fixture or receipt.
All external references are required; this is not a standalone bundle.

The parent should review Lemma 2.7's arbitrary-type scope and the
zero-fiber subgroup/isomorphism proof first. A separate independent proof
verdict and contribution assessment have not occurred. All writes are
inside `artin-root-r2/`; no nested agents, shared edits, staging, commits,
uploads, publication, external messages or submissions occurred.
