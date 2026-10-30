# Independent proof review of the full canonical sampler CS

Myeongjin Kang; no affiliation. Original review prose CC BY 4.0; original
verification code MIT. Third-party source material remains in the author's
private reading directory and is not copied into this review.

**Verdict: PASS_FULL_CS.** The unchanged candidate proves the entire frozen
scope, conditional on the stipulated pinned source theorems. No repair,
extra hypothesis, weaker action, almost-sure equivariance convention, or
reduced law class is required. This is a mathematical verdict only. The
separate contribution/eligibility gate is not decided here, and no result
is accepted or counted by this review. Campaign count remains 6/10.

The audited candidate SHA256 is
`9cdb35237bd65849e6165824f3435fcaf3dc6a6e5d0ce1690221361b153f01ed`;
the full frozen scope SHA256 is
`b1327efb9564d7ddf64d2bcb248aa5d70a699f3ee63ad4d364de7d5f2abc4877`.
The author manifest anchor is
`19e704a0677bae0015fe3b901956daef070f926ab47d7e2cd0ab63f3df38fad9`.
After inspecting the read-only verifier, I authenticated all 31 payloads
and ten pinned Git blobs. Hash authentication is not the basis of the
mathematical verdict; the deductions checked below are.

## Exact dependency boundary

The immutable source revision is
`fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. I read the entire family231
decoder, strongly-Rayleigh, implementation, introduction and observation
sections, and the response section's finite-tilt definition and canonical
drift interface. The actual Brownian-sampler proposition requires finite
sets increasing to its **entire index set**. The deterministic inverse
lemma accepts every product family of continuous paths, not just bounded
fields or almost every Brownian input. The response lemma covers arbitrary
finite strongly Rayleigh laws, including nonhomogeneous and degenerate
ones, under all positive field tilts. The scalar noise-conversion subproof
supplies one everywhere-defined Borel uniform-to-Wiener map.

These source results are stipulated, not truth-audited here. Their use is
checked against their real hypotheses. In particular, this review does not
reprove the upstream innovation theorem or its infinite-dimensional law
transfer. The source's response constant, Brownian decoder, Picard inverse
and scalar converter receive no new-proof credit.

I also read ABZ arXiv:2203.03935v2 sections 2.1–2.2, including the full
Proposition 2.2 and Lemma 2.5 proofs; BBL arXiv:0707.2340v2 Definition
2.13, Proposition 3.1, Proposition 3.2 and its proof, Proposition 3.5 and
its proof, and Theorems 4.8–4.9 with their proof discussion. They support
exactly the finite-marginal convention, stable-limit closure, complex
Hermitian determinantal strong Rayleighness and negative association used
here. ABZ already pays the four-sign covariance bound and summable-row
operation. Their text extraction drops some absolute-value glyphs in the
displayed proposition, but the two explicit proof inequalities identify
the intended bound unambiguously; the candidate's four-sign calculation
was checked independently below.

The family236 companion introduction through its main theorem and initial
motivation was read. Its regular-tree Ising result is not an extra CS
premise. The forest determinant/free-limit proof, the whole BBL paper,
and Lyons–Thom's body were not independently reviewed in this proof role.
Their complete reading is neither claimed nor needed for this deduction.

## 1. Independence is of blocks, not merely of pairs

For finite disjoint A and B, let U and V be their respective coordinate
sums, and let e and f be the indicators of completely arbitrary events on
A and B. Both U+e and U-e are increasing on the Boolean cube: across a
single upward coordinate flip their change is 1 plus or minus an element
of {-1,0,1}. The same holds for V+f and V-f. Negative association therefore
applies even when the events themselves are not increasing. Adding the
two equal-sign inequalities cancels the mixed terms and yields
Cov(e,f) <= -Cov(U,V). Adding the opposite-sign inequalities yields
Cov(e,f) >= Cov(U,V). Thus

    |Cov(e,f)| <= -Cov(U,V) = sum_{a in A,b in B} c(a,b).

In distinct covariance components every cross term vanishes. This gives
independence of arbitrary finite-coordinate events from disjoint unions
of components, which is stronger than pairwise coordinate independence.
For two arbitrary disjoint unions, their finite-coordinate cylinders are
generating pi-systems. Applying the pi-lambda theorem successively to the
two event arguments extends the independence to their full sigma-fields.
In particular each selected component is independent of the union of all
the other selected components. Induction gives mutual independence of any
finite family of components. There are at most countably many components,
so their product law is uniquely determined by these finite block laws.
This verifies the exact factorization claimed in (2.3).

No conditioning step asserts that a missing edge inside a component stays
missing after other sites are observed. The proof needs no such assertion.
Nor does it infer block independence from pairwise independence alone.
The parity example in candidate section 8 correctly exposes the latter
invalid inference, with covariance 1/8 for the indicated increasing events.

## 2. Every component has intrinsic finite increasing exhaustions

For every finite F containing i, the source row estimate and nonpositive
off-diagonal covariances imply sum_{j in F minus {i}} c(i,j) <= Var(X_i).
Nonnegative summation over the countable index set is the supremum of these
finite sums. Consequently the total is at most 1/4, including when there
are infinitely many positive entries. At threshold 1/n there are at most
floor(n/4) neighbors. Equality at the threshold is permitted and the same
degree bound still holds. A finite-radius ball in a finite-degree graph
is finite; here the degree bound is uniform for that fixed n.

Since the threshold decreases and the radius increases as n increases,
the sets S_n(i) are increasing and contain i. They cannot leave the
positive-covariance component. Conversely, for a finite path to j, choose
an integer n at least its length and at least the reciprocal of every
positive edge weight on the path. Then j belongs to S_n(i). Thus their
union is precisely C(i), not a possibly smaller subcomponent.

This reasoning makes no positive lower bound on all nonzero covariances,
no local finiteness assumption on the full covariance graph, and no
uniform bound in n. Covariance is transported by every coordinate
bijection, so the exact sets S_n(i), at the same n, are transported as
well. An enumeration used to describe the Borel sigma-field does not
enter this definition.

## 3. The source hypotheses hold after restriction to a component

For fixed nu and component C, its marginal nu_C is strongly Rayleigh by
the finite-marginal definition. All the sets S_n(i), i in C, are finite
subsets of C and exhaust C. Their finite-tilt ratios computed in nu equal
the same ratios in nu_C, because their integrands use only coordinates
in C. Positive denominators follow from finite positive exponentials;
no full-support assumption or infinite partition sum is involved.

The finite tilted law on S union {i} has its derivative covariance row
bounded by 1/2 in absolute sum. Integrating along the finite field segment
gives the required supremum-norm Lipschitz estimate for every t and every
finite field. Taking limsups in both directions preserves that estimate.
It also keeps the range in [0,1]. The source Brownian-sampler proposition
therefore applies with index set C and exactly its required exhaustion
hypothesis. It is not applied to an incomplete exhaustion of all of I.

Every coordinate of the global drift in C depends only on the field in C.
The global and restricted Picard iterations consequently agree on C at
every step and every input; their limits agree as well. The component
output has law nu_C by the stipulated sampler. Its inputs are precisely
the independent Brownian coordinates in C. The components use disjoint
inputs, so their output blocks are mutually independent. Combining this
with section 1 proves equality of the entire joint law, not just equality
of one-site or pair marginals.

## 4. All inputs and joint law-parameter measurability

The candidate applies the inverse on the full product of continuous-path
spaces. The inputs need not be bounded over sites. Boundedness of the drift
gives the first increment bound t, and each successive difference is
bounded uniformly over sites by (1/2)^k t^(k+1)/(k+1)!. Thus the Lipschitz
estimate is applied only to pairs with bounded differences, exactly as
required. On each finite time interval the sum of these bounds converges.
This yields a continuous-path limit at every input and permits passage
through the scalar integrals. No nonmeasurable choice of an inverse or
Brownian exceptional-set representative is introduced.

For law dependence, fixed-coordinate cylinder probabilities, means and
covariances are continuous in the weak topology on probability laws over
the compact binary product. Membership j in S_n^nu(i) is a countable union
of finite conjunctions of covariance threshold conditions, one for every
path of length at most n. This is Borel. Equality S_n^nu(i)=S is the
countable conjunction of membership and nonmembership predicates. There
are only countably many finite S. On each equality piece the finite-tilt
ratio is continuous in the law, time and finitely many field values, with
strictly positive denominator. Countable assembly and limsup make each
coordinate of the drift jointly Borel.

For fixed finite/countable I, SR(I) is closed: coefficient convergence of
each finite generating polynomial is compact-uniform convergence, stable
polynomials have a stable or zero limit, and the value at the all-one
vector stays one. Intersect over the countably many finite marginals.
This verifies the optional standard-Borel assertion as stated. In fact
the preceding relative-measurability argument did not require closedness.

The evaluation map from time and product continuous paths to the field
is continuous coordinatewise and hence continuous in the product topology.
Induction makes each Picard integrand jointly Borel in (nu,w,s). Integration
over a fixed finite interval, with an indicator for s<=t where needed,
preserves parameter measurability for these bounded integrands. Rational
time evaluations generate the path-space Borel sigma-field; the iterates
and their continuous-path limit are therefore jointly Borel. Finally beta
is fixed, Borel and scalar, and the integer-time limsup threshold is a
countable Borel operation. This proves the full map SR(I) x [0,1]^I is
jointly Borel, not merely a separately chosen measurable map for each law.

No measurable selection of component representatives or enumeration of
components as nu varies is needed. Components are used in the fixed-law
proof of output distribution; the sampler's formula uses the Borel finite
balls directly. This distinction avoids a potential quotient-space gap.

## 5. Every bijection, every group element, every input

Transporting nu by sigma transports each finite-tilt numerator and
denominator, each threshold ball and the corresponding limsup drift.
Time integration, Picard iteration and passage to the limit intertwine
the same bijection exactly. The same fixed scalar beta is applied at
each site for every I; it introduces no coordinate choices. The final
coordinatewise readout intertwines sigma even on inputs where the slope
does not converge. These pointwise identities prove CS across different
index sets and for all u.

For any group action preserving nu, applying this deterministic identity
to each permutation gives equivariance simultaneously for all elements.
There is no intersection of group-indexed conull events and thus no hidden
countability assumption on the group, its stabilizers or its permutation
image. No topology or measurability on the abstract group is needed for
the stated equivariance. The countability hypothesis is solely on I.

The statement requires output law nu under product uniforms; it does not
require every exceptional label input to land in a chosen support set of
nu. For example, a constant label vector for a permutation-invariant
finite nontrivial fixed-cardinality law may produce a constant binary
vector outside that support. This is allowed and is essential when
requiring pointwise equivariance. The candidate does not mistakenly claim
an everywhere-supported sample.

## 6. Degenerate cases and an independent infinite-component stress check

The empty set has its unique input/output and unique law. For a singleton
or any isolated covariance vertex, S_n(i)={i} for every n. Section 1 shows
that this coordinate is independent of the rest, and the singleton source
sampler applies, including Bernoulli parameters zero and one. For a fully
deterministic law all drifts are constants equal to the prescribed bits;
Brownian integer-time slopes recover those bits almost surely. Exceptional
input readout remains defined and pointwise natural. Finite components
eventually exhaust their finite index sets, so no infinitude hypothesis
has been inserted into the source proposition.

An independent stress example checks the genuinely infinite geometry:
let I be the positive integers and put mass 2^(-j) on the configuration
with its unique occupied site at j. Each finite marginal has generating
polynomial a + sum_{j in F} 2^(-j) z_j, with a>=0. For nonempty F its
imaginary part is positive on the product upper half-plane, so the law
is strongly Rayleigh. For distinct i,j its covariance is -2^(-i-j).
Thus its positive-covariance graph is complete and has infinite degree.
Nevertheless the threshold n graph has edge ij exactly when 2^(i+j)<=n;
it has finite degree and the candidate's balls exhaust the whole infinite
component. At fixed i, every j is in the radius-n ball once n>=2^(i+j).
This directly tests the absence of both a bounded-degree assumption on
the full graph and a uniform positive covariance gap. Its row sum is
2^(-i)(1-2^(-i)), exactly the variance.

At the opposite extreme, an infinite identical-Bernoulli product has
singleton components and the full permutation group as stabilizer. No
finite set containing i and another site is invariant under the whole
stabilizer of i. Therefore whole-set finite equivariant exhaustion really
fails there, while the component construction remains valid. The two
examples check complementary extremes without replacing the universal
proof by experiments. No numerical sampler diagnostic is used as proof.

## 7. Determinantal consequence

For a complex Hermitian positive contraction on l2(I), finite compression
is still a Hermitian positive contraction. All finite inclusion
determinants agree with the finite compressed law; inclusion-exclusion
determines the full finite binary law. BBL Proposition 3.5 applies to those
complex Hermitian matrices, not just real symmetric or invertible ones;
its proof uses the complex Hermitian stability construction and a limiting
argument for singular matrices. Hence every finite marginal is strongly
Rayleigh. Applying CS gives the advertised consequence without a trace
class assumption or excluded projection kernel. The construction uses
only the resulting law, so every law-preserving permutation is respected
whether or not it preserves the displayed kernel representative.

## Reading, history and verdict limits

The complete current review brief, AGENTS.md, immutable upstream revision,
author candidate/scope/source reading/comparison and source receipt were
read. The next-discovery brief and inherited r15/r17 historical assignment
and exclusion passages were inspected. The large nested unrelated old
proof audits in those historical files were not all read line by line;
no prior proof verdict is inherited from them. Focused searches over root
iteration bodies, current campaign candidate/analysis files and the
TEN/TWENTY/current ledgers locate I77's finite matroid-sampling comparison
and this candidate, but no earlier developed CS chain in that search
domain. I77's cited comparison does not construct infinite-law coding.
This is a bounded history screen, not an eligibility certificate or a
worldwide novelty search. The independent contribution role must decide
the remaining operation-level and eligibility questions.

There are no required mathematical repairs to the frozen candidate.
If a manuscript follows, keeping explicit the component-wise application,
joint law parameter, all-input distinction and credited antecedents is
necessary to preserve this verdict's scope. This proof PASS does not
settle whether covariance-component canonicalization is substantial or
merely a technical assembly. It authorizes no count change, manuscript,
publication or full-formalization claim by itself.
