# Cross-field research, iteration i02

**Outcome: the requested substantial, genuinely novel advance was not obtained.**
This round developed three concrete routes, with local pivots: sunflower
threshold rounding and discrete convexity; perturbations of the accepted
hyperinvariant-subspace counterexample; and a five-dimensional Kakeya incidence
lift. The strongest completed deduction is a universal obstruction to the
rank-one perturbation route, proved in §4. It is not presented as a substantial
new case of the invariant subspace problem. One specific next proof direction,
including its exact equations and falsification tests, is given in §7.

The upstream theorems at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are premises.
Their proofs were not re-audited. No further agents were started. No staging,
commits, shared-index changes, or writes outside `openai-proof-research/` were
performed. New auxiliary files are under `frontier/sources/i02_crossfield/`
and `frontier/experiments/i02_crossfield*`.

## 1. Scope, importance evidence, and exclusions

I read `AGENTS.md`, `sources/upstream.json`, the full catalogue's result-family
headings and relevant complete entries, the complete preprint-tree listing,
`frontier/OUTCOME.md`, the analysis and discrete scouts, and the relevant Frankl,
K3, and polygon-novelty reviews. In particular, neither a classical reduction
nor a small regularity extension is counted as meeting the user's bar.

The actual cached MathDB records were inspected:

- `frontier/sources/analysis-mathdb/landmark.json`: six landmark problems.
- `frontier/sources/analysis-mathdb/celebrated.json`: forty celebrated problems.
- `frontier/sources/geo_mathdb/celebrated.txt`: cross-check of the latter list.

Our three targets are **315913, sunflower conjecture; 315900, invariant subspace
problem; and 315983, Kakeya conjecture**, all explicitly `celebrated`. This is
problem importance, not a significance score for any deduction below.

The following scope checks prevented selecting already-addressed targets:

- **Graph Hadwiger, 316001:** family 157 already disproves even the fractional
  version and proves a linear list-coloring bound. Its original conjecture is
  not a remaining target under the accepted-corpus premise.
- **Geometric Hadwiger, 383210:** families 087, 091, 092 provide sharp
  volume-product/log-Brunn–Minkowski results and covering-density bounds.
  None of these catalogue contracts gives the required number of strictly
  smaller homothets. A lattice density is an average count per volume, not a
  bound of `2^n` for covering one body. I did not promote this unsupported
  conversion into a fourth candidate.
- **Invariant subspaces:** family 293 concerns hyperinvariance, and invariant
  projections inside a specified factor. Ordinary invariant subspaces in the
  ambient Hilbert space remain a distinct question. Family 296 gives
  *self-adjoint* von Neumann generation, not generation by analytic polynomials.
- **Kakeya:** family 074 proves the three-dimensional maximal estimate and
  four-dimensional Hausdorff result. Its actual consequences section already
  gives dimension at least four in every higher dimension, arbitrary direction
  sets in four dimensions, Nikodym transfer, and a rank-one quadratic curved
  application. None is new work here.
- **PDE/geometry:** the catalogue already includes the dimension-eight De
  Giorgi endpoint (375), infinity-harmonic interior C1-alpha regularity (377),
  global relativistic Vlasov–Maxwell (362), and the relevant hot-spots theorem
  (369). Forced Navier–Stokes computation (376) does not establish unforced
  regularity or blowup. I found no quantitative theorem contract linking those
  settled statements to the remaining landmark Navier–Stokes problem.

This was a catalogue-wide scope screen followed by actual-source reading for
the selected inputs, **not** a claim to have read all 719 manuscripts. Remaining
scope claims are bounded by that search. Withdrawal notices were not used as
theorems; in particular the withdrawn invariant/hyperinvariant equivalence
was independently checked as withdrawn in the primary arXiv record.

## 2. Immutable source contracts

All upstream paths below are relative to
`https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/`.
Full URLs and SHA-256 hashes are recorded in
[`i02_crossfield_upstream_manifest.json`](../sources/i02_crossfield/i02_crossfield_upstream_manifest.json)
and
[`i02_crossfield_reused_source_contracts.json`](../sources/i02_crossfield/i02_crossfield_reused_source_contracts.json).
For both newly fetched sources and reused analysis caches, the Git blob SHA-1
was recomputed and matched the complete pinned tree. Input/review hashes are in
[`i02_crossfield_inputs.json`](../sources/i02_crossfield/i02_crossfield_inputs.json).

**T — constant-factor rounding (family 175).**
`preprints/Integral-and-fractional-expectation-thresholds-are-equivalent-September-23-2026/build/source/sections/introduction.tex`,
`thm:main`: for every finite nonempty ground set X and every nonempty proper
increasing family A, `q_f(A) <= (25*512^4) q(A)`, both with covering budget
1/2. The parameter is an expectation threshold, not the random containment
threshold `p_c`. The companion `consequences.tex`, `cor:two-unions`, already
contains constant-loss integral smallness for sets not covered by two members
of a family of Bernoulli measure greater than 1/2.

**D — discrete convexity (family 175).**
`preprints/Talagrands-discrete-convexity-conjecture-September-23-2026/build/source/sections/00_intro.tex`,
`thm:main`: with the universal integer `L=2^75`, for every N>=1, p in (0,1),
and D subset of `2^[N]`, if `mu_p(D)>=1-1/L`, then

`E_L(D)={A: A is not contained in a union of L members of D}`

has a containment cover G with `sum_{B in G}p^|B|<=1/2`. Members in the union
may repeat and need not be disjoint. Its `cor:two-union` already supplies the
two-member, constant-density-loss version.

**S — the explicit operator (family 293).**
`preprints/Backward-intertwiners-and-a-transitive-commutant-September-27-2026/build/sections/introduction.tex`,
`thm:direct-model`: on `H=L²(Z_2;ell²(Z))`, with Haar probability and
theta(x)=x+1, there are positive measurable weights and a contraction V such
that

`S_x e_j=beta_j(x)e_{j+1}`, `S f(x)=S_x f(x)`,

`||S||=exp(-10)`, and, for every integer n>=1,

`||S^n|| <= exp(-10 floor((n+1)^2/4))`.                       (2.1)

V commutes with S and moves each fibre's coordinate tails backwards by one
with dense image. The algebra generated by S, V, and all scalar multipliers
is transitive. Each fixed global tail `L²(Z_2;span{e_j:j>=h})` is nevertheless
an ordinary S-invariant subspace. These tails and the distinction between
invariant and hyperinvariant subspaces are explicit in the source.

**G — finite-factor generation (family 296).**
`preprints/Relative-generation-and-the-generator-problem-for-finite-factors-September-23-2026/build/sections/introduction.tex`,
`thm:main`: every separable-predual II1 factor has a generator x with
`M=W*(x)`. The source explicitly includes adjoints. This does not say
`M=closure{p(x):p a complex polynomial}`.

**K4 — four-dimensional Kakeya (family 074).**
`preprints/Every-four-dimensional-Kakeya-set-has-full-Hausdorff-dimension-September-24-2026/build/sections/01-introduction.tex`,
`thm:main`: every subset of R4 containing a unit segment in every direction
has Hausdorff dimension four, with no measurability assumption. In
`sections/10-consequences.tex`, `cor:general-directions-four` already gives
`dim_H E >= 1+dim_H D` for arbitrary nonempty direction sets D and
nondegenerate segments in those directions. The same file explicitly records
the higher-dimensional projection bound `dim_H E>=4`.

**K3 — maximal estimate (family 074).**
`preprints/The-Kakeya-maximal-conjecture-in-three-dimensions-September-23-2026/build/sections/introduction.tex`,
`thm:main`, states the L3-to-L3 tube maximal estimate with a
`delta^(-epsilon)` loss.
It is not an estimate for three-dimensional planes in R5 and is not a
four-dimensional maximal estimate. I did not substitute either stronger
statement into the attempts.

## 3. Attempt A: remove the sunflower logarithm by accepted rounding

### 3.1 Exact target and early literature check

For every integer r>=3, seek a constant C_r such that for every k>=1, every
finite ground set X, and every family F of distinct k-element subsets of X,
`|F|>C_r^k` forces r distinct members with all pairwise intersections equal.
The empty core is allowed. This is the celebrated target, and no accepted
catalogue entry resolves it.

The initial candidate was to combine T with a spread measure and replace the
usual logarithmic random-containment loss by an absolute constant. The
classical [Park–Pham theorem, arXiv:2203.17207v2](https://arxiv.org/abs/2203.17207v2)
still has `p_c=O(q log ell)`. T changes fractional certificates into integral
certificates; it does not remove that logarithm.

A bounded-VC fallback was checked **before** treating it as a result. The
September 24, 2026 primary preprint
[Shangguan, arXiv:2609.30263v1](https://arxiv.org/abs/2609.30263v1),
Theorems 1.1 and 1.3, already asserts constant-density containment for fixed VC
dimension and an r-sunflower bound `(Cr log(d+1))^k`. Thus a fixed-VC
specialization would not establish novelty. Its sharpness discussion also
identifies the transversal construction used next as standard. I use these
statements for prior-art exclusion, not as an unreviewed proof input.

### 3.2 Exact failure of the proposed threshold upgrade

Fix integers k,m>=1. Let X be the disjoint union of k blocks B_i of size m,
and let F be all transversals, one element from each block. Put A=up(F).
Then

`mu_p(A) = [1-(1-p)^m]^k`,

`q(A)=q_f(A)=2^(-1/k)/m`,

`p_c(A)=1-(1-2^(-1/k))^(1/m)`.                             (3.1)

**Proof of the expectation-threshold identity.** Any covering coefficient on
a set that is not a partial transversal can be discarded: such a set lies
inside no minimal member of A. For a uniform random transversal F_0,
`Pr(S subset F_0)=m^(-|S|)` for every partial transversal S. Therefore every
fractional cover g of A satisfies

`sum_S g(S)m^(-|S|)>=1`.

For 0<=p<=1/m and |S|<=k,

`p^|S| >= (mp)^k m^(-|S|)`.

Hence every fractional covering cost is at least `(mp)^k`. The integral
cover consisting of all `m^k` transversals attains exactly this value. The
budget 1/2 yields (3.1); at p>=1/m every cover has cost at least one.
The formula for mu_p follows from block independence, and p_c from solving
mu_p=1/2. This proves all claims for every k,m, without numerical evidence.

Take m=k and let k tend to infinity. Since
`1-2^(-1/k)=(log 2)/k+O(k^-2)`, (3.1) gives

`p_c(A)/q(A) ~ log k`.

Thus even **exact equality** of integral and fractional expectation thresholds
does not remove the random-containment logarithm. The uniform measure on F
is m-spread: every prescribed set of j coordinates has containment probability
at most `m^-j`. Consequently a universal claim that every k-uniform
kappa-spread family is hit with probability >=1/2 at p=C/kappa is false.

**Adversarial scope check.** These families contain r-sunflowers when m>=r.
They do **not** refute a statement that additionally assumes r-sunflower
avoidance. Conversely, when m=r-1 they have exactly `(r-1)^k` members and no
r-sunflower: in each block r selections must either all agree or all be
distinct; the latter is impossible, so all r transversals would be identical.
The obstruction refutes the particular general threshold upgrade, not every
possible use of T in a sunflower argument.

### 3.3 Local pivot: apply discrete convexity to avoiding sets

Let k>=2, and let D consist of subsets of X containing no member of F.
At a low enough p, D has the large measure required by D's theorem. A tempting
step is to regard a member of F as an obstruction to being covered by members
of D and apply E_L(D)'s small cover to F.

That inclusion is false in the strongest possible way:

`F intersect E_2(D) = empty`.                              (3.2)

Indeed, split any F_0 in F into two nonempty proper subsets. Since F is
k-uniform, both subsets belong to D, and their union is F_0. The same holds
for E_L with L>=2 by repetitions. Uniform rank, not a finite example, proves
(3.2). Discrete convexity is measuring a coloring obstruction of the induced
hypergraph, not containment of a single edge. This direct pivot produces no
sunflower certificate.

**Disposition.** No improved bound on sunflower-free families was proved.
The general constant-containment bridge is false; the avoiding-family
application has the wrong exceptional set; the bounded-VC fallback has
explicit prior art. These are separate, precisely scoped failures.

## 4. Attempt B: destroy the ordinary invariant tails of the accepted operator

### 4.1 Generation and small-coupling attempts

The actual target is an ordinary invariant subspace: for every bounded T on
an infinite-dimensional separable complex Hilbert space H, does there exist
a closed M with `0 != M != H` and `TM subset M`? To disprove this using S,
one must construct a *new* operator and eliminate all its ordinary invariant
subspaces, not just the fixed tails.

First I tried to encode S, V, and scalar multipliers in one generator using
G. This does not meet the needed contract. Von Neumann generation permits
T*; an invariant subspace for T need not be invariant under T*. Moreover the
strong closure of the unital polynomial algebra of one operator is
commutative. To verify the latter without a hidden joint-continuity claim:
each strong limit A of polynomials commutes with every polynomial by separate
strong continuity of multiplication by a fixed bounded operator; every
second strong limit B then commutes with A by the same argument. But V and
the scalar multiplier of the first 2-adic bit do not commute. The proposed
recovery of the transitive generator algebra from analytic polynomials is
therefore impossible.

Second, put `h(x)=(-1)^(x mod 2)` and

`T_epsilon=M_h+epsilon(S+V)`.

For every complex epsilon with
`|epsilon|(1+exp(-10))<1`, T_epsilon has a nontrivial Riesz spectral
projection and hence an ordinary invariant subspace. Here is the complete
small-coupling argument. The normal operator M_h has spectrum {-1,1};
the Neumann resolvent series confines the perturbed spectrum to the two
closed disks of radius `|epsilon| ||S+V||<1` about these points. Along
`M_h+t epsilon(S+V)`, 0<=t<=1, a separating contour remains in the resolvent
set. Its Riesz projection varies continuously in operator norm and begins
as the nonzero proper projection onto the even 2-adic cylinder. A continuous
path of idempotents cannot change from nonzero to zero or from proper to I:
idempotents within distance less than one have the same trivial/nontrivial
status. Thus the small encoding perturbation fails for every allowed epsilon.

### 4.2 Early prior-art check for a rank-one pivot

The obvious local pivot is a rank-one perturbation that couples the tails.
This was checked against
[Tcaciuc, arXiv:1805.03277v2](https://arxiv.org/abs/1805.03277v2),
especially Lemma 2.1, Theorem 2.3, Proposition 2.4, and Theorem 3.3.
The scalar resolvent criterion and the relation between vanishing moments
and invariant subspaces are already there. A separate primary arXiv check
confirmed that [Kérchy–Pearcy 2503.13005v2](https://arxiv.org/abs/2503.13005v2)
is withdrawn; its asserted invariant/hyperinvariant equivalence supplies no
premise.

For the special accepted S, its much stronger power bound eliminates the
possible exceptional scalar in the scalar resolvent method. The following
diagnostic is the most developed mathematical result of this round.

### 4.3 Completed diagnostic: every rank-one perturbation has an invariant subspace

**Proposition R.** Let H be an infinite-dimensional complex Hilbert space,
and let Q in B(H) satisfy

`||Q^n|| <= A exp(-c n²)` for every integer n>=0,             (4.1)

for some finite A>=1 and c>0. For every nonzero u in H and every nonzero
bounded complex-linear functional phi on H, the operator

`Q+u phi`

has a nonzero proper closed invariant subspace. More precisely, exactly the
following dichotomy suffices: either all moments `phi(Q^n u)` vanish, in
which case a cyclic subspace lies in ker(phi); or Q+u phi has a nonzero
eigenvalue. Consequently every rank-at-most-one perturbation of the accepted
S has an ordinary invariant subspace, the rank-zero case supplied by its
explicit tails.

**Proof.** Condition (4.1) implies quasinilpotence by the spectral-radius
formula. Define the entire scalar function

`g(z)=z phi((I-zQ)^(-1)u)=sum_{n>=0} phi(Q^n u) z^(n+1)`.

For R>=2, the power bound and completion of the square give

`max_{|z|<=R}|g(z)| <= A||phi||||u|| R sum_{n>=0}exp(-cn²+n log R)`

`<= C R exp((log R)²/(4c))`,                               (4.2)

with C depending on A,c,u,phi. The shifted Gaussian sum is bounded uniformly
in its real center: divide the real line into unit intervals, or compare
each half of the sum with the Gaussian integral plus its maximum. In
particular g has entire-function order zero.

If g is identically zero, all moments vanish. Then

`M=closure span{Q^n u:n>=0}`

contains u, lies in the proper closed subspace ker(phi), and is Q-invariant.
The perturbation u phi vanishes on M. Hence M is the required invariant
subspace of Q+u phi.

Suppose g is not identically zero. I claim g attains the value 1. Otherwise
`h=1-g` is a zero-free entire function, h(0)=1, and (4.2) gives

`log max_{|z|<=R}|h(z)| = O((log R)²)`.

There is an entire logarithm b with h=exp(b), b(0)=0. Carathéodory's
coefficient estimate for an analytic function with bounded-above real part
on a disk yields, for every integer j>=1,

`|b^(j)(0)| <= 2 j! R^(-j) sup_{|z|<=R} Re b(z)`.

The right side tends to zero. Thus every positive derivative of b at zero
vanishes, b=0, h=1, and g=0, a contradiction. Equivalently this is the
zero-free, order-zero case of classical Hadamard factorization.

Choose z_0 with g(z_0)=1. Since g(0)=0, z_0 is nonzero. Let lambda=1/z_0
and `y=(lambda I-Q)^(-1)u`. The inverse exists by quasinilpotence and y is
nonzero. By the definition of g, phi(y)=1, so

`(Q+u phi)y = (lambda y-u)+u = lambda y`.

The one-dimensional span of y is a nonzero proper closed invariant subspace.
This proves the proposition. For S, (2.1) implies (4.1) with A=1,c=5/2
(including n=0), since `floor((n+1)²/4)>=n²/4`. Every nonzero rank-one
operator has the form u phi. The rank-zero case uses the tails. QED.

**Adversarial checks.**

- The proposition for a general Q covers *nonzero rank-one* perturbations;
  it does not deduce an invariant subspace for Q itself by setting phi=0.
- The eigenvalue alternative needs no assertion about compactness of Q,
  spectral completeness, or eigenvalue multiplicity.
- The vanishing-moment alternative uses a bounded nonzero functional, so
  the cyclic subspace really is proper. It contains u and cannot be zero.
- The power estimate is uniform in the global operator S, not merely
  fibrewise. This is part of the accepted source contract.
- Positive and negative j tails are ordinary invariant subspaces only;
  no hyperinvariance is claimed. The argument is compatible with the
  accepted absence of hyperinvariant subspaces.

**Novelty and significance disposition.** This is a direct refinement of
the classical scalar rank-one resolvent argument by a classical growth
observation, specialized to the accepted operator. A bounded search did not
establish priority for this exact wording. That is not evidence of novelty.
It excludes a construction route and is not claimed as the substantial
new invariant-subspace case requested by the user.

## 5. Attempt C: use K4 on a slope-incidence lift in R5

The exact hoped-for gain was a universal epsilon>0 such that every compact
Kakeya set K in R5 has `dim_H K>=4+epsilon`. This would improve the bound
four already stated by the accepted corpus. I did not treat the projection
bound itself as a discovery.

For a compact K, parameterize a small direction patch by slopes
`(v,s,1)`, v in a fixed closed three-dimensional ball and s in a fixed
nondegenerate interval I. Unit segments may be replaced by subsegments of a
common positive parameter length: slopes in this patch have uniformly
bounded norms. Define Z to contain (x,s) whenever x lies on *some* witnessing
subsegment in K of slope (v,s,1), with v in the fixed ball. Using all
witnesses avoids any selection-regularity assumption. Their starting points
lie in compact K and the containment condition is closed, so Z is compact.

For every s, the projection of its fibre Z_s to the coordinates (y,t) in
R3 x R contains a segment in every direction (v,1) of an open patch. K4's
already-proved direction-set corollary implies `dim_H Z_s>=4`. The classical
Hausdorff slicing lower bound therefore gives `dim_H Z>=5`. But

`Z subset K x I`,

and the product bound with an interval gives

`dim_H Z <= dim_H K+1`.

The developed argument returns exactly `dim_H K>=4`, with no positive gain.
The lost dimension is the unobserved slope coordinate s. K3 estimates
three-dimensional tube averages, not the size of this slope ambiguity; it
does not supply the missing estimate as stated.

### Local pivot and counterexample to a shadow-only strengthening

I tried replacing one projection by all transversal four-dimensional
projections and demanding compatible lower-dimensional Kakeya shadows.
The required shadow-only implication is false. The sphere

`E={x in R5:|x|=1}`

has Hausdorff dimension four, while its orthogonal projection onto **every**
four-dimensional linear subspace is the full closed unit ball. Every such
projection is a four-dimensional Kakeya set, and every three-dimensional
projection is a full ball as well. Thus arbitrarily many full-dimensional
shadows cannot alone force `dim_H E>4`.

This sphere is **not** a Kakeya counterexample: it contains no nondegenerate
line segment. It refutes only a proposed intermediate lemma that had dropped
the common line-witness information. Similarly, the bush of segments through
one point shows that a uniform pointwise bound on the number of s-labels is
false, but does not settle any averaged incidence bound. I did not replace
Hausdorff fibre estimates by an invalid upper bound based on finite fibre
cardinality; even graphs can have dimension larger than their base.

For prior-art orientation I inspected the primary
[Zahl survey, arXiv:2512.09397v1](https://arxiv.org/abs/2512.09397v1)
and, more decisively for this task, K4's full consequences section. All the
same-dimensional direction and geometric transfers considered here are
already recorded upstream. The compact restriction above makes the attempted
incidence proof well-defined; it is not presented as a substantial new case.

**Disposition.** The lift is valid but recovers only the accepted bound.
The shadow-only pivot is false. A gain would need a new estimate retaining
line incidences and controlling slope ambiguity, which was not proved.

## 6. Validation and artifact record

The complete arguments are above; finite calculations support only their
finite identities. The exact script
[`i02_crossfield_checks.py`](../experiments/i02_crossfield_checks.py)
and output
[`i02_crossfield_checks.json`](../experiments/i02_crossfield_checks.json)
verify:

- twelve Bernoulli containment formulas by full subset enumeration and
  rational arithmetic;
- spread inequalities and the two-independent-subsets decomposition for the
  tested product families;
- absence of 3-sunflowers in binary transversal families of ranks 1 through 4;
- twenty-nine rational evaluations of the rank-two transfer determinant in
  §7's algebraic counterexample.

The probabilistic formulas, sunflower-free product example, rank-one
proposition, and rank-two polynomial identity have proofs independent of
these tests. Finite matrices are not used to infer invariant subspaces of an
infinite-dimensional operator.

Primary-source downloads, version URLs, byte counts, and hashes are recorded
in [`i02_crossfield_literature_manifest.json`](../sources/i02_crossfield/i02_crossfield_literature_manifest.json).
The Tcaciuc PDF was converted to text for its exact theorem statements;
the HTML sources were converted with Python's standard-library parser.
All reused upstream source blobs passed their tree-hash checks. There was no
independent-agent review, as the task forbids further agents; the checks here
are a separate adversarial pass by the same researcher, not external review.

## 7. One next proof direction: rank-two transfer identities for this exact S

**Do not repeat the rank-one or small spectral-gap perturbation attempts.**
The first genuinely different finite-rank test is the following exact
operator-specific problem. Fix S from contract S. For bounded maps
`U:C² -> H`, `W:H -> C²`, require rank(UW)=2 and put

`R(z)=z W(I-zS)^(-1)U`, `D(z)=det(I_2-R(z))`.

Every entry of R has the logarithmic-square growth bound proved in (4.2),
and so does log of the maximum modulus of D. If D has a zero z_0, it is
nonzero because D(0)=1; a vector in the kernel of `I_2-R(z_0)` gives a
nonzero eigenvector of S+UW with eigenvalue 1/z_0. Explicitly, for nonzero c
with c=R(z_0)c, set `y=z_0(I-z_0S)^(-1)Uc`. Then Wy=c, y!=0, and
`(S+UW)y=z_0^(-1)y`.

If D has no zeros, the same entire-logarithm argument forces **D identically
one**. Thus the only rank-two perturbations that might evade the elementary
eigenvalue construction satisfy

`tr R(z)=det R(z)` for every complex z.                     (7.1)

This is an exact necessary condition, not merely a small-norm test.
Writing `M_n=W S^n U`, the condition is equivalent to the countable moment
system, for every integer j>=1,

`tr M_(j-1) = sum_{a+b=j-2}[(M_a)11(M_b)22-(M_a)12(M_b)21]`, (7.2)

where the sum is empty for j=1. Two additional necessary conditions for
absence of an invariant subspace are

`closure span{S^n ran U:n>=0}=H`,                            (7.3)

`intersection_{n>=0} ker(W S^n)={0}`.                        (7.4)

If (7.3) fails its left side is a nonzero proper S+UW-invariant subspace.
If (7.4) fails its left side is a nonzero proper subspace invariant under S
and annihilated by UW. These proofs are immediate from the formulas and
do not assert that (7.1), (7.3), (7.4) are sufficient for a counterexample.

**Precisely proposed next question:** for this particular dyadic direct-
integral S, do there exist rank-two U,W satisfying all of (7.1), (7.3), and
(7.4)? A proof that there are none would finish the rank-two perturbation
obstruction. A construction would isolate an actual operator for further
invariant-subspace analysis; it would not by itself resolve the celebrated
problem. The dyadic weight/fibre structure must enter: rank-two algebra and
fast power decay alone cannot dismiss the determinant identity.

To make that last warning concrete, in dimension two take

`Q=[[0,1],[0,0]]`, `F=[[0,-1],[1,0]]`, `U=F`, `W=I_2`.

Then Q and Q+F are nilpotent, U and W are invertible (so the finite analogues
of (7.3)–(7.4) hold), and

`R(z)=z(I-zQ)^(-1)F=[[z²,-z],[z,0]]`,

`det(I-R(z))=1-z²+z²=1`.

Yet R is not zero or pointwise nilpotent, and Q and F have no common
invariant line: the unique invariant line of Q is span(e_1), which F does
not preserve. This exactly refutes the tempting matrix analogue “determinant
one forces all moments to vanish.” S+UW can still have its *own* invariant
subspace, as the example illustrates. Tcaciuc's final section also warns
that rank-two quasinilpotent perturbations can arise by similarity; those
trivial similarity constructions preserve existing invariant subspaces.

This is the single next direction retained because the round has proved why
rank one cannot work, derived every necessary analytic identity for rank
two, and supplied an explicit counterexample to the easiest proposed
algebraic shortcut. Its eventual significance and novelty would still need
assessment. **No result in this report is offered as satisfying the user's
requested substantial novel theorem.**
