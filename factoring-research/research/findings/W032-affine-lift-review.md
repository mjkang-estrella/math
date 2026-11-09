# W032 affine lift: independent correctness, cost, and degeneracy review

**Disposition: ACCEPT the affine lift identity, exact quotient/top-digit bridge,
integer-family chamber cover, and conservative soft O(R^10(bitlen(N)+R))
complete primitive bound. No mathematical repair to the frozen target is needed;
the explicit degeneracy and arithmetic conventions below specify its literal
sampler. The added parameter is genuine at the input and lower-residue-vector
levels. It can also change the carry distribution: section 7 gives a symbolic
counterexample to an N-fold repetition of the old sweep. Strict enlargement of
carry support and useful factor supply remain UNPROVED. Verified complete
factoring improvement: NONE.**

The added parameter permits an exact pairwise-independence theorem for uniformly
sampled digit phases, not mutual independence. Its resulting second moment gives
a scoped upper bound on uniform proper-split probability. It gives neither a
lower success bound nor an obstruction to exhaustive chamber search. The old
magnitude obstruction continues to exclude actual lifts when leastprime(N)>=4^R.
No stronger exhaustive-family impossibility is established here.

## 1. Frozen scope and accepted interfaces

The full target is the frozen
[affine-family note](W032-affine-lift-review-evidence/inputs/research/findings/W032-affine-lift-family.md),
SHA-256 `84d1c5ff9772ea2ee7c537bd97658e96ccdf6e85cf091b4361627a4046244675`.
The [complete assignment](W032-affine-lift-review-evidence/full-brief.txt) and
[needed-input manifest](W032-affine-lift-review-evidence/needed-inputs.json)
preserve sixteen complete source files, including the original W032 hypothesis.
The five governing documents were read completely. STATE was used only for
coordination; the [exact read scope](W032-affine-lift-review-evidence/read-scope.json)
distinguishes its inspected excerpt from byte-level freezing and the initially
truncated bulk read. The explicit assignment controls this review's boundaries.

The carry-quotient review supplies the accepted lower polynomial, complete
denominator preprocessing, unwrapped-input extension, exact signed quotient,
and acquisition cost. The sweep review supplies the accepted common-lift
interface; its formerly provisional base-acquisition dependency is satisfied
by the carry review, as instructed in this assignment. The arrangement review
is used as geometric background only. Its horizontal-line construction is not
a substitute for the vertical-line and coefficient checks here. Prior reports
are imported at their accepted mathematical scope; their underlying delivery
packages, numerical evidence, and external literature are not reaudited.

The final source check found concurrent changes to STATE and the old common-lift
note. Their [later bytes](W032-affine-lift-review-evidence/observed-later-manifest.json)
are preserved separately. The old-note diff adds its accepted status, the already
imported tie/reporting and storage qualifications, and the resolved acquisition
status; it changes none of this review's identities. Later STATE content was not
adopted. The new affine target and the accepted-interface reports matched their
frozen copies at the recorded stability check.

The old assay report was read, without its code or raw run records. Its stated
outcome remains two exhausted unsuccessful common-lift families and a third
group stopped during prime generation, with candidate execution unstarted.
This review neither replays that run nor extends its finite conclusion to the
new family. There were no candidate evaluations, numerical substitutions for
N, experiments, parameter sweeps, symbolic-program evaluations, installs,
commits, recursive delegation, shared-code/Lean/STATE/registry edits, or project
checks. Python and shell were used only for file inspection, freezing, writing,
and integrity checks. All mathematics below is a prose proof, not Lean-checked
or experimentally certified. W034 and the parent's separate order route were
not inspected or duplicated. Only the two assigned output locations were written.

## 2. Inputs, precision, and the affine Taylor law

Let N>1 be composite, R>=2, m=2R+1, L=2R-2, H=N^(L-1), M=N^(2R),
Q=NM, and D=4^R(2R+1)!. Work on the checked branch gcd(D,N)=1,
equivalently leastprime(N)>m. Rational polynomial identities are interpreted
in S=Z[1/D] or its reduction modulo a power of N. This uses ideals generated
by powers of composite N, not an unjustified prime valuation or field argument.

The complete denominator guard includes j=R even though acquisition of the
lower polynomial stops at R-1. An O(R) scan of gcd(j,N) through the required
small integers, with the composite-input/square-root exit convention of the
accepted carry review, certifies the branch or returns an ordinary proper
factor. An aggregate gcd N requires paid localization. Guard failures and
ordinary factors are distinct from factors supplied by this carry channel.

For a_i=i+1, 0<=i<=m, all points are units on this branch. A prime dividing
m+1 cannot exceed m because m+1 is even and greater than two; all smaller
points have prime divisors at most m as well. Also N>m^2>m+1. Thus no hidden
unit search or endpoint oracle is needed. Explicit O(R) point checks fit the
cost bound. The lifted progression is

    A_i(s,t)=a_i+12H(s+i t)=(1+12Hs)+i(1+12Ht),
    0<=s,t<N, with s,t integers.

Its step is 1 modulo N and is a unit; all points remain the same units modulo
N. Its input width is O(R log N+log R), since A_i< m+2+12(m+1)N^L.
The points are actual unwrapped integers. Replacing them by their residues
modulo N would erase the lift and invalidate the claimed digit consumer.

Keep the three precisions separate:

    V_R(A) in [0,Q),                   full scalar;
    r(A)=[V_R(A)]_M=1+N^2 u(A),        lower remainder;
    u(A) in [0,N^L),                   lower normalized residue.

The full quotient (V_R-1)/N^2 has one more N digit than u. The accepted
lower interface is

    u(A)=[F(A)]_(N^L),
    F(A)=sum_(k=1..R-1) N^(2k-2) G_k(A^2) in S[A],
    deg(F)<=2R-2, F(A)=A^2/24 mod N^2, F'(A)=A/12 mod N.

The accepted full scalar identity modulo Q has degree at most 2R. Its
j>R tail vanishes using integral raw coefficients and their explicit N
powers; no nonunit distant factorial is inverted. That argument is algebraic
in A and remains valid at these large inputs.

For any polynomial over S, binomial expansion gives

    F(a+h)=F(a)+h F'(a)+h^2 E(a,h),       E in S[a,h].

It needs no extra Taylor-factorial inverses. Set h=12H(s+i t). The derivative
error is in (N), so h times that error is in (N^L). The quadratic and all
higher shift terms are in (N^(2L-2)), contained in (N^L) because L>=2.
There is no upper-size restriction on s+i t for this divisibility argument.
Consequently

    F(A_i)=F(a_i)+H a_i(s+i t) mod N^L.

At the boundary R=2, L=2 and H=N, this reads explicitly

    ((a+12Nz)^2-a^2)/24 = aNz+6N^2 z^2 = aNz mod N^2,
    z=s+i t.

The quadratic term vanishes at exactly the required precision; it was not
silently dropped at a higher precision where it could survive. R=1 is outside
this construction. Its previously accepted constant-remainder case is not a
license to use H=N^(-1) here.

Split the acquired base integers as u_i=v_i+H b_i, with 0<=v_i<H and
0<=b_i<N. Uniqueness of canonical representatives now proves exactly

    X_i(s,t)=[b_i+a_i s+i a_i t]_N,
    u(A_i(s,t))=v_i+H X_i(s,t).                         (1)

There is no carry out of v_i: the displayed integer is already in [0,N^L).

## 3. Integer quotient, sign, and strict bounds

Write lambda_i=(-1)^(m-i) binom(m,i), and Delta x=sum_i lambda_i x_i.
The positive and negative weight totals are each 2^(m-1)=4^R. Polynomial
annihilation on any actual arithmetic progression gives the exact base
integer c0=Delta u/N^L. For

    q_i(s,t)=floor((b_i+a_i s+i a_i t)/N),

(1) gives the integer equality

    u(A_i)-u_i=H(a_i s+i a_i t)-N^L q_i.

Both sum lambda_i a_i and sum lambda_i i a_i vanish: the respective
index-polynomials have degrees one and two, less than m>=5. Therefore

    c(s,t)=Delta u(A_i)/N^L=c0-sum_i lambda_i q_i(s,t) in Z.       (2)

No fractional term is rounded away. Every u(A_i) is canonical, hence

    |c(s,t)| <= 4^R(1-N^(-L)) < 4^R.                            (3)

Let d_i=floor(V_R(A_i)/M). The full degree-at-most-2R polynomial vanishes
under the same order-m difference even when its unit step varies with t.
Thus Delta V_R=Q z for some integer z. Since Delta r=M c and V_R=M d+r,

    Delta d=N z-c,             Delta d=-c mod N.                (4)

This proves both the minus sign and gcd(Delta d,N)=gcd(c,N). It neither
identifies c with an individual digit nor asserts equality of the signed
integers Delta d and -c. Higher terms that may affect individual full digits
are accounted for by this full-precision annihilation.

For real (s,t) in [0,N)^2 define C by the right side of (2), without giving
it an unwrapped-integer scalar interpretation. Set epsilon=Delta v/N^L.
Using floor(y)=y-frac(y) and the two cancellations above yields

    C(s,t)=epsilon+sum_i lambda_i frac((b_i+a_i s+i a_i t)/N),
    |epsilon|<4^R/N,
    |C(s,t)|<4^R(1+1/N).                                      (5)

C is still an integer because its defining c0, weights and floors are
integers. Bound (3) belongs to actual integer lifts; (5) covers the extra
continuous samples. Both bounds give O(R) final bits. Direct accumulation
also has O(R) bits: each floor is at most (i+1)^2, so the sum of absolute
weighted terms is at most (m+1)^2 2^m, before cancellation.

## 4. Thresholds and all literal geometric degeneracies

Use line coefficients

    A_i=i+1, B_i=i(i+1), T_i=A_i+B_i=(i+1)^2,
    d_(i,k)=kN-b_i,
    ell_(i,k): A_i s+B_i t=d_(i,k), 1<=k<=T_i.

The numerator b_i+A_i s+B_i t lies in [0,(T_i+1)N), so these include
every positive threshold. There are exactly

    J=sum_(i=0..m)(i+1)^2=(m+1)(m+2)(2m+3)/6=O(R^3)

line records before discarding lines that miss the interior. k=0 can meet
the domain only where b_i=0: at the origin for i>0, or along s=0 for i=0.
Neither creates an additional floor vector requiring an interior cut.

For an integer point (s,t), increase both coordinates by

    delta=1/[2(m+1)^2].

The new point lies in (0,N)^2. Its ith integer numerator increases by
T_i delta in (0,1/2]. The next strictly larger multiple of N has integer
distance at least one, so no floor changes; an existing equality moves to
its included upper side. The new numerator is nonintegral and cannot lie
on a threshold. Thus every integer output has an open-chamber representative,
including points at the origin, edges, intersections, and the last integer
row/column. This is simultaneous positive perturbation, not processing tied
jumps one at a time. It uses the actual positive gradients, including i=0.

Here is a complete literal interpretation of the target's sampler:

1. Generate the J records. For two lines from different indices i,j the
   determinant is (i+1)(j+1)(j-i), nonzero. Solve exactly by Cramer's rule;
   retain the s coordinate only if both coordinates lie in the closed square
   [0,N]^2. Same-index lines are distinct parallel lines. Skip their zero
   determinant; there are no distinct coincident records in this family.
   A defensive implementation may deduplicate coincident records.
2. For each line, its crossings with t=0,N have s coordinates d/A_i and
   (d-B_i N)/A_i. A_i is always positive, including i=0. Retain coordinates
   in [0,N]. Add 0,N and the coordinates of vertical lines in [0,N].
   The sole i=0 record is s=N-b_0. If b_0=0 it overlaps s=N; retain only
   the already present endpoint, not an infinite list of boundary points.
   A putative added k=0 overlap at s=0 is handled by the same endpoint rule.
3. Sort and deduplicate these rational cuts; use only consecutive distinct
   pairs to make positive-width slabs. At their midpoint s*, form heights
   (d-A_i s*)/B_i only for i>0. Never divide by B_0=0: vertical lines are
   cuts and cannot cross a slab's interior. Keep only heights strictly
   between 0 and N, add 0,N, sort and deduplicate.
4. In each positive-height gap choose its midpoint t*. Evaluate (2) directly
   by exact rational floor division, take gcd(|C|,N), and validate any proper
   factor. Retain unit and full gcd outcomes as failures. Boundary-only lines
   add no active height. Zero-width or zero-height gaps are not sampled.

Unlike the prior arrangement, there are no horizontal lines here. Nonvertical
lines have strictly negative slopes -1/i and cannot overlap a square edge.
Corner-only intersections, repeated pair coordinates, concurrent multiway
intersections, and parallel families merely reduce the deduplicated cut/gap
counts. Crossings through s=0,N need no additional interior cuts; these two
slab endpoints are present. The explicit vertical cuts prevent the missing
chamber defect that would result from treating every line as a height.

For completeness, every open chamber contains a point whose s coordinate is
not in the finite cut list. In its slab, no active height can enter or leave
through t=0,N, and no two nonparallel active heights can exchange order:
every such event was inserted as a cut. There is no vertical boundary inside
the slab. Each successive height gap therefore persists across the slab as
a connected band in one chamber. Its midpoint sample is in that chamber.
An open chamber cannot be confined to one cut coordinate. This proves

    {c(s,t): integer 0<=s,t<N} subset {all sampled C values}.    (6)

A gcd from an extra sample is a valid ordinary factor, but is not assigned
an actual integer-lift witness. Complete unsuccessful traversal rules out a
proper filtered gcd throughout this supplied integer family. An incomplete
traversal does not. No lattice feasibility, orbit-membership, or probability
oracle was used.

## 5. Rational widths, sample counts, and complete cost

Let n=bitlen(N) and U=O(n+log(R+1)). A_i=O(R), B_i=O(R^2),
d_(i,k)=O(R^2 N). Pair-intersection determinants are O(R^3); their
numerators, before square filtering, are O(R^4 N). Boundary-cut denominators
are A_i=O(R). Reduced cut denominators are thus bounded by a fixed Q0=O(R^3).
For retained cuts their numerators are at most N times their denominators.
All cross-products and range comparisons have O(U) bits.

Construct each slab midpoint freshly from its two original adjacent cuts,
not from a growing chain of rational operations. If their denominators are
q,q'<=Q0, write s*=S/Ds with Ds=2qq'=O(R^6). Each nonvertical height is

    (d Ds-A_i S)/(Ds B_i),             denominator O(R^8).

Boundary heights can be represented with B=1. For two adjacent heights
h=U1/(Ds B), h'=U2/(Ds B'), their midpoint is

    t*=(U1 B'+U2 B)/(2 Ds B B') = T/(Ds E), E=2BB',
    Ds E=O(R^10).

This uses only the two adjacent heights; it never forms the lcm or product
of all height denominators. Every floor is computed as the nonnegative
integer division

    (b_i Ds E + A_i S E + B_i T) div (N Ds E).            (7)

Both operands have O(U) bits. Rational reduction is optional and is charged
if performed. Signs during intersection construction and weighted carry
summation are exact. The floor in (7) is mathematical floor, never floating
point or rounding of a signed purported quotient.

There are O(J^2) cut records and O(J^2) slabs, each with O(J) heights and
O(J) gaps. Sorting cuts and the per-slab heights costs respectively
O(J^2 log(J+1)) and O(J^3 log(J+1)) rational comparisons. There are
O(J^3)=O(R^9) samples, each paying O(R) floors and signed-weight operations,
one gcd on n- and O(R)-bit operands, and any witness validation. Under the
accepted fast integer multiplication/division/gcd model, this gives

    soft O(J^2 U+J^3 U+R J^3(U+R)+J^3(n+R))
        = soft O(R^10(n+R)).                            (8)

Soft notation suppresses logarithmic factors in operand and list lengths,
not an unpriced factor n from scalar powering. This is a conservative
mathematical bit bound, not an implementation or Python timing claim.

Base work fits (8): full guards and optional base-point gcds cost soft
O(R n); modulus construction, the accepted coefficient recurrence and
shared acquisition cost soft O(R^2 n); all u/v/b extractions, the signed
c0 numerator and its exact division cost soft O(R^2 n+R^2). The accepted
binomial recurrence generates O(R) weights of O(R) bits with soft O(R^2)
work. For robustness, even ordinary Horner acquisition from the accepted
lower coefficients, at soft O(R^3 n), fits (8); the large slab envelope does
not depend on achieving the faster multipoint bound in an implementation.
It still depends on paid finite-width fast integer arithmetic. Reading
N,R, range checks, all generated/rejected cuts, duplicate visits, every gcd
(including 0/full), factor validation and ordinary record traffic are included.
No full scalar power or lifted stencil is materialized at each sample.

The line arrangement has at most 1+J(J+1)/2=O(J^2)=O(R^6) chambers: inserting
a line cuts its clipped segment at at most the number of previous lines,
so it adds at most one more region than that number. Degeneracies only reduce
the count. Therefore distinct floor vectors and distinct C values also have
this upper bound. It does not upgrade the explicitly charged O(J^3) sampler
to an O(J^2) traversal or supply that many independent factoring trials.

Streaming slabs needs a cut list of O(J^2 U) bits, one height list of O(J U)
bits, O(R^2 n) base storage, O(R^2) weight bits, and arithmetic/evaluation
workspace. A conservative soft bound is O(R^6(n+log(R+1))+R^2 n).
Keeping every sample/carry/gcd record adds O(R^9(n+R)) output storage;
recording every floor vector adds its corresponding data volume. No such
fully retained transcript is assumed by the streaming-space claim.

At R=Theta(n), (8) becomes soft O(n^11) for one complete, possibly unsuccessful
superset traversal. A supplied R need not be polynomial in n; any factoring
schedule must bound its attempted depths, repetitions and preprocessing.
This primitive comparison supplies no matched factoring speedup.

## 6. Exact rank and the scoped uniform-sampling bound

The new family is not an old input stencil under reindexing. Equality of
unwrapped ordered stencils first fixes s by i=0, then fixes t by their step.
More substantially, their normalized residue vectors are all distinct.
If the vector (1) at (s,t) equals the old vector at w, i=0 gives s=w mod N,
and i=1 gives 2(s+t)=2w mod N. Since 2 is a unit, t=0 mod N. In the stated
range, this is precisely t=0,s=w. The same argument between two new pairs
proves N^2 distinct lower-residue vectors. Every fixed-t row has N distinct
vectors, and the old row is exactly t=0.

This vector statement alone says nothing about the many-to-one weighted
quotient. Here is an additional, proved distribution constraint. Only in
this section let s,t be independent uniform integers modulo N. For i!=j,
the affine map to (X_i,X_j) has coefficient determinant

    a_i a_j (j-i).

Every factor is a unit: a_i,a_j are base units, and 0<|j-i|<=m is below
leastprime(N). Its inverse exists over Z/NZ, also for nonsquarefree N.
Thus (X_i,X_j) is exactly uniform on (Z/NZ)^2. All phases are individually
uniform and pairwise independent. They are not mutually independent:
normalizing Y_i=a_i^(-1)(X_i-b_i) mod N gives

    Y_i=s+i t=(1-i)Y_0+i Y_1 mod N.

Every later coordinate is determined by the first two; the joint support
has N^2 points. In particular, pairwise phase independence must not be
promoted to independent carries, independent gcds, or an independent law
for prime-component carry events.

Set tau=Delta v/H. This is an integer because v_i=[F(a_i)]_H and polynomial
annihilation holds modulo H. It satisfies |tau|<4^R. Equation (1) gives

    c(s,t)=(tau+sum_i lambda_i X_i(s,t))/N.

Using the exact mean and variance of a uniform integer in [0,N), together
with the proved pairwise independence, yields

    E[c]=tau/N,
    Var(c)=(N^2-1)/(12N^2) * binom(2m,m),
    E[c^2]=(tau^2+(N^2-1)binom(2m,m)/12)/N^2.          (9)

Here sum lambda_i=0 and sum lambda_i^2=binom(2m,m); the latter follows by
comparing the middle coefficient of (1+x)^m(1+x)^m. No central-limit law
or phase-independence heuristic is invoked.

Let p=leastprime(N), used only in the theorem, not as an algorithm input.
Every proper gcd requires a nonzero c with |c|>=p. Therefore

    Pr_uniform(s,t)[1<gcd(c,N)<N]
      <= min(1, [tau^2+(N^2-1)binom(2m,m)/12]/(N^2 p^2)).       (10)

This follows simply from c^2>=p^2 on the event. It is a new upper bound
for this exact uniform sampler, not a lower useful-yield theorem. If
p>=4^R, (3) gives the stronger exact zero probability and absence of a
proper factor anywhere in the actual family. For the continuous superset,
leastprime(N)>=4^R(1+1/N) similarly rules out every extra gcd as well.
These strict-size conditions include repeated prime factors and c=0, whose
gcd is N. Their converses are not asserted.

Bound (10) does not bound the success of selecting a rare chamber,
conditioning on observed base data with a different parameter law, adaptively
choosing a lift, or exhaustively testing the cover. Chamber counts or areas
are not the exact probability on N^2 lattice points. Thus this distribution
constraint is not an all-selector, all-depth, or all-algorithm lower bound.
No new exhaustive-family obstruction beyond the stated size conditions was
proved in this review.

## 7. Symbolic counterexample to an output-distribution relabeling

There is a cheap exact witness against a stronger degeneracy claim: that,
for every t, the new carry row is merely a permutation of the old row, or
more generally that the whole N^2 carry multiset repeats the old N-entry
multiset exactly N times. No candidate is executed in this argument.

Fix the symbolic depth R=2 and let N=24z+1 be any composite satisfying the
full guard leastprime(N)>5. Such inputs form a nonempty infinite symbolic
family; N=(120v+1)^2 for positive integer v is a sufficient subfamily. Here
m=5, L=2, H=N and F(a)=a^2/24 mod N^2. For a_i=1,...,6 put

    k_i=[-a_i^2]_24=(23,20,15,8,23,12),
    e_i=(a_i^2+k_i)/24=(1,1,1,1,2,2).

Since N^2=1 mod 24 and a_i<N, the exact canonical base value is

    u_i=(a_i^2+k_i N^2)/24.

Moreover N>=49 on the guarded composite branch, so
0<k_i/24+a_i^2/(24N)<1 for every displayed index. Hence

    b_i=floor(u_i/N)=k_i z,
    v_i=u_i-N b_i=k_i z+e_i.

For the signed weights (-1,5,-10,10,-5,1), direct fixed-coefficient
identities give Delta k=-96 and Delta e=-4. Thus

    Delta v=-96z-4=-4N,             tau=-4.

No N value, phase point, parameter grid or gcd was evaluated. These are
polynomial identities valid for the entire symbolic family. Since
binom(10,5)=252, (9) becomes

    E_new[c^2]=21-5/N^2,
    sum_(s,t) c(s,t)^2=21N^2-5.                       (11)

For any old N-entry integer carry list c_old(w), its N-fold repetition
has sum of squares N*sum_w c_old(w)^2, divisible by N. The quantity in
(11) is congruent to -5 mod N, not zero. Thus the new multiset cannot be
that repetition. In particular, there cannot be a permutation pi_t of the
old parameters for every t with c(s,t)=c_old(pi_t(s)). This excludes the
usual affine relabelings in s with a unit coefficient as special cases.

The scope is precise: (11) proves a changed carry distribution on an actual
symbolic input family. It does not prove that some carry value is outside
the old support; equal supports can have different multiplicities. It does
not exclude an arbitrary unbalanced many-to-one map into the old support,
prove that every depth/input changes its distribution, or prove any proper
factor exists. Vector-rank novelty, distribution novelty, support novelty
and useful gcd supply are four different statements; only the first two
are established here at the stated scopes.

## 8. Final disposition and decisive remaining proof

Accept the target as a concrete, uniformly described supplied-(N,R) primitive.
It compresses the N^2 integer parameter family into a polynomial-size
continuous superset and pays a conservative polynomial traversal cost when
R is polynomial in bitlen(N). Its precision, exact divisions, sign, boundary
coverage, vertical-line cuts, rational widths and all sample gcds are justified.
The new parameter is not simply redundant at the residue-vector level and
can alter the carry distribution. No independence assumption was needed;
the limited pairwise result was proved from an invertible two-coordinate map.

Useful factor supply remains the decisive missing statement. The next proof
that could change the factoring disposition is a proper-split cover for an
explicit bounded N-only depth schedule, or a rigorously justified useful
probability for its actual paid sampler, including all guard exits, ordinary
factors, trivial gcds, failed acquisitions, rejected parameters and restarts.
The exact moment bound above is a constraint on such a uniform-sampling
proposal, not evidence for favorable yield. Showing only a larger support
would still leave the divisibility/separation question unanswered.

A complete unsuccessful cover traversal would close this one supplied affine
family; it would not certify primality or rule out a different depth, base,
consumer or factoring algorithm. The two older negative sweeps do not close
this new family, and the newly proved non-relabeling does not overturn those
finite negatives. No new assay is selected, requested or authorized here.

The [validation record](W032-affine-lift-review-evidence/validation.json)
checks byte integrity and live-source drift only. The
[full delivery manifest](W032-affine-lift-review-evidence/manifest.json)
lists this report and every owned payload; its explicit exclusions are the
manifest itself and the two terminal handoff/anchor files, to avoid circular
hashing. Those three files together with all listed payloads constitute the
complete delivery. The manifest's external terminal SHA-256 is returned in
[handoff.json](W032-affine-lift-review-evidence/handoff.json), its sidecar, and
the final response. Integrity hashes establish byte identity, not mathematical
correctness or an independently accepted theorem for section 7.
