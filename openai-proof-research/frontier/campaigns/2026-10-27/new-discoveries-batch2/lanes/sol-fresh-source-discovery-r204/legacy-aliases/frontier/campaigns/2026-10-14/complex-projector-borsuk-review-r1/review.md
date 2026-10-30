# Independent full B8C review, round 1

Myeongjin Kang; no affiliation. 2026-10-16.
Original prose CC BY 4.0; original code MIT. Third-party rights retained privately.

**Mathematics: PASS_FULL_B8C. Contribution: UNRESOLVED. Counted: false.**

The frozen candidate proves the entire assertion: the rank-one complex
3-by-3 projector set in the trace-one Hermitian hyperplane has diameter
sqrt(2) and Borsuk number exactly nine. The lower bound permits arbitrary,
including nonmeasurable, covering subsets. The upper bound supplies nine
actual compact sets of uniformly smaller diameter. This set attains d+1
in dimension eight; it is not a dimension-eight Borsuk counterexample.

This verdict concerns candidate.md SHA256
52256d84ffea02d6c30bccc9ff29d6cebc9f88cbb12a15f265c49b85fd8e0304,
with scope 133c0d45fdd9f4a1c328dee664b142ac2cf09c6d0600fcc1ed53bdb565dea838.
The supplied external seal fc997d93ac553767e1ce252e73e57ffb3c675d36b09d1949c1e8a14f6f9db9af
was checked, including its 416-byte length, before parsing its manifest.
Independent membership/hash checks found exactly 35 files and eight
directories including the root. No author executable was run.

I read the original historical brief at
../linear-ryser-parent/fresh-r16-brief.txt, all 1750 lines, from the
specified parent path, checking SHA256
61a47abea0a23646294b6e3abd1bff6ed012d7980ca4a3d0e16c0464a4dd65e6.
The author's transcription is not used as the original provenance source.
Historical ownership instructions are superseded by this review assignment.
No excluded research target was reopened. PCW and crossing work are separate.

## B1. Arbitrary covers and the Hermitian lower bound — PASS

For unit u,v, trace multiplication gives

    ||P_u-P_v||_F^2 = 2-2|u* v|^2.

Thus the diameter is sqrt(2), attained precisely on orthogonal lines.
The projector map is a continuous injection from compact CP^2 into a
Hausdorff space, hence a homeomorphism onto X. Herm_3 has three real
diagonal entries and three complex off-diagonal entries, real dimension
nine; its trace-one hyperplane has dimension eight.

Assume a finite cover A_1,...,A_m has every diameter d_i<sqrt(2).
For each nonempty member choose t_i=(sqrt(2)-d_i)/4 and its relative
open t_i-neighborhood U_i in X. Given points of U_i, approximation by
points of A_i gives diameter at most d_i+2t_i<sqrt(2). Empty members
have empty neighborhoods. No closure, measurability, or other regularity
of A_i enters this argument. Each U_i is proper, since X has the larger
diameter. Its complement is nonempty and closed, and

    g_i(P)=dist(P,X\U_i),     f_i=g_i/(sum_j g_j)

is continuous, nonnegative, positive exactly on U_i, and sums to one.
Relative openness makes the denominator positive at every point.
Consequently orthogonal lines have disjoint positive-coordinate supports.

For H(w)=||w||^2 f([w]), H(0)=0, the norm identity
||H(w)||_1=||w||^2 proves continuity at zero. The PSD square root is
continuous even when rank changes. On each compact neighborhood of Q,
joint continuity of H(Q^(1/2)u) on that neighborhood times the unit sphere
gives continuity of

    E(Q)=3 integral H(Q^(1/2)u) dmu(u).

Unitary invariance gives integral uu* dmu=I/3, so sum E_i(Q)=tr Q.
This factor is the complex vector dimension three, not real dimension six.

Here is the singular-rank support check explicitly. If E_i(Q)>0, some
nonzero image Q^(1/2)u has its line in ran Q and positive f_i. Conversely,
if w is a nonzero range vector with f_i([w])>0, take
u=Q^(-1/2)w/||Q^(-1/2)w||, using the inverse only on ran Q.
The integrand is positive at u and hence on an open set of positive
spherical measure. This proves the exact support identity at ranks one,
two and three. At Q=0 both supports are empty. There is no assumption
that a lower-dimensional range itself has positive ambient measure.

For Hermitian A, its positive and negative spectral ranges are orthogonal.
Therefore E(A_+) and E(A_-) have disjoint positive coordinate sets.
Their difference F is continuous, odd, and has

    ||F(A)||_1=tr A_+ + tr A_-=tr|A|>0   (A nonzero).

This includes positive or negative semidefinite A and matrices with a
kernel. Normalizing F in Euclidean output norm gives an odd map
S^8 -> S^(m-1). For m<=8, composing with an equatorial inclusion into
S^7 contradicts Borsuk–Ulam (or use its general dimension form).
The empty family cannot cover nonempty X. Hence every cover by at most
eight arbitrary subsets has a member of diameter sqrt(2), as asserted.

The source's real cover-to-map, integral extension, signed extension,
and label-count operations are antecedents. I read their actual proofs;
none of the real equality-case results is imported into this deduction.

## B2. Hesse algebra, all twelve equality rays, and covariance — PASS

Use the candidate's convention <a,b>=a* b, Xv(j)=v(j-1),
Z=diag(1,omega,omega^2). Then ZX=omega XZ and X^3=Z^3=I.
Applying these operators to (0,1,-1)/sqrt(2) gives exactly the three
displayed groups of s_{a,b}. The eight nonidentity displacement overlaps
have modulus 1/2: for a=0 their sum is (omega^b+omega^(2b))/2,
and for a=1,2 only one coordinate product survives. Covariance therefore
checks every one of the 36 distinct SIC pairs, not a sample.

For a fixed c, the inner product of v_{c,a},v_{c,a'} is
(1/3)sum_j omega^((a'-a)j), so each B_c is orthonormal.
For different c,c', put d=c'-c nonzero and e=a'-a. The squared modulus
of sum_j omega^(d j^2+e j) is three: in the double sum set j=k+t;
for t nonzero the sum over k of omega^(2dt k) vanishes, and t=0
contributes three. Thus cross-basis squared overlaps are 1/3.
The standard basis has the same unbiasedness with every B_c.
All twelve rays are consequently distinct; orthogonal hole pairs occur
only inside the same listed basis.

At e_0 the SIC scores are three zeros and six halves. At v_{c,0}
the three groups reduce, including their removable unit phases, to

    |1-omega^(-b)|^2/6,
    |1-omega^(c+b)|^2/6,
    |1-omega^(c-b)|^2/6.

Each has one zero and two halves. Within each basis no SIC can be
orthogonal to two poles: it would equal the remaining pole, whose score
would then be one, contrary to these formulas. This proves the triple
partition, four incidences per SIC, and all twelve Hesse lines.

For a triple in span(p,q), simultaneous phase normalization of s and
its attached d makes <p,s>=1/sqrt(2) and
s=(p+conj(gamma_s)q)/sqrt(2). Pairwise SIC overlaps give
Re(gamma_s conj(gamma_t))=-1/2. The triple is exactly a rotated set of
cube roots. This conclusion holds for either of the two triples used
at every hole.

For the covering equality classification, put p_j=|u_j|^2. For any
coordinate pair the maximum squared SIC score is

    (p_a+p_b+2 sqrt(p_a p_b) mu_ab)/2,    1/2<=mu_ab<=1.

Choose c with minimal p_c. Then sqrt(p_a p_b)>=p_c, proving M_0>=1/2.
Equality forces sqrt(p_a p_b)=p_c. If p_c=0, another coordinate is zero
and u is a coordinate ray. Otherwise all three p's are 1/3; all three
mu's must then be 1/2. For three equally spaced angles the maximum of
their negative cosines is 1/2 exactly when their angles are the cube-root
angles. After setting u_0 positive, u=(1,omega^alpha,omega^beta)/sqrt(3).
The map (c,a)->(c+a,c+2a) has determinant one modulo three, so these
are exactly the nine v_{c,a}. The converse follows from the scores above.
This covers zero-coordinate and repeated-minimum cases too. There are
no additional equality continua.

The exact basis actions are

    Z v_{c,a}=v_{c,a+1},
    X v_{c,a}=omega^(c-a) v_{c,a+c}.

X shifts the standard basis; Z fixes its rays. These are translations
of the cyclic labels, so they preserve the successor rule on every basis,
including c=0 where X has zero shift. A displacement permutes the
attached pairs (s,d_s) up to the SAME phase. The expression defining
kappa is invariant under that simultaneous phase and under the hole
phase. This is the covariance needed later, not covariance under an
unspecified Clifford action.

The unperturbed cell for any s contains the two nonorthogonal-to-s poles
from each basis. Those two poles are orthogonal to one another, with score
1/2 equal to the global maximum. Hence its diameter really is sqrt(2).

Original editorial error: Section 3 says “nine holes” and immediately
lists and correctly counts twelve. It must say “twelve holes” in a future
revision. No frozen bytes were changed, and the proof uses all twelve.

## B3. Favored derivatives and the entire complex neighborhood — PASS

The fiducial tangent d_0=(1+i)(0,1,1)/2 has norm one and is Hermitian
orthogonal to s_0. At the four favored poles of lines through s_0,
the relevant products are

    <d_0,e_1><e_1,s_0>=(1-i)/(2 sqrt(2)),
    <d_0,v_{c,1}><v_{c,1},s_0>=(1+i)/(2 sqrt(6)).

For the latter calculation the factors are
-(1-i)omega^c/(2 sqrt(3)) and -i omega^(-c)/sqrt(2).
Their product has the sign printed in the candidate. Thus the four
real parts are positive, with minimum 1/sqrt(24). Covariance proves
this for all 36 favored line/SIC incidences. The derivative at epsilon=0
of the squared score is 2 kappa, because normalization by 1+epsilon^2
has zero first derivative. No claim that both poles of an orthogonal
pair improve for a fixed center is needed.

Fix a hole h, with other poles h',h'', where L(h'') favors h.
Choose the phase of u to write

    u=(h+z_2 h'+z_3 h'')/N,   N^2=1+|z_2|^2+|z_3|^2.

For s in the favored trio, normalize (s,d_s) together so
s=(h+conj(gamma)h')/sqrt(2). Define delta_j=<d_s,b_j>, where
(b_0,b_1,b_2)=(h,h',h''). Then D=delta_0+delta_1 z_2+delta_2 z_3.
These are bra coefficients; conjugating them again would be an error.
Direct expansion gives, with a=|z_2|, b=|z_3|,

    2N^2(1+epsilon^2)(x_{s(epsilon)}(u)-1/2)
      =2 Re(gamma z_2)-b^2
       +2 sqrt(2) epsilon Re(conj(1+gamma z_2)D)
       +2 epsilon^2 |D|^2-epsilon^2 N^2.

Because sum |delta_j|^2=1, Re D>=Re delta_0-|z| and
|conj(gamma z_2)D|<=|z|(1+|z|)<=2|z| when |z|<=1.
Also Re delta_0=sqrt(2) kappa. The phase choice may depend on h;
this changes no perturbed ray because d_s is changed with s.

Let c=1/sqrt(12), r=c/6=1/(12 sqrt(3)), |z|<r and
0<epsilon<=1/50. In the favored trio every Re delta_0>=c, while
some gamma has Re(gamma z_2)>=a/2 for EVERY complex z_2.
The displayed expression for that member therefore exceeds

    a-b^2+(1/sqrt(6))epsilon-2epsilon^2.             (F)

For the other trio swap z_2,z_3 and use only Re delta_0>=-1.
Some member has the expression at least

    b-a^2-(2 sqrt(2)+1/sqrt(6))epsilon-2epsilon^2
      >= b-a^2-(13/4)epsilon-2epsilon^2.            (O)

Here are exact checks replacing any dependence on decimal rounding:

* r<1, r^3=1/(5184 sqrt(3))<1/1000.
* 1/sqrt(6)>2/5, since 1/6>4/25.
* 2 sqrt(2)+1/sqrt(6)<13/4. For example sqrt(2)<99/70 and
  1/sqrt(6)<41/100; their resulting sum 2267/700 is <13/4.
* N^2<2; dropping the nonnegative 2epsilon^2|D|^2 is legitimate.

If b^2<=a, (F)>epsilon(1/sqrt(6)-2epsilon)>0.
If b^2>a, then a^2<b^4<r^3 b<b/1000. For b>=4epsilon,
(O)>epsilon(3996/1000-13/4-1/25)=353epsilon/500>0.
For b<4epsilon, (F)>epsilon(1/sqrt(6)-18epsilon), which is
greater than epsilon(2/5-9/25)=epsilon/25>0.
These cases exhaust the full four-real-dimensional complex chart.

In particular z_2=z_3=0 and z_3=0 use the first case. If z_2=0,
the two subcases in the second case cover every b>0, including b much
smaller than epsilon. For z_2 nonzero no complex phase makes the
maximum over its three gamma's vanish; the worst value a/2 includes
ties. The boundaries b^2=a, b=4epsilon, and epsilon=1/50 are included
by the stated weak inequalities with strictly positive residual bounds.
The boundary |z|=r is not asserted by this open-chart lemma; it belongs
to the compact far-region argument. Epsilon=0 is deliberately excluded.
There is no untested degenerate direction or omitted scale regime.

## B4. Compact complement, uniform margin, and strict cells — PASS

The twelve B_h are well-defined open projective sets, with |z|<r in
the corresponding charts, and contain their respective holes. Their
complement K is compact. It is also nonempty: s_0 lies in none of them.
Indeed membership in B_h would require |<h,s_0>|^2>1/(1+r^2)>1/2,
whereas each of these twelve scores is zero or 1/2. Thus the candidate's
min_K is defined without an empty-set convention. This is an immediate
consequence of its earlier overlap formulas, not a repair of the cover.

The equality classification gives M_0>1/2 on K. Hence its continuous
minimum has a positive gap eta. For t>=0,
2-2/sqrt(1+t)<=t: the difference t-2+2/sqrt(1+t) is zero at zero
and has derivative 1-(1+t)^(-3/2)>=0. With t=epsilon^2 this proves
||s(epsilon)-s||<=epsilon uniformly over the orbit. The score difference
is at most 2||s(epsilon)-s||, by factoring the difference of squared
absolute inner products. Taking maxima preserves that bound.

Choose ANY positive epsilon<=min(1/50,eta/3). On K,
M_epsilon>=1/2+eta-2epsilon>=1/2+eta/3. On the twelve open sets
the local proof gives M_epsilon>1/2. These regions cover all CP^2.
Continuity and compactness now give a GLOBAL positive number

    delta=min_CP^2 (M_epsilon-1/2)>0.

This second compactness step makes the overlap margin uniform even though
the local lemma was stated pointwise. An explicit eta or epsilon is not
needed for the existential frozen upper bound.

The equality-to-maximum sets A_s are closed and cover X, including ties.
Each lies in x_{s(epsilon)}>=1/2+delta. Bessel gives
x_s(u)+x_s(v)<=1 for orthogonal u,v, so A_s has no orthogonal pair.
Every A_s is compact, and its continuous pairwise distance attains a
maximum. That maximum cannot be sqrt(2), by the projector formula.
Each diameter is therefore STRICTLY smaller than sqrt(2). This compactness
is essential: absence of orthogonal pairs in an arbitrary nonclosed set
alone would not give a strict supremum. Empty cells, if present, cause
no problem; each center in fact belongs to its own cell.

With the convention d_FS([u],[v])=arccos|<u,v>|, the same global delta
gives nine closed balls of radius arccos sqrt(1/2+delta)<pi/4 covering
CP^2. Hughston–Salamon use twice this distance, a normalization difference
accounted for in the comparison. No optimum covering radius is claimed.

## B5. Contribution — UNRESOLVED, independently of mathematical PASS

The lower-bound operation is a routine Hermitian transfer of the pinned
source and receives no substantiality credit. The Hesse configuration,
its twelve MUB normals, the Weyl–Heisenberg action, and the SIC family are
established antecedents. I read the actual entire Hughston–Salamon paper,
including its classification proof, and the relevant full body sections
of other primary papers listed in primary-reading-source-contracts.md.

The candidate's remaining operation is specific and mathematically paid:
a cyclic assignment compatible with the WH action, one fiducial tangent
with four favorable derivative signs, and a uniform two-trio estimate
that removes every old equality hole and excludes shifted nearby holes.
The compactness and Bessel/Voronoi consequences are standard once that
estimate is established. operation-comparison.md explains why neither SIC
classification nor packing optimality supplies this operation, and why
average quantization bounds are different from this worst-case cover.

The bodies actually read do not exhibit an identical strict nine-center
construction. That is insufficient for a substantiality or priority PASS:
the focused search did not exhaust worst-case complex projective covering
tables, non-SIC WH codebooks, or older quantization/covering constructions.
Nor did it find an antecedent allowing a justified DUPLICATE verdict.
I therefore leave contribution UNRESOLVED, rather than infer SUBSTANTIAL
from a new dimension or a missing search hit, or infer TECHNICAL solely
from the brevity of a valid proof. No acceptance/count increase follows.

## Original gaps, repairs, and limits

No blocking proof gap was found; this is a PASS of the frozen proof,
not of an unannounced replacement proof. The independent expansions,
exact rational checks, and explicit demonstration K is nonempty above
spell out implications already available from its formulas.

Future editorial corrections: change “nine holes” to “twelve holes”;
state K is nonempty using s_0; print exact bounds instead of rounded
decimals; fix the provenance receipt's “no repository original” sentence.
These proposed edits were not made. The original thin novelty screen is
an actual contribution-assessment gap; no editorial change cures it.

I inspected the full floating-point diagnostic before deciding it was
unnecessary. It was not executed, and its sampled minima at epsilon=.01,
.02 or .05 supply no universal proof or certified epsilon. No broad
mathematical scan, upstream truth audit, manuscript, Lean package, shared
edit, staging, commit, upload, publication, or nested delegation occurred.
The integrity verifier and its controls establish byte identity only.
