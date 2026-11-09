# W005 orthogonal-pair review

Date: 2026-10-08. Independent narrow review of the post-launch parent note.
**All recommendations and additional deductions await parent disposition.**
Verified new complete factoring improvement: **NONE**.

This review does not consume, repeat, supersede, or wait for
`factoring-w005-quaternion-validation-r1`. In particular, reflection realization,
its scalar domination, and acquisition of the initial quaternion are outside
this review. No candidate, numerical search, mathematical program, experiment,
Lean check, package change, or recursive delegation ran. Tool execution was
limited to document/source retrieval, PDF rendering, hashing, and report writing.

## Recommendations

- **Accept the supplied-pair extraction lemma** for positive odd N and integer
  coordinates, with no primitivity hypothesis. Signs and multiplication sides
  are correct. Both contents, not just g_V, are proper factors for a pair outside
  the stated union of at most twelve exceptions.
- **Accept the finite lattice search with explicit width accounting below.**
  It is a complete exact search, not a polynomial-time shell solver. Its
  N^(2/3) scan count requires a well-conditioned, isotropic basis and is only a
  shape-qualified work estimate.
- **Accept the denominator-N representation as an exact bijection. Correct
  the subsequent claim about arbitrary rational rotations.** The preservation
  statement applies to multiplication on a specified side, not every rotation
  with a denominator coprime to N.
- **Additional reverse reduction:** for primitive integer A of odd composite
  norm N, *any supplied proper divisor* of N allows deterministic polynomial-bit
  construction of a nonexceptional twin. No coprimality of the two factors or
  squarefree assumption is needed. This is not an N-only generator.
- **Prior art:** the useful-twin-to-factoring route is already explicit in the
  cited literature. No novelty claim is supported for the route or for a fast
  generator. The projector/content proof is a convenient elementary formulation;
  this limited source check does not establish its originality.

## 1. Projector, Frobenius calculation, and prime powers

Use Hamilton multiplication, ij=k, jk=i, ki=j, and define L_u(x)=ux,
R_v(x)=xv. A bar denotes quaternion conjugation. Put V=B bar(A),
W=bar(A) B. Orthogonality gives Re(V)=Re(W)=0, and both norms are N^2.
In particular V^2=W^2=-N^2. The side/sign checks are

    V A = N B,       A W = N B,
    V B = -N A,      B W = -N A.

Thus T=L_V R_W has T(A)=-N^2 A and T(B)=-N^2 B. Left and right
multiplication commute; each factor is skew-symmetric, so T is symmetric,
T^2=N^4 I, and tr(T)=4 Re(V)Re(W)=0. Since N>0, A and B are independent.
The remaining two eigenvalues are +N^2. Consequently the parent's identity is
exactly

    T = N^2 I - 2N(aa^T+bb^T).

For i,j in {1,2,3}, let M_ij=L_(e_i) R_(e_j). Each M_ij is symmetric,
integral, and traceless. Right multiplication reverses the order in operator
composition, so

    tr(M_ij^T M_kl)
      = tr(L_(e_i e_k) R_(e_l e_j))
      = 4 Re(e_i e_k) Re(e_l e_j)
      = 4 delta_ik delta_jl.

This verifies the handedness in the Frobenius calculation. It gives the
stronger explicit equality

    4 V_i W_j = -2N(a^T M_ij a + b^T M_ij b).

The parent only needs N | 4 V_i W_j. Oddness makes 4 invertible modulo N,
yielding N | V_i W_j. No coordinate primitivity entered this proof.

For p^e || N, put s=min_i v_p(V_i), t=min_j v_p(W_j), with v_p(0)=infinity.
Neither entire vector is zero. Taking coordinates attaining these minima gives
s+t>=e. Truncating at e preserves the inequality:

    v_p(g_V)+v_p(g_W)=min(e,s)+min(e,t)>=e.

Hence N | g_V g_W, including repeated primes. The proof uses primes only to
justify the integer assertion; extraction does not know them.

If g_V=N, then V/N is an integral pure quaternion of norm 1, hence one of
the six signed axes u. Multiplying V=N u on the right by A gives B=u A.
Conversely B=u A implies g_V=N. Similarly g_W=N iff B=A u.
If g_V=1, the product divisibility forces g_W=N; the swapped argument also
holds. Therefore avoiding both sets forces

    1 < g_V < N,       1 < g_W < N.

The union is a sufficient exclusion set, not the exact set of failed gcds.
For example a right-unit exception can still have 1<g_V<N. Products, contents,
norm checks, and comparisons have polynomial bit cost: |A_i|,|B_i|<=sqrt(N)
and |V_i|,|W_i|<=N.

For orientation terminology, when A and B are nonzero rank-one matrices modulo
an odd p|N, V=0 is the common-right-kernel condition, whereas W=0 is the
common-image condition. If either quaternion vanishes modulo p there is no
corresponding unique line; retain the content proof instead. The scalar
Norm(A-B)=2N indeed has gcd N with N, so it does not resolve these two sides.

**Without primitivity:** all of the above survives. For the orthogonal lattice,
however, if c=gcd(A_0,A_1,A_2,A_3), its covolume is sqrt(N)/c, not sqrt(N).
If c>1, then c^2|N and c itself is already a proper factor for N>1.
An imprimitive B supplies the same immediate content factor.

## 2. Finite lattice search and coefficient sizes

For primitive A, L=A-perp intersect Z^4 is saturated, has rank three and
covolume sqrt(N), so det(G)=N for a genuine integer basis H. A collection of
three independent orthogonal vectors is not enough: it must span all of L.
The dual coordinate vector H G^(-1)e_i has squared norm (G^(-1))_ii and
inner product t_i with Ht. Cauchy-Schwarz therefore proves the stated bounds.
In this primitive case they simplify to the especially convenient formula

    B_i = floor(sqrt(cofactor_ii(G))).

Use integer square roots; no floating-point boundary decisions are necessary.
After permuting basis columns to scan the two smallest bounds, put

    alpha = G_33 > 0,
    beta  = G_13 t_1 + G_23 t_2,
    gamma = G_11 t_1^2 + 2G_12 t_1 t_2 + G_22 t_2^2 - N.

The remaining equation is alpha t_3^2+2 beta t_3+gamma=0. It has integer
solutions precisely when D=beta^2-alpha gamma is nonnegative, its integer
square root s satisfies s^2=D, and alpha divides -beta+s or -beta-s.
Reconstruct both distinct roots and check the result. Every exact-shell point
has its unique basis coordinates in the enumerated box, proving completeness.

There is no width gap if the basis routine is fixed. Here is one elementary
choice, independently checked from the displayed Bezout construction in the
parent's reference. Permute A's coordinate positions for this lattice
calculation so that, writing A=(a,b,c,d), both g_1=gcd(a,b) and g_2=gcd(c,d)
are positive. A primitive A with N>1 has at least two nonzero coordinates, so
this is possible. Choose bounded Bezout coefficients
ax+by=g_1, cz+dw=g_2. A basis consists of

    (g_2 x, g_2 y, -g_1 z, -g_1 w),
    (b/g_1, -a/g_1, 0, 0),
    (0, 0, d/g_2, -c/g_2).

Indeed gcd(g_1,g_2)=1 forces the two partial inner products of any lattice
point to be r g_1 g_2 and -r g_1 g_2; subtracting r times the first column
leaves exactly the last two columns' integer spans. Undo the coordinate
permutation afterward. Zero members of a pair are handled by the elementary
one-coordinate Bezout solution. N=1 is a separate constant case.

Bounded Bezout coefficients and |A_i|<=sqrt(N) give |H_ij|=O(N), hence
|G_ij|=O(N^2), cofactors O(N^4), and all B_i=O(N^2). Throughout the scan,
beta=O(N^4), gamma=O(N^6), D=O(N^8); all have O(log N) bits. These loose
envelopes suffice for the parent's per-slice polynomial-bit assertion. Any
optional reduction must itself have a stated polynomial-bit implementation.
Alternatively keep the unreduced explicit basis. Stream results rather than
storing all points. Basis acquisition is polynomial-bit and the complete
conditional search cost is

    C_A + poly(log N)
        + O((2B_(1)+1)(2B_(2)+1) poly(log N)).

For nonprimitive A, first divide the normal vector by its content; the same
lattice is obtained but det(G)=N/c^2 and B_i=floor(c sqrt(cofactor_ii(G))).
Factoring should already have stopped on c>1.

The N^(2/3) estimate follows if all singular values of H are Theta(N^(1/6)),
equivalently the eigenvalues of G are Theta(N^(1/3)). Merely giving three
column lengths of that size without angle control would not justify inverse
Gram bounds. This conditional two-coordinate scan does not suggest an
improvement over the supplied N^(1/5) deterministic comparator. It is neither
a lower bound on all shell algorithms nor an all-input upper bound of that
exponent. Fixed dimension, LLL, ball enumeration, and the abundance of the
twelve known points do not provide fast useful exact-shell generation.

## 3. Denominator-N representation: accept, but sharpen its obstruction

The maps

    B -> C=B bar(A),          C -> B=C A/N

are inverse bijections between integer B perpendicular to A and pure integer
C satisfying C A=0 mod N. Their norm relation is Norm(C)=N Norm(B).
Thus imposing Norm(C)=N^2 is exactly the old norm-N shell condition. This
holds without primitivity. For primitive A the congruence lattice has
covolume N^2: the map scales all three lengths by sqrt(N), and the original
lattice has covolume sqrt(N). Constructing its basis does not solve its shell.

More specifically, the *reduced common denominators* of the unique one-sided
rational multipliers B A^(-1)=V/N and A^(-1)B=W/N are

    d_L=N/g_V,       d_R=N/g_W,       d_L d_R | N.

A nonexceptional pair necessarily has 1<d_L,d_R<N. If d_L=1 it is a left
unit exception; if d_L=N, then g_V=1 and it is a right unit exception.
The same statements hold after exchanging sides. Therefore a reduced
denominator coprime to N cannot help, and neither can a genuinely reduced
full denominator N. The notation C/N remains valid, but its useful outputs
necessarily contain a proper cancellable factor g_V in the numerator.

This is a **decisive obstruction to the one-sided denominator-selection
generator**, including compositions of norm-one multipliers whose
denominators remain coprime to N. It is not an obstruction to arbitrary
two-sided rotations or to all exact-shell algorithms. Selecting a proper
reduced denominator already supplies a factor; starting with the unreduced
denominator N leaves the nontrivial content to be generated and paid for.

The parent's unqualified assertion about rational rotations is false. A
symbolic counterexample family uses P=x+y i and Q=z+w j, with all four
integer parameters nonzero and |x|!=|y|, |z|!=|w|. Put

    A=P Q=(xz,yz,xw,yw),
    B=P k Q=(yw,-xw,-yz,xz).

The fixed map T(a,b,c,d)=(d,-c,-b,a) lies in SO(4,Z), has denominator 1,
and gives B=T(A). These A,B are equal-norm and orthogonal. Furthermore

    B A^(-1)=P k P^(-1),       A^(-1)B=Q^(-1) k Q

each have two nonzero imaginary coordinates, so neither is a signed axis:
B is nonexceptional. Choose the two sum-of-two-square norms odd if desired.
There is no factoring speedup hidden here: Norm(A)=(x^2+y^2)(z^2+w^2), and
acquiring this special product representation already exposes the factors.
This counterexample is a symbolic derivation, not an executed test.

Replace the parent's sentence by: "An invertible left multiplier modulo p
preserves the right kernel; an invertible right multiplier preserves the
image. General rotations require a separate analysis." Multiplication on
the right generally moves the right kernel, even with denominator 1.

## 4. Reverse reduction from a supplied factor

**Additional theorem for parent review.** Given primitive A in Z^4 with odd
Norm(A)=N>1 and a supplied integer 1<f<N dividing N, one can construct a
nonexceptional integral twin in deterministic poly(log N) bit time. There
are no further exceptions under these hypotheses, including prime powers.
The output twin need not be primitive.

First compute a greatest common *right divisor* Q of A and the scalar f in
the Hurwitz order, and choose a Lipschitz left associate of Q. Write
h=Norm(Q). Because Q divides A, h is odd; then P=A bar(Q)/h is also
Lipschitz: a Hurwitz quaternion with coordinates having odd denominators
cannot have strict half-integer coordinates. Both P and Q are primitive,
since any rational prime content would divide A.

The odd prescribed-norm divisor theorem supplies a right divisor D of A
of norm f; it is also a right divisor of f=bar(D)D. Thus D right-divides Q
and f|h. This is the existence theorem stated as Theorem 2.2 in
[Machiavelo-Rocadas, p. 3](https://cmup.fc.up.pt/main/sites/default/files/publications/Quaternions_AM_LR.pdf),
not a factorization subroutine invoked by the construction. Conversely,
Q right-divides f, so f bar(Q)/h is Hurwitz and, since h is odd, Lipschitz.
Primitivity of Q then gives h|f. Therefore h=f and A=P Q with
Norm(P)=N/f. Computing Q requires no factorization of f or N/f.

For completeness, the Hurwitz Euclidean algorithm is polynomial-bit here.
Choose the nearer of the integer and all-half-integer grids in each division.
Its squared distance is at most 1/2: for coordinate residual magnitudes
t_i in [0,1/2], the two squared distances are bounded by
(sum t_i)/2 and 1-(sum t_i)/2. Thus remainder norm at most halves each
step. Starting norms are at most N^2, giving O(log N) divisions with
O(log N)-bit operands. Checking the 24 units for an integral associate and
computing P take polynomial additional work.

Now form just the three twins

    B_u=P u Q,       u in {i,j,k}.

A candidate is a left exception iff P u P^(-1) is a signed coordinate
axis; it is a right exception iff Q^(-1)u Q is a signed coordinate axis.
Each of the two primitive, odd-norm, nonunit factors can rule out **at most
one** of the three axes. To prove this assertion, if conjugation by an
integer quaternion R maps two distinct axes to signed axes, orthogonality
and orientation force its entire 3-by-3 rotation matrix to be an integral
signed permutation. For R=(r_0,r_1,r_2,r_3), h_R=Norm(R), the usual diagonal
entries of this matrix then imply h_R | 4r_i^2 for every i. Any odd prime
dividing h_R divides every r_i, contradicting primitivity. The inverse
conjugation has the same property.

At most two axes are excluded by the union of the two tests. At least one
B_u therefore lies outside all twelve exceptions. Norm multiplicativity
and inner-product scaling under left and right multiplication
prove Norm(B_u)=N and <A,B_u>=0. Everything uses O(log N)-bit coordinates.
Explicit comparison against the twelve known vectors selects a good output.

Consequently, for a **supplied primitive A**, a nonexceptional twin exists
iff N is composite (N>1 odd). The forward implication is the extraction
lemma; the reverse follows by choosing any factor in this theorem. The
finite lattice scan therefore cannot legitimately exhaust without success
on this promised composite/primitive domain. Exhaustion remains appropriate
for prime controls and for broader unproved input promises. This is a
polynomial search reduction in both directions *with A supplied*. Obtaining
A from N remains a separately charged computation, and constructing P,Q
above uses the known factor. Neither direction supplies a free N-only
generator or a new factoring upper bound. In particular, factoring N by an
existing comparator and applying this reverse construction is an honest
shell-solver baseline of T_fact(N)+poly(log N) with A supplied. The literal
two-coordinate scan is not the best known upper bound for this search problem.

## 5. Prior art, scope, and next decisive question

The factoring reduction is already explicit after Theorem 3.4 on printed
p. 5 of
[Machiavelo-Rocadas](https://cmup.fc.up.pt/main/sites/default/files/publications/Quaternions_AM_LR.pdf):
the missing computation is insertion between quaternion factors. Its Lemma
4.2 and Theorems 4.3-4.4 address the lattice and vector-product route.
This is stronger evidence of prior art than the introduction alone.
[Kiss-Kutas, Lemmas 3.1-3.4 and Theorem 3.5](https://ewkiss.web.elte.hu/wp/wordpress/wp-content/uploads/2014/11/Int4vec9.pdf)
give the twin/common-divisor structure and two-sided decomposition. Their
proof recursively removes prime-norm divisors; it does not provide unfactored
N with an efficient useful-twin generator. Do not turn that classification
into an algorithmic assumption. No complete literature survey was attempted.

**Disposition recommendation: revised.** Accept the extraction and finite
search, correct the rotation scope, and review the strengthened denominator
and reverse-reduction deductions. The new reverse operation is actual unit
insertion after a paid gcd with a known factor; it is useful for understanding
the reduction, not for meeting the N-only contract. The scoped denominator
obstruction above closes the proposed one-sided parameter escape without
making a general lower-bound claim.

**Next decisive computational question:** Can a concretely specified
factor-blind operation on (A,H,G) produce a nonexceptional exact-shell point
without taking a proper divisor as input or preselecting it as a denominator,
and with total work below the matched factoring comparator? In particular,
before testing a binary-slice proposal, specify the actual representation
algorithm, all discriminant/class computations, input acquisition, failure
law and complete slice budget. Under the reverse theorem proposed here,
existence is guaranteed on the primitive composite domain; the question is
useful-point cost, not existence or LLL shortness. If a bounded screen is
selected, first freeze its primitive,
corpus, controls, budgets and rejection criterion in a separately authorized
protocol; a full algorithm comparison belongs in the existing harness.
No experiment is preregistered or recommended for immediate execution here.

Evidence is under `W005-orthogonal-review-evidence/`: frozen rules, the
original wave and new parent briefs, source identities, input hashes, and
PDF page renders. Visually checked conjugation-sensitive passages include
Machiavelo-Rocadas pp. 3, 5, 7 and Kiss-Kutas pp. 6-7. Sources were also
opened through their primary URLs. Source retrieval and document rendering
are not mathematical execution or experimental evidence.
