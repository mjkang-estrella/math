# W004 — explicit twisted packets and the independent-field square condition

2026-10-08. **UNACCEPTED: every new deduction below requires a NEW independent
review. Verified new COMPLETE classical factoring improvement: NONE.**

The accepted W003 two-row packet supplies the first field's twisted target.
I extend it to a paid rational rotation family, give an exact second-field
square test and valid root extraction, and identify its remaining rational-point
problem. Its elliptic norm quotient has a known rational point, but a useful
point must pass two further square lifts and the actual field-square condition.
No such witness supply or useful completion mass is proved. A second, reciprocal
packet law forces square norms in both fields; it still has an explicit
genus-five target-point problem. Neither attempt improves complete factoring.

Only symbolic derivation, source inspection, archiving and document authoring
were performed. No numerical examples, mathematical execution, implementation,
experiment, Lean action or delegation occurred. After the in-flight update,
I read the completed 322-line norm-gate review and both new dispositions;
the review hash matches 6418998b6e1e3f5e3708011ca7e8c4261f66b98be6aee1b57558f815fe521269.
The Lens B review itself was not read. Its integer algorithm is not imported.
The original local briefs, parent note and dispositions remain preserved in
[direct inputs](W004-biquadratic-evidence/inputs.json); the user's lifecycle
overrides and exact in-flight update are [preserved separately](W004-biquadratic-evidence/assignment-override.txt).
[Appended inputs](W004-biquadratic-evidence/update-inputs.json) preserve the newly
accepted material without changing any frozen original. Acceptance applies only
to W003's scoped findings; W004's selector and new deductions remain UNACCEPTED.

## 1. Independent selector checks and cost

Write n=bit_length(N). Paid preprocessing precedes the promised branch
gcd(N,30)=1, 1<=R<N, R a unit square; the inner program never receives x.
Use the verified Norm2 output, at charged cost C_norm(N,R) and space S_norm.
Existence needs no sampler premise: over each odd prime the two sets of squares
and 5R minus squares intersect; a nonzero coordinate gives a nonzero derivative,
so the solution lifts to prime powers and combines by CRT. This is an existence
proof, not permission to use the unknown factorization. The deterministic
reference sorts the two full N-record lists by (residue,coordinate), merges,
and takes the first match. The accepted fixed-multitape realization costs
O(N n^2) time and O(N n) working bits, including sequential access.

There are fewer than 2n distinct prime divisors of NR. Thus an eligible prime
ell>=7 occurs among the first 2n+4 primes. Rosser–Schoenfeld (3.13), read on
printed p.69, gives p_k<k(log k+log log k) for k>=6. Hence ell=O(n log n).
Scanning all integers through this bound and testing primality by trial division
costs O((n log n)^(3/2) poly(log n)) for the small primality tests, plus
O(n log n poly(n)) for divisibility/gcd checks against NR. Any proper factor
of N encountered is a paid factor return; otherwise skip primes dividing NR.
No factor or auxiliary prime is supplied as advice.
[Primary bound](https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf).

Put t=2R and c=2t in F_ell. Counting (z-y)(z+y)=c^2 gives ell-1 solutions,
since c!=0 and 2 is invertible. Thus sum_z chi(z^2-c^2)=-1. There are exactly
two zero arguments, (ell-3)/2 arguments with character +1 and (ell-1)/2 with
character -1. **These count z arguments, not distinct polynomial values.**
Every z is a sum of two squares: two subsets of size (ell+1)/2 intersect.
Both requested pairs therefore exist. Scan (a,b) lexicographically in
{0,...,ell-1}^2, retaining the first pair for each sign. Modular exponentiation
for each character test costs O(ell^2 poly(log ell)) bit operations in total.

The stated CRT and shifts give 4Nell<=u_i<5Nell, 0<=v_i<Nell, and

    16N^2 ell^2 <= s_i < 26N^2 ell^2,
    (s_i-1)^2 < Delta_i=s_i^2-16R^2 < s_i^2.

The second inequality follows from 0<16R^2<2s_i-1. Thus Delta_i is positive
and nonsquare. Also s_i=5R mod N, f_i(R)=0, f_i'(R)=-3R mod N, and
Delta_i=9R^2 mod N. Both s_i and the derivative image are units.
The product Delta_1 Delta_2 has character -1 modulo ell and cannot be a
rational square (an integer rational square is an integer square).
Consequently K_1 and K_2 are distinct real quadratic fields and s_1!=s_2.
Both roots of each f_i are positive. All coefficients have O(n) bits;
CRT, exact integer square tests, gcds and validation add poly(n) overhead.

Set d_i^+=s_i+2t and d_i^-=s_i-2t; both are positive. The tests in the brief
are exact: if alpha_i=w^2 in K_i, integrality gives integer Tr(w) and
Norm(w)=+t or -t, so Tr(w)^2=d_i^+ or d_i^-. Conversely

    (alpha_i+t)^2=d_i^+ alpha_i,
    (alpha_i-t)^2=d_i^- alpha_i.

An integer square root k of d_i^- returns k mod N; one of d_i^+ returns
k/3 mod N. Verify each output. On the remaining branch neither d_i^+ nor
d_i^- is a rational square. No frequency is inferred for these branches.

## 2. Actual biquadratic extension and norm information

For beta_i^2=alpha_i put r_i=beta_i+t/beta_i, q_i=beta_i-t/beta_i.
Then r_i^2=d_i^+, q_i^2=d_i^-, r_i q_i=2alpha_i-s_i, and
beta_i=(r_i+q_i)/2. Since d_i^+, d_i^- and their product Delta_i are all
nonsquares, L_i=Q(r_i,q_i) has degree four and Galois group C2 x C2.
Its automorphisms send beta_i to beta_i, -beta_i, t/beta_i, -t/beta_i.
The involution beta_i->-beta_i fixes K_i; beta_i->t/beta_i induces
alpha_i->s_i-alpha_i. Distinct K_i do not imply disjoint L_i.

The given certificate checks directly by cancellation of the cross terms:

    A_i^2+B_i^2=(alpha_i^2+t^2)/s_i=alpha_i.

B_i!=0 by irrationality of alpha_i (or by v_i=0 separately).
Consequently Norm_{L_i/K_i}((A_i+beta_i)/B_i)=-1 and multiplying its argument
by beta_i gives relative norm alpha_i. This uses K_i coefficients and does
not factor the certificate into rational-pair rows. Reduction at s_i gives
Abar_i=(u_i+2v_i)/5 and Bbar_i=(v_i-2u_i)/5. Check gcd(Bbar_i,N): a proper
gcd is a factor, a full gcd makes Abar_i a verified root, and only a unit
permits division by Bbar_i. No map from the entire field is assumed.

Here is the precise scope of rational norm compression. For nonzero
gamma=U+V alpha_i,

    Norm(gamma)=U^2+s_i U V+t^2 V^2,
    (gamma+m)^2=(Tr(gamma)+2m) gamma  if Norm(gamma)=m^2.

One can choose the sign of the nonzero rational m so D=Tr(gamma)+2m!=0.
If one sign gives D=0, the field identity implies gamma=-m is rational;
the other sign gives D=-4m!=0. Actual trace zero with square nonzero norm
cannot occur in this real quadratic field: Norm(gamma)=-gamma^2 then.
Thus [gamma]=[D] in K_i^*/K_i^{*2}. For rational nonzero D, expansion in
the basis 1,sqrt(Delta_i) proves

    gamma square in K_i       iff D or D/Delta_i is a rational square;
    gamma/alpha_i square     iff D/d_i^+ or D/d_i^- is a rational square.

These are exact tests, not ideal-parity surrogates. Since Norm(alpha_i)=t^2,
both target classes have the same square rational norm here. Nevertheless
alpha_i remains nonsquare. This statement is specifically about these fields;
it does not apply to a generator of nonsquare rational norm.

There are additional cheap root branches: for i!=j, test Delta_i/d_j^+ and
Delta_i/d_j^- for rational squares. Their roots reduce to a root of R and
three times a root of R, respectively. Their reduced denominators are units
because d_j^+ and d_j^- are units modulo N. Check and verify these returns.
They handle some possible intersections of the two biquadratic fields; they
do not prove that the remaining compositum has degree sixteen.

## 3. The accepted one-field packet and an explicit rotation family

First, the frozen brief's original packet still checks:
P_j(alpha_i)=(s_i-s_j)alpha_i+c_j, c_j=u_j^2 v_j^2-t^2. Here c_j!=0:
v_j=0 gives -t^2, otherwise u_j v_j>=4Nell>t. Each packet has the same
image in the two fields, and these two packets also have equal images modulo
N because their coordinates were lifted from the same u_0,v_0. No field
square or smoothness statement follows from those equal modular images.

The newly accepted packet is stronger and different. For u^2+v^2=s_j,

    Q_j(T)=(t^2-u^2 T)(v^2-T),
    t^2-u^2 alpha_j=alpha_j(v^2-alpha_j),
    Q_j(alpha_j)=alpha_j(v^2-alpha_j)^2.                         (1)

These identities independently check by f_j(alpha_j)=0. The one-field target
is therefore already attained; no character can exclude it from all rational
rows. Reusing a conjugate gives the twisted class again, as accepted in the
[norm-gate disposition](W003-normgate-disposition.md). The present second
field is independently selected; that conjugate obstruction does not apply.

Keep both fields fixed. For coprime integers 0<=m<=M, 1<=k<=M, set

    D=k^2+m^2,
    A=u_j(k^2-m^2)-2v_j mk,  B=v_j(k^2-m^2)+2u_j mk.

Then A^2+B^2=s_j D^2. These are explicit rational rotations of the known
circle point, including (m,k)=(0,1). Clear denominators at construction:
use the COMMON INTEGER rows (tD,A),(B,D), so

    Q(T)=(t^2 D^2-A^2 T)(B^2-D^2 T),
    Q(alpha_j)=alpha_j (B^2-D^2 alpha_j)^2.                      (2)

Negative parameters give the same packet at the antipodal parameter -1/r;
the infinite parameter is the negative original point and gives its packet.
No modular inverse of D, A, B, m or k is needed for (2). Put

g=B^2-D^2 R mod N. The two row images are Rg and g, so Q(R)=Rg^2.
If gcd(g,N) is proper, return its verified factor. If g=0, a unit D returns
B/D as a verified root; a proper gcd of D or B with N returns a factor;
otherwise this candidate fails. If g is a unit, the explicit twisted root
has the unit image g, and testing the other field is the remaining work.
No frequency is assumed for any of these branches.

Even exhaustive subsets of just the two unrotated accepted packets add no
first useful target. If Q_1 Q_2 is twisted in K_1 and square in K_2, then
Q_2 must be square in K_1, so Q_2 alone is useful in the opposite orientation.
For the other orientation Q_1 alone is useful. A unit product has unit factors.
This observation is limited to those two packets; it excludes no larger row
family, and (2) supplies many different rational rows for further attempts.

## 4. Exact second-field square test, including recoverability

For a packet anchored at j and tested in i!=j, put e=s_i-s_j and
C=t^2 D^4-A^2 B^2. Reduction and absolute norms give

    gamma=Q(alpha_i)=C_0+C_1 alpha_i,
    C_0=t^2 D^2(B^2-A^2),
    C_1=A^2(s_i D^2-B^2)-t^2 D^4,
    Norm(gamma)=t^2 E,
    E=(C-e A^2 D^2)(C-e B^2 D^2).                              (3)

For example, the second factor is Norm(B^2-D^2 alpha_i); the first
multiplied by t^2 is Norm(t^2 D^2-A^2 alpha_i). The field rows and gamma
are nonzero by irreducibility. The factors in (3) have no supplied
smoothness or square law. On the unrotated anchor they specialize to
(t^2-u_j^2 v_j^2-e u_j^2)(t^2-u_j^2 v_j^2-e v_j^2).

Test E for an exact integer square. If it fails, gamma is not square.
If E=w^2, take m_0=tw with a sign making S=Tr(gamma)+2m_0 nonzero.
The exceptional-case proof in section 2 guarantees such a sign. Then gamma
is square iff S or S/Delta_i is a rational square. If S=h^2 the root is
z_i=(gamma+m_0)/h; if S=Delta_i h^2 it is
z_i=(gamma+m_0)/(h(2alpha_i-s_i)). Verify in K_i by exact coordinates.
This is a constant number of rational gcd/integer-square operations, not a
number-field square-root oracle. Both tests include signs and nonsquares.

Do not reduce that quotient term by term. Since gamma is integral, z_i is
integral. For delta_i=2alpha_i-s_i, coordinate expansion proves

    delta_i z_i=Tr(alpha_i z_i)-s_i Tr(z_i)+Tr(z_i) alpha_i
                 in Z[alpha_i].

Compute this exact cleared expression and verify its integer coefficients.
Now reduce it and divide only by delta_i(R)=-3R, a known unit. This also
handles h whose modular image is not a unit: exact cancellation occurs before
reduction. If g is a unit, the resulting zbar_i is a unit because
zbar_i^2=Rg^2. Return y=zbar_i/g and verify y^2=R modulo N. Thus every square
hit for this integral packet with unit g is recoverable. No map from all of
K_i or inversion of the shared-root resultant has been used.

## 5. Exact remaining point problem, beyond the elliptic norm quotient

Write the rational rotation as u=A/D, v=B/D. Its absolute-norm condition
has the elliptic quotient

    E_ji: W^2=f_i(X) f_i(s_j-X),         X=u^2, s_j-X=v^2.        (4)

The four roots on the right are distinct. The roots of f_i are simple;
intersection with their s_j-reflections would give either s_j=s_i or a
rational root s_j/2 of f_i, both impossible. Thus its smooth projective
model has genus one. It even has the known rational point
(X,W)=(s_j/2,f_i(s_j/2)), so calling this an unpointed torsor would be wrong.
This point need not lift to rational u,v, since that needs s_j/2 to be a
rational square. Even such a lift does not guarantee that gamma is square.

An exact full target system, with the other field root a+b alpha_i, is

    u^2+v^2=s_j,
    a^2-t^2 b^2=t^2(v^2-u^2),
    2ab+s_i b^2=u^2(s_i-v^2)-t^2.                              (5)

It is equivalent to the anchored packet (1) being square in K_i. After the
integer clearing in (2), it must additionally have the specified unit image.
The first coefficient equation alone is no bottleneck: a=tv,b=u satisfies
it. But its error in the second equation is (t+uv)^2, which is nonzero:
uv=-t and u^2+v^2=s_j would make Delta_j=(u^2-v^2)^2 a rational square.
Changing a to -tv gives the likewise nonzero (t-uv)^2. A convenient conic
point therefore does not complete the second-field root.

For specificity, these lifts have higher genus than (4). Adding the two
square conditions X=u^2 and s_j-X=v^2 to (4) gives a genus-seven curve:
it is an eightfold multiquadratic cover of the X-line branched at
0,s_j,infinity and the four roots in (4), each with ramification index two;
Riemann–Hurwitz gives 2g-2=-16+28=12. For the full system (5), work over
an algebraic closure and use the rational circle u^2+v^2=s_j as base.
The two conjugate radicands are
alpha_i^+*(alpha_i^--u^2)*(s_j-alpha_i^+-u^2) and its conjugate.
Each has eight simple zeros on that circle; their zeros are disjoint, and
all poles have even order. Their independent square roots give a degree-four
cover with sixteen branch points: 2g-2=-8+32=24, so the smooth model has
genus thirteen. These counts concern the fixed two-row rotation family only.

The remaining primitive is therefore a rational point of (5), with paid
numerator/denominator height and a useful unit image, under the actual field
law. A rational point, positive rank, or even a generated subgroup on (4)
does not provide the needed lifts. No rank, rational-point oracle, full descent,
uniform group sampling or point-height theorem is granted. Nor is emptiness
of (5) proved for any actual input: no numerical case was inspected.

## 6. A second explicit packet: forced norms, still a target-point gate

Independently, the reciprocal rows (p,q),(tq,p), for coprime positive p,q, obey

    Q(alpha_i)=alpha_i Lambda_i,
    Lambda_i=s_i p^2q^2-p^4-t^2q^4,
    Norm(Q(alpha_i))=t^2 Lambda_i^2.

Thus both norm conditions hold identically. The first orientation requires
Lambda_1 in {h^2,Delta_1 h^2} and Lambda_2 in
{d_2^+ k^2,d_2^- k^2}, for rational h,k. These tests are sufficient and
supply explicit field roots; integer clearing and unit epsilon coefficients
give valid reductions. The exact derivation, genus-five simultaneous quartics,
genus-one quotient, and unit-conic warning are in the focused
[reciprocal-packet supplement](W004-biquadratic-reciprocal-packets.md).
No useful rational point or height bound is supplied by forcing the norms.
This alternative does not reopen the settled one-field attainment question.

## 7. A finite executable attempt and complete cost accounting

The following is an on-paper finite program, not executed code. Fix a public
integer cap M(n), for example M(n)=n^2, and use the deterministic Norm2 and
lexicographic selector specified above. Perform their validation and early
factor/root branches; test d_i^+/- and the cross ratios; check Bbar_i and the
four original rows (u_j,1),(v_j,1) in index order. A zero original row gives
a root directly, a proper row gcd a factor, and a unit continues. Next, for
anchors j=1,2, scan the coprime (m,k) rectangle of section 3 lexicographically,
apply its g/D/B checks, and use section 4's exact square test and cleared
recovery. Finally scan coprime 1<=p,q<=M for the reciprocal supplement's
two orientations and four epsilon choices, including its ordered row checks.
Return the first verified factor or root; after the cap return FAILURE.
Every discard, failed square test and full-gcd failure is charged. No elliptic,
factoring or root oracle is part of this program. Fixed root signs suffice.

All row coefficients, (3), Lambda_i, rational-square tests and explicit root
coefficients have O(n+log M) bits. The three streaming scans have O(M^2)
candidates and constant many exact tests per candidate. Schoolbook arithmetic,
Euclidean gcd, binary integer square roots, sequential counters and verification
give the conservative bit bounds

    T_inner <= C_norm(N,R)+poly(n)+M^2 poly(n+log M),
    S_inner <= S_norm(N,R)+poly(n+log M).

If M is a polynomial in n the post-Norm2 work is polynomial. If M=2^b the
scan is O(2^(2b) poly(n+b)); an O(poly(n))-bit point by itself does not make
this exhaustive search polynomial. No cap here guarantees a useful witness.
Repeating the same deterministic inner attempt for the same R changes nothing.

For clarity, the failure-inclusive outer law can still be stated exactly.
Let r be the number of distinct prime divisors of the continuing N, let G(R)
be the probability the inner routine returns a proper factor, and J(R) the
probability it returns a root, with disjoint outcomes and all other outcomes
counted as failure. For this reference these probabilities are indicators.
An n-bit raw outer word, including rejects and the zero word, has split law

    sigma_N=[N-1-phi(N)
             +sum_{R in QR_N^*}(2^r G(R)+(2^r-2)J(R))]/2^n.     (8)

Each unit-square fiber has 2^r elements even with repeated odd prime-power
factors. Conditional on R the inner result is independent of the outer x;
exactly two preimages are globally +/- the returned root. This proves (8),
not a positive lower bound for the packet contribution J(R).

For iid cold outer trials E[T_split]=E[T_trial]/sigma_N. The existing early
gcd branch alone gives sigma_N>=1/(4 sqrt(N)): multiples of a smallest prime
p<=sqrt(N), excluding zero, contribute N/p-1 raw words. With M=n^2 and the
finite Norm2 reference, this yields only O(N_0^(3/2) poly(log N_0)) expected
COMPLETE factorization, paying preprocessing at each node and a polynomial-size
factor tree; working space is O(N_0 log N_0+poly(log N_0)). This bound comes entirely
from the old gcd fallback. Ordinary trial division already costs
O(sqrt(N_0) poly(log N_0)) deterministically. The literal Norm2 lists alone
materialize N records before the new field phase. A future cheaper C_norm
does not resolve (3), (5), useful mass or cold-restart cost.

## 8. Prior art, disposition and next boundary

Quartic covering equations and the distinction between local solubility and
finding rational points are established descent machinery. Cremona's
chapter III, sections 3.5–3.6 (read scopes in the source ledger), explicitly
uses bounded point searches; its rational-2-torsion procedure factors a bad-prime
integer and returns rank bounds when searches do not settle solubility. Its
statement is not a polynomial-time witness theorem for (5) or the reciprocal
supplement's curves.
[Author text](https://johncremona.github.io/book/fulltext/chapter3.pdf).
The CFOSS introduction's Selmer exact sequence likewise distinguishes
representing covering curves from finding their rational points.
[Primary paper](https://arxiv.org/html/math/0606580v1).

Coppersmith's sections 2–3 already use field norms, character columns, actual
algebraic square roots and several fields with a common modular evaluation.
Printed p.170 explicitly qualifies its smoothness estimates as heuristic.
Those methods do not supply a probability law for these two packet streams or
their prescribed mixed class. No novelty or transferred NFS bound is asserted.
[Primary paper](https://link.springer.com/content/pdf/10.1007/BF00198464.pdf).
Shallit and BGH were read only to check the inherited conic-source boundary;
no AEM retrieval or theorem verification was attempted. Exact source copies,
read scopes and retrieval limitations are in
[sources](W004-biquadratic-evidence/sources.json) and
[source notes](W004-biquadratic-evidence/source-notes.md).

**Disposition: symbolically derived packet laws; target supply unresolved.**
The first remaining constructive obligation is a useful point of (5), or of
one of the reciprocal supplement's eight curves, with paid height/search cost
for enough of the actual N,R law. Solving the elliptic norm quotient (4)
does not discharge the lifting and square-class obligations. No universal
separating character for arbitrary allowed rows, universal failure of either
packet family or factoring lower bound has been proved. A separately bounded
[future test proposal](W004-biquadratic-test-proposal.md)
targets only the explicit M=n^2 coverage claim; it is not authorized execution
or evidence of success. Parent acceptance and a new independent review remain
mandatory before promoting any deduction here.
