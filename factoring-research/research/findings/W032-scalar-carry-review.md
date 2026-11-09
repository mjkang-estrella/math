# W032 scalar/carry review

**Disposition: accept the scalar construction, precision, formal diagonal,
first two digit identities, stated second-digit zero bound, and proposed
common-denominator formula. Later canonical digits require actual floor
terms; a degree-2R root bound for the unconditioned digit is not established.
The exact third-digit formula below supplies the missing carry explicitly.
Verified complete factoring improvement: NONE.**

For fixed R the same observation is an elementary public floor-polynomial
screen, computable without the quadratic-algebra exponentiation. This is an
exact alternative acquisition method, not a theorem excluding a useful
success law for that screen. For growing R, the scalar method can avoid the
quadratic coefficient-table construction described below; its precision and
success obligations remain separate.

## Scope and frozen evidence

The full brief and ten relevant inputs were frozen before the mathematical
review in [input-manifest.json](W032-scalar-carry-review-evidence/input-manifest.json).
These include the five governing documents, W032, STATE, and the three named
W031 reports. The reviewed target is the frozen W032, not a later live edit.
[brief.txt](W032-scalar-carry-review-evidence/brief.txt) preserves the complete
assignment; [read-scope.json](W032-scalar-carry-review-evidence/read-scope.json)
records actual reads and exclusions.

The accepted W031 identity and coefficient formula are imported interfaces.
The separate normalized-prime-screen review is used only for scope and its
accepted qualifications: sufficiently precise lower rational terms cost
work, its fixed-coefficient recurrence is a separate screen, and the staged
37 example needs the 7-unit condition. Its experiments, prime-coverage
argument, and literature review are not repeated here.

There were **no numerical factoring experiments**, no N=143/N=323 evaluations,
no access to the live assay's implementation or results, and no delegation.
The only computation beyond file integrity is an exact formal-polynomial
check over Q[N,a,r,s,l], with no numerical substitution for these variables.
Its [source](W032-scalar-carry-review-evidence/symbolic-check.py) and
[output](W032-scalar-carry-review-evidence/symbolic-check.json) are delivered.
The floor arguments, general-R proofs, and cost analysis are prose proofs,
not Lean-checked results. No new prior-art or novelty assertion is made;
no web search or external source is needed for the direct proofs below.
Only this report and its assigned evidence directory were written. No shared
code, Lean, STATE, task registry, install, commit, or project-check run occurred.

## 1. Exact scalar and legal normalization

Let N=2n+1>=3 be odd; let 0<=a<N and gcd(a,N)=1. Put U=(-4)^n,
z=Na, Delta=z^2-4. In the free rank-two algebra Z[w]/(w^2-Delta), write

    (z+w)^N = A+B w.

Conjugation w -> -w gives 2A=(z+w)^N+(z-w)^N. Both roots have sum 2z
and product 4, so this power sum obeys the same initial conditions and
recurrence as the W031 companion trace. The imported polynomial identity
therefore gives

    A = z J_N(z^2),
    J_N(t) = sum_(j=0..n) alpha_j t^j,   alpha_0=N U.

This uses the coefficient pair directly, so there is no integer-halving
error on a modular trace. All alpha_j are integers. Consequently

    A = N^2 a U + sum_(j=1..n) alpha_j N^(2j+1) a^(2j+1),

which proves N^2 divides A for every odd N, without a denominator-unit
assumption and without asserting that N divides every alpha_j.

Set Q=N^(2R+3) and M=N^(2R+1). Projection into the algebra modulo Q is
a ring homomorphism. Binary pair powering obtains the exact residue of A;
its canonical representative A_bar in [0,Q) is also divisible by N^2.
Changing an integer lift of A_bar by tQ changes A_bar/N^2 by tM. Thus

    V_R(a) = [(A_bar/N^2) * (a U)^(-1)]_M

is well-defined, where brackets mean the canonical residue in [0,M).
Both a and U are units; N is never inverted. This proves that Q is
sufficient to recover the complete stated output precision. It is a
precision statement about this acquisition method, not a minimum-cost or
minimum-information theorem for alternative evaluation methods.

Reducing V_R modulo N^(2r+1) yields V_r for every r<=R. If two integer
lifts differ by t N^(2r+1), their quotients after floor division by N^(2r)
differ by tN. Therefore the digit modulo N is invariant under this lift
change. This also proves consistency of all requested d_r between precision
levels. The odd base-N digits are present in V_R and must be retained in
this reasoning.

Initial gcd(a,N) is a separate operation. A proper gcd is an ordinary
initial split, not a digit success. The only full-gcd case in [0,N) is a=0;
normalization is skipped there. All density statements below concern the
unit branch unless an extended public formula is expressly being counted.

## 2. Diagonal expansion and the tail that does not divide by N

For all j in the imported identity, as a rational equality,

    alpha_j/(N U) = A_j(N^2),
    A_j(Y) = E_j(Y)/D_j,
    E_j(Y) = product_(i=1..j) ((2i-1)^2-Y),
    D_j = 4^j (2j+1)!,
    A_j(Y) = sum_(h=0..j) c_(j,h) Y^h.

Assume leastprime(N)>2R+1. For j<=R, gcd(D_j,N)=1. Clearing this
denominator in alpha_j=N U E_j(N^2)/D_j proves N divides alpha_j;
only in this range may that integer divisibility be inferred this way.
The identity then has its legal interpretation at every needed N-power
precision.

For the remaining terms use the integral alpha_j instead. After cancelling
the exact a factor and normalizing by U, the contribution is

    N^(2j-1) alpha_j a^(2j) U^(-1).

For j>R its explicit N-power has exponent at least 2R+1, so it vanishes
modulo M. This needs only integrality of alpha_j and the unit U; it does
**not** use alpha_j/N or a modular interpretation of the nonunit factorial
D_j. The possible distant loss of N-divisibility is therefore harmless at
this precision.

For j<=R, expansion of N^(2j) A_j(N^2) a^(2j), followed by collection at
k=j+h, gives

    V_R(a) = sum_(k=0..R) N^(2k) G_k(a^2)  (mod M),
    G_k(x) = sum_(j=ceil(k/2)..k) c_(j,k-j) x^j.             (2.1)

Terms with k>R have exponent at least 2R+2 and vanish. Every rational
coefficient in (2.1) is interpreted with its unit denominator at the
required precision. In particular G_0=1 and V_R=1 modulo N^2 under this
unit hypothesis. That latter congruence is not being asserted for arbitrary
odd N with small denominator factors.

G_k has degree exactly k. Its leading coefficient

    c_(k,0) = product_(i=1..k)(2i-1)^2 / [4^k(2k+1)!]

is a unit at every prime divisor of N under the hypothesis. Thus the
formal polynomial G_k(a^2) has degree 2k and nonzero leading coefficient
in every such prime field. This does not identify it with the canonical
digit d_k. Subtracting lower terms to extract G_R would require G_k modulo
N^(2(R-k)+1) for each k<R; knowing only G_k modulo N does not supply their
carries.

The first four formal terms are

    G_0(a^2) = 1,
    G_1(a^2) = a^2/24,
    G_2(a^2) = 3a^4/640 - a^2/24,
    G_3(a^2) = 5a^6/7168 - a^4/192.                         (2.2)

## 3. First and second canonical digits

Assume gcd(N,30)=1. All statements here hold for every canonical unit a.
From V_1=1+N^2 G_1 modulo N^3,

    d_1(a) = a^2/24  (mod N).

Indeed the canonical representative is exactly 1+N^2 [G_1]_N; its constant
1 cannot cross the digit boundary. This digit is a unit and cannot split N.
Higher precision does not change it. Only gcd(N,6)=1 is needed for this
first-digit conclusion.

For the second digit set

    r = [-a^2]_24,                 0<=r<24,
    L = (a^2+r N^2)/24,
    H = 3a^4/640 - (a^2+r)/24.

Since gcd(N,6)=1, N^2=1 modulo 24. Hence L is an integer. The canonical
range a^2<N^2 and 0<=r<=23 gives 0<=L<N^2. Direct rational algebra gives

    G_1(a^2)+N^2 G_2(a^2) = L+N^2 H.

Thus V_2 has the canonical form

    V_2 = 1+N^2 L+N^4 [H]_N.

The lower part satisfies 0<=1+N^2 L<N^4, so there is no further carry at
this boundary. Consequently

    d_2(a) = 3a^4/640 - (a^2+r)/24  (mod N).                (3.1)

The second quotient is an ordinary integer. This proves the proposed
formula, including the boundary issue for the constant 1. Equivalently,
clearing the unit denominator 1920 gives

    1920 d_2(a) = P(a,r) := 9a^4-80a^2-80r  (mod N).        (3.2)

The hypothesis a<N matters: it supplied the small canonical block L.
Replacing a by an arbitrary congruent integer without recanonicalizing
need not preserve these carry formulas.

## 4. Second-digit zero count and what a split means

Let p>5 be prime, N=pq, and gcd(N,30)=1. The counting argument itself
allows an arbitrary positive integer cofactor q. Extend the right side
of (3.1) to all integers 0<=a<N purely for an upper count; scalar
normalization is still only performed on units.

Fix a class b modulo 24. Then r=[-b^2]_24 is constant and (3.2) is a
quartic over F_p with nonzero leading coefficient 9. It has at most four
roots modulo p. A pair consisting of b modulo 24 and one such root
modulo p is one residue class modulo 24p. Its intersection with [0,N)
has size at most ceil(N/(24p))=ceil(q/24). Hence

    # {a in [0,N): p divides the extended d_2(a)}
        <= min(N, 4*24*ceil(q/24))
        <= min(N, 4q+96).                                   (4.1)

For a uniform a in [0,N), the p-zero probability of this extended screen
is at most min(1,4/p+96/N). This is only an upper bound, and it concerns
zeros, not proper gcds or a lower success probability.

For distinct primes p,q>5, write

    B_p = 96 ceil(q/24),   B_q = 96 ceil(p/24),
    phi(N)=(p-1)(q-1).

After conditioning on units, a valid bound is

    Pr[p | d_2(a) | a unit] <= min(1, B_p/phi(N)),
    Pr[proper digit split | a unit]
        <= min(1, (B_p+B_q)/phi(N)).                         (4.2)

Using N rather than phi(N) after unit conditioning would be unjustified.
For squarefree semiprimes a proper split is the event that exactly one
component vanishes. If E_p and E_q denote the two zero events, its exact
probability is Pr(E_p)+Pr(E_q)-2Pr(E_p intersect E_q). Both-component zeros
give gcd N. No independence is needed for (4.2), and none is asserted.
Even though uniform CRT coordinates are independent, carry events can
depend on the whole canonical representative, not just their own coordinate.

In particular the second digit has no positive constant-density guarantee
as the least semiprime factor tends to infinity. The bound does not exclude
special inputs or a changed, paid nonuniform selector. For N=p^2, a zero
modulo p can lead to gcd p or p^2; component-zero counting alone does not
distinguish them. Initial gcd(a,N) outcomes are excluded throughout (4.2).

## 5. Proposed common-denominator formula: accepted

Let

    D = 4^R(2R+1)!,
    C_k(x) = D G_k(x),
    F = sum_(k=0..R) N^(2k) C_k(a^2),
    M = N^(2R+1).

D_j divides D for every j<=R. Since E_j has integer coefficients,
every C_k is an integer polynomial. Also gcd(D,N)=1 on the stated
branch. Thus (2.1) says V_R=F D^(-1) modulo M.

There is a unique h in [0,D) such that

    h M = -F  (mod D),

because M is a unit modulo D. Put T=(F+hM)/D, an integer. Modulo M,
D T=F, so T is an integer lift of V_R. If V_R=T-tM for the unique integer
t giving the canonical range, then

    floor(V_R/N^(2R)) = floor(T/N^(2R)) - tN.

This identity also holds for negative T. Reduction modulo N proves exactly

    d_R(a) = floor(F/(D N^(2R)) + hN/D)  (mod N).             (5.1)

No assumption that T is canonical, positive, or smaller than M is needed.
An implementation may use the single integer floor quotient

    ((F+hM) // (D N^(2R))) mod N,

with mathematical floor division. There is no floating-point approximation
and no discarded fractional term.

For R=3 an explicit cleared polynomial is

    D=322560,
    F=322560 + 13440 N^2 a^2
       + N^4(1512a^4-13440a^2)
       + N^6(225a^6-1680a^4).                               (5.2)

The formal-polynomial check verifies (2.2), (3.1)'s underlying rational
identity, the lower-block identity used next, and (5.2). The general
integrality and floor arguments are the proofs above, not extrapolations
from a finite coefficient check.

## 6. Exact third digit

Assume leastprime(N)>7 and a is a canonical unit. This supplies the
additional 7-unit condition for G_3. Retain r, L, H from section 3 and put

    P = 9a^4-80a^2-80r,                 H=P/1920,
    s = [-P * (N^2)^(-1)]_1920,         0<=s<1920,
    ell = floor((P+sN^2)/(1920 N^2)).

The inverse defining s exists since gcd(N,30)=1. These are public integer
operations, requiring no knowledge of a factor. The exact formula is

    d_3(a) = 5a^6/7168 - a^4/192 - s/1920 + ell  (mod N).   (6.1)

To prove it, the rational lower-block identity gives

    V_3 = 1+N^2 L+N^4 H+N^6 G_3(a^2)  (mod N^7).

Since 1+N^2 L<N^4, if u=[H]_(N^3), then the digit at N^6 is

    d_3 = G_3(a^2)+floor(u/N^2)  (mod N).

This follows by choosing the integer lift with H replaced by u and G_3
replaced by its residue modulo N; the discarded lower block cannot carry
across the boundary. Let k in [0,1920) satisfy

    kN^3 = -P  (mod 1920).

Then (P+kN^3)/1920 is an integer lift of H modulo N^3; canonicalizing it
changes its N^2-quotient by a multiple of N. Write kN=1920v+s. The s here
is exactly the residue defined above, since sN^2=-P modulo 1920. Therefore

    floor(u/N^2)
      = v + floor((P+sN^2)/(1920 N^2))  (mod N)
      = -s/1920 + ell  (mod N),

which proves (6.1). This accounts for both lower formal terms, not merely
the previously observed value of d_2 modulo N.

For fixed N, r and s are determined by a modulo 1920. The remaining ell
contains the actual floor of a quartic expression divided by N^2; it is
not generally fixed by that small residue label. Its possible magnitude is
O(N^2) on the canonical interval. For example the elementary bounds

    P >= -2018,   P < 9N^4,
    -1 <= ell <= ceil(3N^2/640)     (N>=11)

follow from 9x^2-80x>=-1600/9, x=a^2, and 0<=r<=23, 0<=s<1920.
This is a bound on the label range, not a claim that all labels occur.
It provides no constant-size partition on which a global degree-six
root estimate can simply be summed.

There is a symbolic unit-family witness that the integer floor need not be
constant on a residue class. For positive integer t put

    m = 210*1920*1919*t+1,   N=m^2,
    a_0=2,                 a_1=N-1919.

Both a values are canonical units, gcd(N,210)=1, and a_0=a_1=2 modulo
1920 because N=1 modulo 1920. For both points r=20 and s=1776. At a_0,
P=-1776 and ell=0; at a_1, P=9(N-1919)^4-80(N-1919)^2-1600, so ell
grows asymptotically as 3N^2/640. This is a symbolic family, not a
numerical assay. It demonstrates nonconstant integer carry on one small
residue class; it does not by itself prove a particular lower bound on
roots modulo p or disprove every possible modular polynomial description.

After fixing both s and ell, clearing (6.1) gives the polynomial

    322560 d_3(a)
       = 225a^6-1680a^4-168s+322560 ell  (mod N).             (6.2)

For p|N, p>7, its leading coefficient is a unit and it has at most six
roots modulo p. This is a valid bound for that fixed label pair only.
It is not a six-root bound for the union of the actual carry classes.
Nor does the presence of a floor by itself prove that no other useful
root-density estimate or algorithm exists.

## 7. Exactly which higher-digit root bounds follow

For the formal G_r(a^2), the field-root bound is valid: at most 2r roots
modulo p. On units one can even divide its forced factor a^(2 ceil(r/2))
and obtain at most 2 floor(r/2) roots, since the remaining leading
coefficient is a unit. These are bounds for G_r, which one obtains by
fully paid rational subtraction, not automatically for d_r.

A general conditional statement for d_R follows from (5.1). Fix a residue
class b modulo D. Then h is constant, and so is

    e = [C_R(a^2)]_D.

Writing C_R(a^2)=D J+e with J integral gives

    d_R(a) = (C_R(a^2)-e)/D + t(a)  (mod N),
    t(a) = floor(e/D + hN/D
                   + sum_(k<R) N^(2k-2R) G_k(a^2)).         (7.1)

On a fixed class b and a fixed integer value of t, the cleared expression
C_R(a^2)-e+Dt has degree 2R and unit leading coefficient modulo p. It has
at most 2R roots. If N=pq, each combined class modulo D and p contains at
most ceil(q/D) points in [0,N). This yields a conditional count of at most
2R ceil(q/D) for that b,t. Summing needs an actual bound on how many
relevant floor values occur and on their intersections with these classes.
D itself grows with R; calling this a small fixed partition when R grows
would be another unjustified assumption.

Already at R=3 the lower term G_2(a^2)/N^2 can have size of order N^2.
Therefore the first-two-digit proof does not extend by dropping integer
quotients of lower terms. Neither a blanket 2R/p estimate for canonical
d_R nor a random-residue estimate of 1/p has been proved here. There is
also no lower bound on the probability of a proper split, and no
independence assertion across digits, across prime components, or across
adaptively selected a. A union bound over valid individual upper bounds
is possible; it cannot manufacture a lower success guarantee.

## 8. Paid scalar and public-screen costs

Let b=bitlen(N) and B=bitlen(N^(2R+3))=Theta((R+1)b). Denote integer
multiplication, division, and extended-gcd costs on B-bit operands by
M_int(B), Div(B), and Gcd(B), respectively. A pair multiplication is

    (u,v)(x,y) = (ux+Delta*vy, uy+vx) modulo Q.

With Delta reduced modulo Q this uses a constant number of B-bit modular
multiplications and additions. Binary powering uses O(b) such operations.
Computing U modulo M, the inverse of aU, exact division of A_bar by N^2,
and the final quotient are also paid. A transparent single-digit upper
bound is

    O((b+log(R+1))*[M_int(B)+Div(B)] + Gcd(B) + Gcd(b)),

including construction of Q/M by binary powering and validation of a
returned factor. Under quasi-linear multiplication/division and fast gcd,
this is soft O((R+1)b^2) on the stated branch, where log(R+1)=O(b).
This is an arithmetic-model upper bound, not an implementation timing.
The claim is polynomial in input bit length only if R is polynomial in b.

All digits up to R can be extracted by divide-and-conquer radix conversion
with radix N (or N^2 blocks), retaining both positions in each block.
At each recursion level total operand lengths are O(B); with the usual
superadditive multiplication bound this costs O(M_int(B) log(R+1)) up to
fast-division factors. Testing the R digits adds R gcds on b-bit values.
A simple repeated-division implementation must instead pay its own larger
cost. The scalar acquisition keeps a constant number of B-bit residues;
fast-arithmetic workspace is additional, and retaining all digit results
requires O(Rb) output bits. There is no R-length polynomial jet in this
powering method, but the precision itself has linear R bit volume.

For the same N and many a, Q, U, and associated unit data can be reused.
Each new a still pays its selection, initial gcd, point-dependent power
or alternative evaluation, digit processing, and final witness checks.
No per-attempt success probability follows from the acquisition cost.

The floor formula supplies a concrete alternative. The recurrence

    E_0(Y)=1,
    E_j(Y)=((2j-1)^2-Y) E_(j-1)(Y)

constructs the integer coefficient rows. Multiplying each needed row by
D/D_j and collecting the j+h=k diagonal constructs C_k. These operations
need O(R^2) integer coefficient work in a straightforward construction;
coefficient bit lengths are O(R log(R+1)). The bound follows directly from

    sum_h |[Y^h]E_j| = product_(i=1..j)(1+(2i-1)^2)
                      <= (1+4j^2)^j,

and log D=O(R log(R+1)). This is a fully paid upper bound, not a claim of
optimal coefficient construction.

For fixed N,R, combine the terms into the degree-R polynomial in x

    P_(N,R)(x) = sum_(k=0..R) N^(2k) C_k(x).

Its coefficients have O(R[b+log(R+1)]) bits. Evaluating at x=a^2 by Horner,
including intermediate values, stays within that bit bound: powers in F
have total N/a exponent at most 4R. Compute M modulo D and its inverse
once, then h=[-F M^(-1)]_D and the integer quotient in (5.1). This takes
O(R) big-integer Horner steps per a, plus division/reduction, after the
stated O(R^2) coefficient setup and O(log(R+1)) powering/inverse work.
For all lower digits as well, canonicalize T=(F+hM)/D modulo M once and
perform the same radix conversion; it is unnecessary to reevaluate each R.
If all C_k tables are retained, there are O(R^2) coefficients of
O(R log(R+1)) bits. They can instead be streamed row by row directly into
P_(N,R), retaining O(R) values of O(R[b+log(R+1)]) bits, in addition to
arithmetic workspace. These storage costs are separate from the scalar
method's constant number of wide residues.
No factor, root oracle, hidden order, or coefficient of index proportional
to N is requested. For R=3, (6.1) is an even smaller explicit screen with
fixed small denominators and one actual floor computation.

Thus for **fixed R**, scalar exponentiation creates no unique access to
these digits: fixed-degree public polynomial evaluation, small-denominator
modular arithmetic, and floors compute them directly, generally removing
the O(b) powering stages. For **growing R**, this direct implementation's
O(R^2) setup and O(R) wide multiplications per point need comparison with
the scalar method; no same-cost or lower-bound theorem for all R is claimed.
Nor does public computability make a function useless for factoring. The
unproved issue is useful separating yield per paid computation.

The scalar algorithm itself does not need the least-prime bound to execute.
It is an assumption for the displayed rational expansion and its density
analysis. If an implementation wants to certify that branch, it must pay
for denominator checks. Sequential gcd(t,N) for
2<=t<=min(2R+1,floor(sqrt(N))) is one elementary method, using O(R) gcds.
For composite N each tested t<N; a nonunit therefore yields a proper
factor. Reaching floor(sqrt(N)) without a factor contradicts the composite
promise. A single gcd(D,N)=N is not a split and needs localization among
the known small factors. This preprocessing is separate from the scalar
unit-a check and must not be hidden in a claimed factoring runtime.

## 9. Saved work, disposition, and decisive obligation

The supported saving is acquisition: one point-dependent scalar at high
precision replaces a dense polynomial jet or a table of individually
normalized coefficients. It avoids explicitly generating lower G_k when
using the scalar route. It does not eliminate their mathematical carries.
At fixed R, the public floor-polynomial formula supplies the same observation
more directly, so the quadratic-algebra presentation alone supplies no new
asymptotic factoring advantage.

Remaining paid work includes parameter and sample selection; R-dependent
precision; inverses and unit/denominator exits; all output digits and gcds;
rejected and full-gcd outcomes; repeated points; any direct-screen setup
and exact integer widths; and localization if products or batches vanish
at both components. A selector depending on hidden factors is not allowed.
An initial nonunit a is an ordinary gcd success. An upper zero count is
not a lower success probability, and successful splitting is not yet a
complete recursive factoring bound.

Accept the symbolic construction at its stated scope. Keep the higher-digit
success question **open**, without promoting the absence of a polynomial
root bound to evidence of favorable density. No experiment in the live
assay can settle a uniform asymptotic success law by itself.

The decisive mathematical obligation is an executable N-only schedule or
sampler for (R,a), with complete bit cost, and either a deterministic cover
that forces a proper gcd or a proved separating probability on every stated
input family. For a polynomial-time randomized claim, R and total trial
work must be polynomial in b and the proper-split probability must support
the claimed amplification or expectation. For any weaker improvement, the
charged work divided by justified success must beat a specified comparable
baseline. Composite prime powers, small-denominator exits, and the rest of
the claimed input domain must be covered separately where necessary.

A useful changed next computation is explicit evaluation of (6.1), or (5.1)
for a chosen growing R, coupled to a proved analysis of its actual floor
classes and a paid selector. This removes the temptation to assign random
residues to the scalar power or ignore the carry. It is a mathematical
research direction, not authorization for another overlapping finite assay.
No all-algorithm lower bound, universal impossibility theorem, novelty claim,
or verified complete factoring improvement follows from this review.

## Delivery integrity

The [validation record](W032-scalar-carry-review-evidence/validation.json)
confirms all ten frozen input hashes, the brief hash, and 11 passing exact
formal-polynomial checks. The live STATE changed during concurrent parent
work; the other nine live inputs still matched at final intake. This review
uses the frozen STATE context and the explicit brief, without altering or
incorporating the concurrent STATE update.

The [full delivery manifest](W032-scalar-carry-review-evidence/delivery-manifest.json)
records every payload's path, byte length, and SHA-256, including this report,
the complete frozen inputs, and symbolic-check source/output. It excludes
itself and the terminal anchor file to avoid circular hashing. Those two
inventory files plus the listed payloads constitute the full delivery.
[terminal-manifest.sha256](W032-scalar-carry-review-evidence/terminal-manifest.sha256)
contains the hash of the exact manifest bytes, also returned in the terminal
handoff. The manifest is generated after this report is final; no report
content is appended afterward. Hash checks authenticate byte identity
relative to that anchor, not mathematical correctness.
