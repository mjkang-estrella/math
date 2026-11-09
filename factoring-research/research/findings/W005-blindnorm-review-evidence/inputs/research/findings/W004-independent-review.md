# W004 — independent review of the completed construction

2026-10-08. **Recommend scoped acceptance with the conic qualification and
execution-order completion below. Do not select the proposed coverage screen.**
The selector, packet identities, exact field-square tests, cleared extraction,
and smooth-model genera survive. Useful mixed-target supply remains unproved.
The proposed small-corpus coverage property already follows from elementary
row gcds, independently of either mixed-target construction (section 9).
**Verified new COMPLETE classical factoring improvement: NONE.** This is a
review recommendation, not acceptance. Every new deduction in this review,
including the coverage lemma and strengthened branch analysis, remains
**UNACCEPTED pending coordinator disposition**.

## 1. Scope, evidence and findings requiring disposition

I read the required project instructions and current STATE; the full original
assignment and W003/W004 briefs; all 385 final main-report, 127 supplement and
69 proposal lines; both intake/preparation notes, including all eight obligations
and the rotation addendum; the exact update/receipt; all three accepted W003
dispositions; the 322-line norm-gate review and original note; H027's prior-art
note, H031's disposition, and W004's source notes and cited passages. The latest
lifecycle override governs stale live/provisional wording. There was no earlier
independent W004 review or author response. W003's accepted one-field packet
is governing context; this review does not reopen those accepted dispositions.

Independent hash/byte checks pass for **13 initial snapshots, 3 appended
snapshots, 11 source-artifact identities and 36 delivery entries**. Only STATE
differs among the original 13+3 inputs. The three submitted copies are identical
to their assessed originals, whose SHA-256 values are:

    main       9957b2368caa91ba3261bcef7d7b2f33b392c931d2744c2536906d55ad7132e9
    supplement a520c469b3e4c635500916bd952fd9fa6eaf1126a0bb827c8c0038fd25e56764
    proposal   5456e113dc6f2318b3d97e105032a63e80d1630f5e7011781eca690d0a693eba

[Verification](W004-independent-review-evidence/submission-verification.json),
[direct-input identities](W004-independent-review-evidence/input-identities.json),
[exact review assignment](W004-independent-review-evidence/exact-review-assignment.txt),
and [delivery manifest](W004-independent-review-delivery.sha256) are separate.
The original constructive assignment and exact update/receipt are also preserved
under this review prefix. No recursive historical evidence tree was copied.
Parent lifecycle updates changed STATE, the intake's closing paragraph and the
task registry during review; both consumed versions of each are separately frozen.
The later STATE mentions a separate Shallit follow-up but accepts no fast Norm2;
that follow-up is not a new dependency here. No assessed report, disposition or frozen manifest was
edited. Only source reading/extraction/rendering, archival/hash/link operations
and report writing occurred: no mathematical execution, numerical case, corpus,
experiment, solver, Lean, dependency, delegation, commit or publication.

Material dispositions requested: (i) supplement lines 110–115 must require
reduction of d*l^2 to zero, not just unit h,k; (ii) freeze the few unspecified
tie/orders before an implementation; (iii) the optional coverage screen is
mathematically uninformative for packet supply, as proved below. These do not
invalidate the actual integer reciprocal packet or the conservative cost bound.

## 2. Paid selector and the field law

On the promised branch N is odd, gcd(N,30)=1, R is a unit square and
n=bit_length(N). Norm2 existence is valid for every unit 5R, without the
square promise: the two square sets over each odd prime intersect; at least one
coordinate is nonzero, its derivative lifts the solution to every prime power,
and CRT combines them. This uses factors only in the proof. The specified two
lists, sorted by (residue,coordinate), have a match. Their construction costs
O(N*n^2), each of O(n) sequential merge passes costs O(N*n), and the final merge
and verification fit the same bound. Space is O(N*n) bits on fixed multitapes.
This remains an exponential paid primitive, with no favorable output law.
A replacement must specify and charge its output domain, randomness, failures,
restarts, time and space; C_norm is conditional on that complete contract.

If w distinct primes divide NR, then 2^w<=NR<2^(2n), so w<2n. Excluding
2,3,5 still leaves an eligible prime among the first 2n+4 primes. The inspected
Rosser–Schoenfeld corollary (3.13) gives p_k<k(log k+log log k), k>=6.
Thus ell=O(n log n). Sequentially test integers for primality by trial division;
for each prime check gcd(ell,N) before skipping divisors of NR. A proper gcd
returns a verified factor. All small primality work costs
O((n log n)^(3/2)*poly(log n)); the gcd/divisibility work is polynomial in n.
The program can stop at the first eligible prime without evaluating real logs.

For c=4R nonzero modulo ell, the bijection
(z,y)<->(z-y,z+y) identifies z^2-y^2=c^2 with ell-1 ordered nonzero factor
pairs of c^2. Hence sum chi(z^2-c^2)=-1. Exactly two arguments give zero,
and the positive/negative counts are (ell-3)/2 and (ell-1)/2. These count
arguments z, not distinct values or pairs (a,b). Every z is a sum of two squares
by the two sets of size (ell+1)/2. Both lexicographic pair searches therefore
terminate; their O(ell^2*poly(log ell)) character work is paid.

CRT uses gcd(N,ell)=1, with representatives in [0,N*ell). The prescribed shift
gives 4N*ell<=u_i<5N*ell and 0<=v_i<N*ell, hence the claimed bounds on s_i.
Since 0<16R^2<2s_i-1, Delta_i lies strictly between consecutive squares.
It is positive nonsquare; f_i is irreducible, with two positive roots. The
opposite nonzero characters of Delta_1,Delta_2 make their product nonsquare,
so the quadratic fields are distinct and s_1!=s_2. All heights have O(n) bits.
Moreover f_i(T)=(T-R)(T-4R) modulo N: s_i, Delta_i and f_i'(R)=-3R are units.
Neither discriminant factorization nor a field-order oracle is needed.

If alpha_i=w^2, w is integral and Norm(w)=±t; its integer trace squares to
s_i±2t. Conversely (alpha_i±t)^2=(s_i±2t)*alpha_i. Thus the exact tests of
d_i^-=s_i-4R and d_i^+=s_i+4R are exhaustive and give roots k and k/3
modulo N. Their positivity excludes a zero denominator. Every root is verified;
no frequency claim is justified. The entire selector after Norm2 is poly(n).

## 3. Biquadratic structure, norm compression and intersections

After those square branches fail, d_i^+, d_i^- and their product Delta_i are
nonsquares in Q. The two independent radicals generate a degree-four Galois
extension, with beta=(sqrt(d_i^+)+sqrt(d_i^-))/2 and beta^2=alpha_i,
using compatible radical signs.
Their product is 2alpha_i-s_i. Independent sign changes give exactly
beta, -beta, t/beta, -t/beta; the stated fixed field and conjugation follow.
Distinct K_i alone says nothing sufficient about disjointness of the L_i.

The cross-term cancellation in the certificate gives A_i^2+B_i^2=alpha_i;
B_i!=0 by irrationality, including the separate v_i=0 case. The two relative
norms are -1 and alpha_i, since Norm(beta_i)=-alpha_i. Reduction at s_i is
legitimate and gives the stated division by 5. A proper gcd of Bbar_i is a
factor; full gcd gives root Abar_i; only a unit allows inversion of Bbar_i.
This certificate uses field coefficients; the accepted distinct two-row identity
already solves rational-row attainment in one field. Neither fact solves two fields.

For gamma=U+V*alpha!=0, its norm is U^2+sUV+t^2V^2. If Norm(gamma)=m^2,
then m!=0 and gamma^2-Tr(gamma)*gamma+m^2=0 proves the compression identity.
If D=Tr(gamma)+2m=0, then (gamma+m)^2=0 implies gamma=-m; reversing the
sign gives D=-4m!=0. Actual trace zero would give negative norm at a real
embedding, so cannot occur with nonzero square norm. For a valid D,
gamma=(gamma+m)^2/D has square class [D]. A rational c is square in
Q(sqrt(Delta)) exactly when c or c/Delta is a rational square: the cross
coefficient of (a+b*sqrt(Delta))^2 forces a=0 or b=0.

Since [alpha]=[d^+]=[d^-] and d^+*d^-=Delta, the four tests in main §2
are necessary and sufficient, including negative inputs and rational denominators.
Both target classes have square rational norm because Norm(alpha)=t^2;
this is not a general statement about generators of nonsquare norm.
Exact reduced-fraction tests use integer square roots of numerator/denominator.

For Delta_i/d_j^±=a^2/b^2 in lowest terms, b^2 divides d_j^±, so b is a
unit modulo N. The two quotients reduce to R and 9R respectively; the returns
are a/b and a/(3b). These branches exclude the corresponding equal quadratic
subfields. Remaining intersections of d_1^± and d_2^± classes are not excluded;
no degree-sixteen compositum premise may be imported.

## 4. Anchored rotations, nonunits and actual second-field roots

The original P_j identity is correct, including nonzero c_j: v_j=0 gives
-t^2, otherwise u_j*v_j>=4N*ell>t. CRT makes both packets' modular images
equal, without making either a field square. For the accepted Q_j identity,
t^2-u^2*alpha_j=alpha_j*(v^2-alpha_j) proves the twisted relation directly.

The rotation matrix has transpose times itself equal to D^2 times the identity,
so A^2+B^2=s_j*D^2 and the integer rows (tD,A),(B,D) prove main (2).
The rational circle is parameterized completely by r=m/k and infinity; this
follows by taking the rational unit-circle ratio to the initial nonzero point
and its Cayley parameter. Replacing r by -1/r negates both coordinates.
For primitive negative m, the replacement (m',k')=(k,-m) preserves D and
negates A,B exactly; it preserves a symmetric numerator/denominator cap.
Infinity gives (-u_j,-v_j) and the same packet as (0,1). Thus signs/infinity
are handled correctly, but the finite rectangle is not every rational point.

For g=B^2-D^2R, the first row reduces to Rg and the second to g; this follows
from s_j=5R and t=2R, even when D is a nonunit. A proper gcd(g,N) is a
factor. If g=0, check gcd(D,N): unit gives B/D; proper gives a factor;
if full, check gcd(B,N) and return a proper factor if found, otherwise discard.
All inversions are justified. On a unit g branch no inverse of D is needed.
In fact the safety discard is unreachable for valid primitive (m,k): if a
prime p|N divided D, then k,m are nonzero modulo p and m^2=-k^2. The
formula B=2k(v_j*k+u_j*m) shows B=0 would force s_j=u_j^2+v_j^2=0
modulo p, impossible. Thus g=0 implies D is a unit, also for repeated powers.

Expanding Q before reduction gives constant t^2*D^2*B^2, linear coefficient
-(t^2*D^4+A^2*B^2), and quadratic coefficient A^2*D^2. Replacing alpha_i^2
by s_i*alpha_i-t^2 gives exactly C_0,C_1 of main (3). Writing e=s_i-s_j
and C=t^2*D^4-A^2*B^2, the two separate norms are

    Norm(B^2-D^2*alpha_i)=C-e*B^2*D^2,
    Norm(t^2*D^2-A^2*alpha_i)=t^2*(C-e*A^2*D^2).

This proves the displayed product norm, including D^4 and all signs. Each
row is nonzero by irreducibility (or is a nonzero constant if A=0), so E!=0.
A square gamma must give nonnegative square integer E. Conversely E=w^2
only passes the norm gate. Take m_0=tw and reverse its sign if S vanishes;
the additional S or S/Delta_i test is indispensable. The displayed roots
(gamma+m_0)/h and (gamma+m_0)/(h*(2alpha_i-s_i)) square to gamma exactly.

They must be simplified in Q[alpha_i] first. The monic equation
z^4-Tr(gamma)*z^2+Norm(gamma)=0 proves that z is integral. For any such z,
Tr(z) and Tr(alpha_i*z) are integers and direct expansion gives

    (2alpha_i-s_i)z=Tr(alpha_i*z)-s_i*Tr(z)+Tr(z)*alpha_i.

This proves both integer coefficients of the cleared root, without computing
a maximal order. Reduce that expression, dividing only by -3R. In particular
a displayed nonunit h is NEVER inverted modulo N. The reduced square is
Rg^2; for unit g both zbar and g are units, and zbar/g is a verified root.
Thus abstract hits of this integral packet with unit g are indeed recoverable.

The two-unrotated-packet observation also survives: in square classes,
[Q_1]_1=[alpha_1] and [Q_2]_2=[alpha_2]. If their product has the first
mixed orientation, [Q_2]_1=1, so Q_2 alone gives the opposite mixed orientation;
reverse the indices for the other case. A unit product has unit factors, and
the preceding clearing proof applies to each integral square hit. This covers
only these two packets, not subsets of their individual rows or larger families.

## 5. Rotation geometry: all three genera and the missing lifts

Let a,b be the two conjugate roots of f_i; then a+b=s_i and ab=t^2.
The four numbers a,b,s_j-a,s_j-b are distinct: an intersection would force
s_j=s_i or a rational root s_j/2 of f_i. None equals 0 or s_j.
Consequently F(X)=f_i(X)*f_i(s_j-X) has four simple roots. Its double cover
of the X-line is connected, has four simple branch points and even pole order
four at infinity; Riemann–Hurwitz gives genus one. The asserted rational point
(s_j/2,f_i(s_j/2)) is nonbranching and valid. It is a pointed genus-one curve,
but that point requires s_j/2 to be a rational square to lift to both u,v.

Adjoin sqrt(X), sqrt(s_j-X) and sqrt(F(X)). Their square classes over
the algebraic closure's rational function field are independent: the valuations
at 0, s_j and any root of F force each exponent in a square product to vanish.
The connected degree-eight cover branches at these six finite points and infinity.
At infinity both first radicands have odd valuation, but their local ratio is
a square over the algebraically closed residue field, so inertia has order two,
not four. All seven branch points contribute 8/2=4. Hence
2g-2=-16+7*4=12 and g=7. This normalization is the two-coordinate lift of
the norm curve; its rational points still need the actual field-square lift.

For main (5), equating coefficients of (a_0+b_0*alpha_i)^2 proves both
equations exactly. Substitution (a_0,b_0)=(tv,u) leaves error (t+uv)^2
in the second equation; (-tv,u) leaves (t-uv)^2. Either vanishing would make
Delta_j=(u^2-v^2)^2, impossible. These conic points do not solve the system.

Over the algebraic closure use the smooth rational circle u^2+v^2=s_j.
The two root coordinates a_0+b_0*a and a_0+b_0*b are an invertible linear
change of variables. Their radicands are

    a*(b-u^2)*(s_j-a-u^2),   b*(a-u^2)*(s_j-b-u^2).

The circle's map X=u^2 has degree four, branched only at 0,s_j,infinity.
Each of the four distinct displayed zero values avoids that branch locus and
has four distinct preimages. Each radicand therefore has eight simple zeros;
the two supports are disjoint. The two points at infinity on the circle give
u poles of order one and radicand poles of order four, hence no extra branching.
The odd zero divisors prove independence and geometric connectedness of the
degree-four cover. Its sixteen branch points each contribute two, so
2g-2=-8+32=24 and g=13. These are smooth-projective-normalization genera;
they neither prove emptiness nor establish a computational hardness bound.

A useful witness is an actual rational solution of (5), with paid height and
search cost and a unit cleared packet image. Knowing points or generators on
the elliptic quotient supplies neither the two coordinate lifts nor this last
square lift. A point with polynomially many bits alone is not a polynomial
search algorithm, and the report correctly provides no witness-supply theorem.

## 6. Reciprocal packets, all eight tests and their curves

Expansion gives constant p^2*t^2*q^2 and quadratic coefficient p^2*q^2;
reduction cancels the constant and leaves alpha_i*Lambda_i. If Lambda_i=0,
(p/q)^2 would be a rational root of f_i, impossible. Both norms are therefore
nonzero squares t^2*Lambda_i^2, without any smoothness conclusion.

For orientation j twisted, i ordinary, the exact choices are

    Lambda_j=epsilon_j*h^2, epsilon_j in {1,Delta_j},
    Lambda_i=epsilon_i*k^2, epsilon_i in {d_i^+,d_i^-}.

There are four choices for each of the two orientations; they need not be
nonisomorphic curves. The actual roots are h or h*(2alpha_j-s_j), and
k*(alpha_i+t) or k*(alpha_i-t), respectively. Squaring checks every case.
All epsilon are positive integers and modular units. For a reduced fraction
h=A/B, integrality of epsilon*h^2 implies B^2|epsilon, proving unit rational
denominators. This argument applies to k too, regardless of units of p,q.

Ordered row checks precede square tests: for row (a,b), proper gcd of
a^2-b^2R returns a factor; unit continues; full gcd calls gcd(b,N), returning
a/b if unit, a proper factor if proper, otherwise discarding. In these packets
no prime of N divides both coordinates, by gcd(p,q)=1 and t a unit. Indeed
full row gcd already forces b to be a unit: otherwise reduction at a prime
dividing b and N would also force that prime to divide a. The fallback
failure is unreachable here. Original rows with b=1 have the same exhaustive
factor/root/unit rule. Multiplying units cannot conceal a nonunit row.

On a unit packet, Lambda_i=Lambda_j modulo N is a unit. With
c_j=1 or -3R and c_i=3R or -R, both h*c_j and k*c_i are units;
their ratio squares to R. The rational denominators and field roots have
thus been checked separately from abstract class membership.

For a=p/q the two quartics -a^4+s_i*a^2-t^2 have simple roots: a=0 is
not a root and a repeated root would force Delta_i=0. Their root sets are
disjoint since subtraction gives (s_1-s_2)*a^2=0. Disjoint odd zero divisors
prove independence of the two quadratic covers. Infinity has pole order four
for each radicand and is unramified. Their connected degree-four fiber product
has eight branch points, giving 2g-2=-8+16=8, thus genus five for every choice.

The invariants of a->-a give the two stated quadrics with X/Z=a^2.
The quadratic polynomials f_1,f_2 have simple disjoint roots (subtract them);
their two square classes are independent. The degree-four cover of the X-line
has four branch points and even poles at infinity, hence genus one. The
projective intersection is smooth: finite root collisions would require a
common or repeated root, and at infinity X,H,J are nonzero so the two
gradients are independent. A usable rational quotient point needs Z!=0,
X/Z a nonzero rational square, and the unit packet condition after primitive
integer clearing. Neither this lift nor a point on the quotient is supplied.

## 7. Material qualification: the weaker conic's third denominator

The subtraction identity epsilon_1*h^2-epsilon_2*k^2=d*l^2, d=s_1-s_2,
l=pq, is correct. **Supplement lines 110–115 are too broad if extended to
arbitrary rational l with only h,k known to have unit reductions.** Let
A=Z_(N) denote rationals whose reduced denominators are coprime to N.
For h,k in A^* the identity ensures d*l^2 lies in A, but not that it lies in
N*A. Because epsilon_1=c_1^2 and epsilon_2=c_2^2/R modulo N, exact reduction
instead gives

    ((k*c_2)/(h*c_1))^2 = R*(1-d*l^2/(epsilon_1*h^2)) modulo N.

The asserted root follows **if and only if d*l^2 belongs to N*A**. A simple
sufficient repair is l in A, since N|d. The actual packet has integer l=pq,
so its extraction is unaffected. For arbitrary rational solutions the exact
condition is v_p(d)+2v_p(l)>=v_p(N) for every p|N. Integrality of the left
side alone supplies only the weaker inequality >=0. This explains the missing
implication without a numerical example or an unprovided rational-point oracle.

With that repair, the conic reduction is valid and its coefficient of l^2
vanishes modulo every prime divisor of N. The projective reduction is singular
at [0:0:1]; this point supplies no unit h,k slope. A solver for prescribed
unit h,k **and the corrected third-coordinate condition** gives the desired
modular root. This is a one-way reduction with explicit witness restrictions,
not existence, equivalence to every conic problem, or a factoring lower bound.

## 8. Finite execution, widths, retries and complete cost

Main §7 specifies the stage order, but not every sign/epsilon ordering. A
reproducible completion is: after Norm2 and the selector, build both fields;
test d_i^+,d_i^- in i=1,2 order; cross ratios in (i,j)=(1,2),(2,1) order,
plus before minus; Bbar_1,Bbar_2; the four original rows by j then u,v;
rotations by j then lexicographic (m,k); reciprocals lexicographically (p,q),
first row before second, then orientations (1,2),(2,1), and choices
(1,d_i^+),(1,d_i^-),(Delta_j,d_i^+),(Delta_j,d_i^-). Use nonnegative exact
rational square roots, positive m_0 unless S=0, and stop at the first verified
return. Discard noncoprime parameters and charge them. This is a completion
for future use, not a claim that all these details were frozen in the original.

All integers are constant-degree expressions in O(n)-bit fields and O(log M)-bit
parameters. Hence coefficients, norms, rational-square numerators/denominators,
root coordinates and cleared traces have O(n+log(M+1)) bits. Exact rational
cancellation and integer-coefficient verification take polynomial time at that
width, even if h is a nonunit. Streaming counters and gcd rejection give
O(M^2) candidates for M>=1; sequential arithmetic needs no random-access oracle.
Thus C_norm+poly(n)+M^2*poly(n+log(M+1)) time and
S_norm+poly(n+log(M+1)) space are valid conservative bounds. Outputting every
event for an experiment costs extra; the streaming space claim stores no trace.

For a raw uniform n-bit word x, x>=N and x=0 are failures; exactly
N-1-phi(N) other nonunits give proper gcds. At an odd prime power a unit
square has exactly two roots: each prime root lifts uniquely by its unit
derivative. CRT gives 2^r preimages even with unequal repeated exponents.
Conditional on R and any N,R-only inner transcript, x stays uniform on that
fiber. If the inner output is a root y, only x=y and x=-y give full/trivial
gcd(x-y,N); every other sign pattern gives a proper product of prime powers.
An inner factor succeeds for all preimages. This proves main (8), with G,J
including all early returns and failures, for any fixed execution completion.

For iid cold trials, if C is the mean full trial cost and sigma>0, conditioning
on the first trial gives E[T]=C+(1-sigma)E[T], hence C/sigma. No within-trial
cost/success independence is needed. Repeating the same deterministic N,R call
adds no chances. Warm caching across outer trials changes the cost law and
requires its own storage, lookup and conditional analysis; it is not priced here.

For continuing composite N, its smallest prime p<=sqrt(N) gives N/p-1
nonzero multiples below N, all proper gcds. Since 2^n<2N and
N/p-1>=sqrt(N)-1>=sqrt(N)/2, sigma>=1/(4sqrt(N)). With M=n^2 the full
reference trial costs O(N*poly(n)), so expected splitting costs at most
O(N^(3/2)*poly(n)). Paid elementary-factor, primality and perfect-power
handling is reapplied at every node; the complete tree has O(log N_0) nodes
when multiplicities are counted. Summing these uniform upper bounds proves
O(N_0^(3/2)*poly(log N_0)) expected complete time. Depth-first processing
releases lists before recursing and needs O(N_0*log N_0+poly(log N_0)) bits.
Ordinary complete trial division already gives the smaller deterministic
O(sqrt(N_0)*poly(log N_0)) envelope. These are upper bounds, not lower bounds
on W004's actual expected time or on alternative solvers. No speedup follows.

## 9. The proposed finite screen: symbolic coverage makes it unnecessary

The corpus rule is deterministic, deduplicates at most four indices for each
of at most twelve moduli, and exposes only N,R and public budgets to a worker.
Roots, factors, phi and generator metadata must stay outside the worker. No
seed or restart is needed. The 10-second setup, 1-second/200000-event workers,
60-second wave, 4096-bit width, soft traced 32-MiB memory and evidence caps
are bounded diagnostics, not mathematical running-time or OS memory claims.
Before any future run the exact event/checkpoint convention would also need
freezing. Exhaustion, timeout, unstarted cases and evidence-budget stops stay
UNKNOWN; malformed answers are validation failures, never coverage evidence.

There is a wording issue: “early factor/root or useful packet” must count row
gcd/root returns reached *inside* either scan too. A fully exhausted FAILURE
refutes completion of the specified finite program, not the correctness of the
report, which never asserts universal coverage. Stopping at the first success
can hide all mixed-target information; keeping labels does not reveal unvisited
candidates. More decisively, this corpus's coverage can already be proved.

**Coverage lemma (new, UNACCEPTED):** If 1<=M<N and N<=M(M+1), then for
every unit square R modulo N, the first-row checks over all coprime positive
1<=p,q<=M must return a proper factor or a root. This holds for repeated
prime powers and requires no field setup or target-square tests.

Proof. Use an arbitrary root x only in this existence argument, never in the
worker. The M+1 distinct residues 0,x,...,Mx have a cyclic consecutive gap
0<a<=N/(M+1)<=M. The corresponding index difference has absolute value
1<=b<=M, and a is congruent to x*b or -x*b modulo N. Put
d=gcd(a,b), p=a/d, q=b/d. These are positive coprime integers in the cap.
Let K=N/gcd(N,d)>1, since d<=M<N. From N|d*(p±x*q) follows
K|(p±x*q), hence K|(p^2-R*q^2). Thus its row gcd with N exceeds one.
If proper, it is a factor. If full, any prime dividing q and N would also
divide p, contradicting coprimality; q is therefore a unit and p/q is a root.
This proves the lemma, including loss of divisibility caused by primitive
normalization. It uses neither knowledge of x nor factors in the actual scan.

Throughout the proposed interval 128<=N<512, n is 8 or 9. Consequently
M=n^2 satisfies M<N and M^2>N, so the lemma applies to **every** promised
input in that interval, not just the selected residues. These interval
inequalities are a symbolic bound, not generated cases or a test execution.
Earlier returns can only supply success sooner. Any correctly completed run
therefore succeeds by the time the reciprocal scan ends, even if no useful
mixed packet exists anywhere in the cap. A FAILURE would expose a defect in
the implementation/specification or this proof, not discover a packet-supply
counterexample on that corpus. Budget stops would remain unknown.

**Recommendation: do not run this proposal as the next research test.** It
could serve only as implementation validation, which is not selected here.
An enlarged cap or a general impossibility conclusion is unwarranted. This
coverage lemma concerns small caps relative to the modulus and early row
returns; it supplies no asymptotic polynomial-time factoring theorem and no
mixed-target witness. The substantive next obligation remains a paid useful
point supply for main (5) or a reciprocal curve under the actual N,R law.

## 10. Primary sources and final recommendation

The [source scope ledger](W004-independent-review-evidence/source-review.md)
records the exact archived objects and inspected passages, including visual
checks. Rosser–Schoenfeld's [p.69 corollary](https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf)
supports the small-prime bound with its k>=6 condition. Cremona's
[chapter III §§3.5–3.6](https://johncremona.github.io/book/fulltext/chapter3.pdf)
uses bounded searches and explicit prime-divisor inputs in the rational-2-torsion
procedure; its rank bounds do not solve these packet curves. The
[CFOSS introduction](https://arxiv.org/html/math/0606580v1) distinguishes
Selmer coverings from rational-point discovery. No historical limitation is
promoted to a complete survey of algorithms available in 2026.

[Coppersmith §§2–3](https://link.springer.com/content/pdf/10.1007/BF00198464.pdf)
does use norms, character columns, actual roots and several common-evaluation
fields; p.170 expressly makes its smoothness transfer heuristic. That is no
supply law for these squared-coefficient packets. Shallit's inspected cost
paragraph is conditional, and BGH's Lemma 5.2 charges suitable prime generation
and its conic inputs. Neither inspection supplies a faster unconditional Norm2
contract here. No AEM retrieval was attempted. Source hashes establish object
identity, not theorem proofs; no novelty or full analytic-proof audit is claimed.

Accept only the scoped symbolic constructions, recovery and conservative cost
analysis after the conic and ordering qualifications; separately disposition the
new coverage proof. Preserve all original bytes and decline the proposed screen.
One-field attainment is solved; useful common mixed-target attainment at paid
height/search cost, its actual success mass and an improved complete cost remain
missing. No point oracle, uniform elliptic sampling, smoothness law, high-genus
emptiness assertion or factoring-hardness inference fills those obligations.
