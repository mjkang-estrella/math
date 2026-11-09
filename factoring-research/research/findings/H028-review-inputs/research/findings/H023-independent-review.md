# H023 — Independent symbolic review

2026-10-08. Independent review of the complete 661-line
[proposer report](H023-cluster-escape.md), SHA256
`c025d0e2c52ad9deb9540a8514cd170c2779e18e02cd60838b65a65b1974eeb3`,
and the complete [parent intake, including I1–I4](H023-intake.md), SHA256
`1fcb6070d9bf16c8a961054d2fad83c8f2123543caf8782c5170744d4bc62618`.
The proposer hash matches the handoff.

**Overall: ACCEPT the finite family, actual geometry counterexample, attained
primitive population, exact norm statements, and the optimizations as real
conditional relaxations. ACCEPT the parent's fixed-s binomial comparison
I1–I4 with its stated restrictions. No mathematical correction to their
displayed constants is required. REJECT promotion to a new factoring
algorithm, useful-supply theorem, or full factoring complexity improvement.**

The root-separation premise cannot hold uniformly even on this irreducible
ordinary-base family of actual height gamma=1. Moreover, simply removing
that premise from H022's population bound gives a false statement. These
are independently accepted informal mathematical results, not Lean proofs.
The positive rectangular populations count candidates only.

**Verified full factoring complexity improvement: NONE.**

## 1. Scope, inputs, and decisions

Read AGENTS.md, README.md, docs/SPECIFICATION.md, RESEARCH_LOOP.md,
RESEARCH_TEAM.md, research/STATE.md, and research/hypotheses/H023.md.
Read both complete submitted H023 documents, H020's disposition and its
normalization/containment argument, H022 Sections 1–4, its independent-review
scope and corrected disposition, and H016's processing disposition.
The present review instruction controls over stale pending-task text in STATE.
H024/H025 work was not read or duplicated.

This was symbolic review plus a bounded primary-source check. No mathematical
program, experiment, executable implementation, benchmark, root sample,
parameter sweep, package, shared check, Lean build, delegation, commit,
publication, or scheduler was used. File-reading and hashing utilities were
used for review provenance. Only this review file was written.

Claim decisions, with details below:

1. **ACCEPT — proposer Section 2:** exact ordinary digits, floor root, odd N,
   polynomial N-only recognition, actual gamma=1, and existence of the
   stipulated degree-scale sequences. Recognition is not an all-input selector.
2. **ACCEPT — Section 3:** both strict Rouche counts, irreducibility over Q,
   square-freeness, and actual normalized separation failure for every
   eligible H020 large-root split. No exceptional-M search is needed.
3. **ACCEPT — Sections 4–5:** resultant signs, distinct primitive rectangle
   and edge-rectangle counts, paid enumeration, uniform rational sizes,
   algebraic upper bounds, and actual edge norm strata.
4. **ACCEPT — Section 5:** the exact Q_threshold=1 population counterexample
   to H022 with its geometry condition deleted. This does not contradict H022.
5. **ACCEPT AS A REAL RELAXATION — Section 6:** inf C cubed = 16/3,
   including interior, unbalanced and boundary cases and the expressly
   conditional subset observation. No actual smoothness law follows.
6. **ACCEPT WITH THE EXISTING RESTRICTIONS — Section 7:** integer processing
   and good-prime ideal accounting are compatible with the displayed cost
   model. The stated missing distributional and extraction obligations remain.
7. **ACCEPT — Section 8:** the quotient/remainder identity, degree-halved
   representation and its irreducibility, gamma_H=1/2, isotropic cube 16/3,
   even-h skewed cube 40/9, fixed-parameter comparison, and binomial resultant.
   The numerical optima are model comparisons on their respective sequences.
8. **ACCEPT — parent I1–I4:** Eisenstein subfamily, common root, exact norms,
   attained edge exponent, full fixed-s optimization, and the sequence of
   model cubes 32(s+1)/(9s). Neither growing-s uniformity nor fixed-input
   dominance is proved.
9. **ACCEPT — Section 9:** fixed-degree injectivity and family counts, their
   stated uniform range, usual-scale sparsity and compact-degree union bound,
   and the explicit easy composite subsequences. No semiprime claim follows.
10. **ACCEPT — prior-art classification; minor citation precision revision:**
    special forms, skewed regions, translation and rotation are established
    NFS methods. Add Section 6.7 to the Kleinjung pinpoint for rotation.
    This bibliographic correction does not affect any mathematical result.
11. **REJECT — stronger interpretations:** a novel special-family record,
    general input coverage, smoothness or independent-rank guarantees,
    a square-root/proper-split guarantee, or an end-to-end factoring bound.

## 2. Finite construction and recognition

Use the exact submitted assumptions

    d >= 4 even, k=d-2,
    m >= 2^(d+7) even,
    M odd in [m/2^(d+3), m/2^(d+2)].

Throughout, q=m+1, A0=m^2+M+1, and

    f(X)=(X+1)^k(X^2+M+1)+1,   N=f(m),
    G(Y)=f(Y-1)=Y^d-2Y^(d-1)+(M+2)Y^k+1,
    t=log N,   D=t^(1/3)(log t)^(2/3),
    V=t^(2/3)(log t)^(1/3).

Asymptotic statements use d=(delta+o(1))(t/log t)^(1/3) with
fixed delta>0 and natural logarithms. Finite statements do not require
this scale assumption.

The finite assumptions give M>=16 and, by oddness, M>16. With out-of-range binomial
coefficients set to zero, expansion gives

    a_j = binom(k,j-2) + (M+1)binom(k,j) + [j=0].

Thus a_d=1 and all a_j are nonnegative. The submitted common upper bound is
valid even at the endpoint coefficients:

    a_j <= (M+2)2^k+1 <= m/16+2^(d-1)+1 < m.

For the last step, 2^(d-1)<=m/256 and 1<m/256 under the finite bound;
there is ample strict margin. There are no base-m carries. Separately,

    N > m^d,
    (m+1)^d-N = (m+1)^k(2m-M)-1 > 0.

Consequently m is exactly floor(N^(1/d)), and these are the actual ordinary
base-m digits, not merely a polynomial taking the value N. Since m is even,
(m+1)^k is odd and m^2+M+1 is even; N is odd.

For each even trial degree 4<=d<=n=bit_length(N), an integer root, a checked
division by (m+1)^(d-2), and subtraction recover the sole possible M.
Check the range, parities, finite m bound, and final identity. This is an
N-only recognizer. Binary-search integer root computation uses O(n)
comparisons per degree; even unreduced powers of n-bit trial bases to
exponents at most n have O(n^2) bits. Binomial coefficients and 2^(d+7)
also have polynomial bit lengths. Ordinary integer arithmetic therefore
gives a finite polynomial bit-work bound for the O(n) trials. No factor
of N, factorization of N-1, real-root oracle or degree advice is required.

The actual height A obeys M+2<=A<m. Also

    log m-(d+3)log 2 <= log M <= log A < log m,
    t=log N=d log m+O(d/m).

On the submitted degree scale, dD=(delta+o(1))V and
t/(dV)=1/delta+o(1), while d=o(V). Hence log M, log A and log m
all have leading coefficient 1/delta on the V scale. This proves actual
gamma=1, rather than assigning gamma from an upper bound.

For the sequence existence check, log m~3d^2 log d/delta^3 gives
t~3d^3 log d/delta^3 and log t~3 log d. It follows that
(t/log t)^(1/3)~d/delta. Even rounding of m and a fixed congruence class
of d do not change these limits. The interval for M eventually contains
many allowed odd integers. This establishes sequences for each fixed
positive delta, not alternative optimized degrees on every individual N.

## 3. Root counts, irreducibility, and true separation

For r=(2/M)^(1/k), 0<r<1. On |Y|=r,

    |M Y^k|=2,
    |G(Y)-M Y^k| <= 1+r^k(r^2+2r+2)
                  < 1+10/M < 2.

Every inequality needed for Rouche is strict. This gives exactly k roots
inside the smaller disk and none on its boundary. On the unit circle,

    |(M+2)Y^k|=M+2>4>=|Y^(k+2)-2Y^(k+1)+1|.

There are exactly k roots inside and exactly two outside the unit disk,
counting multiplicity, with no boundary roots. Moreover

    G(Y)=Y^k((Y-1)^2+M+1)+1>0  for real Y.

The two outside roots are therefore a nonreal conjugate pair.

The irreducibility argument is sound without already assuming square-freeness.
If monic G had a proper factorization over Q, Gauss's lemma gives monic
nonconstant factors over Z. Any factor containing one outside root contains
its conjugate, since its coefficients are real. Thus another nonconstant
factor has all its roots strictly inside the unit disk. Its constant term
is a nonzero integer, since G(0)=1, but its absolute value is a product
of root moduli less than one. This is impossible. Roots were counted with
multiplicity throughout; there is no circular assumption about simplicity.
Irreducibility in characteristic zero then gives square-freeness. Integral
translation preserves both conclusions for f.

Every cluster root alpha of f has |alpha+1|<r and hence |alpha|<2.
For H>=1 it is ineligible for H020's selected large-root set, whose cutoff
is |alpha|>=2H+2. Every permitted complement J therefore contains all
k>=2 cluster roots. For two such distinct roots,

    |alpha_i-alpha_j|/[max(1,|alpha_i|)max(1,|alpha_j|)] < 2r.

Consequently 0<kappa_J<r and

    log(1/kappa_J) > log(M/2)/(d-2)
                   = (delta^(-2)+o(1))D.

This is an upper bound on the actual minimum separation. Choosing better
root disks or a different eligible large-root subset cannot make a valid
certified lower bound satisfy log(1/kappa)=o(D). The conclusion concerns
these ordinary-base representations; it is not a theorem that every
other polynomial representation of the same integer has clustered roots.

## 4. Exact norms, attained populations, and the H022 counterexample

With the report's resultant convention, for monic P of degree d,

    Res(P,xY+z)=(-1)^d x^d P(-z/x).

Substitution into G, with d even, gives exactly

    Q(x,z)=z^d+2xz^(d-1)+(M+2)x^2 z^(d-2)+x^d.

Translation X=Y-1 preserves the resultant, and y=x+z gives g(m)=qx+z,
q=m+1. The coordinate change is integral and invertible, and
gcd(x,y)=gcd(x,z). Positive x fixes the sign associate. All displayed
norms are strictly positive on the positive rectangle. The x^d term
cannot be dropped.

For the original boxes take U=floor(exp(aD)), Z=floor(exp(cD)),
where a>=c>0 are fixed.

For U>=Z>=1, Mobius inversion is exact:

    P(U,Z)=sum_(j<=Z) mu(j) floor(U/j)floor(Z/j).

Expanding the floors costs O((U+Z)log(2Z)+Z), and truncating the absolutely
convergent sum sum mu(j)/j^2 costs O(U). Thus the proposed error term

    P(U,Z)=UZ/zeta(2)+O((U+Z)log(2Z)+U)

is valid with absolute constants. For log U=(a+o(1))D and
log Z=(c+o(1))D with fixed a>=c>0, the error divided by UZ tends
to zero. Subtracting the four prefix rectangles gives
UZ/(4 zeta(2)) plus the same-order error on U/2<x<=U, Z/2<z<=Z.
The symmetric formula also applies when the two axes are interchanged,
as in the parent's binomial calculation.

These are attained counts of distinct primitive linears of exponent a+c.
A raw UZ scan with gcd tests costs UZ poly(n) at the specified polynomial
operand widths, including rejected pairs. This is a generation upper bound
for integer box endpoints; the continuous constants used in optimizing
the asymptotic relaxation are not an uncharged exact-real primitive.

For all pairs in the full original rectangle,

    q+1<=qx+z<=qU+Z,
    log(qx+z)=(1/delta+o(1))V

uniformly. The four positive algebraic terms give an upper coefficient

    beta=max(a delta, 1/delta+c delta).

The 2log x and the difference between d and d-2 contribute O(D)=o(V).
On the upper-edge rectangle both x^d and (M+2)x^2 z^(d-2) supply
matching lower bounds, since log x=aD+O(1), log z=cD+O(1).
This proves uniform actual leading size beta there. The full box does
not have this common algebraic size; Q(1,1)=M+6 is the report's correct
counterexample. Neither statement is a smoothness assertion.

For the exact H022 comparison, let a>delta^(-2) and

    Z=floor(U/(M+2)^(1/k)),   H=U+Z.

Then Z tends to infinity with log Z=(a-delta^(-2)+o(1))D, and
Z<=U. The four terms of Q are bounded, respectively, by
U^d, 2U^d, U^d and U^d. Thus Q<=5U^d, while x<=H and y=x+z<=H.
There is no zero rational or algebraic norm and all primitive pairs qualify
as the type of normalized linear counted in H022.

The maximum of the k+1 binomial coefficients is at least 2^k/(k+1).
Therefore actual A, not a substituted upper bound, satisfies

    A >= (M+1)2^k/(k+1) >= m/[32(d-1)].

Since N^(1/d)<m+1 and H>=U,

    (2H)^d(d+1)A N^(-1/d)
      > 2^d U^d (d+1)m/[32(d-1)(m+1)]
      >= (2^d/64)U^d.

For even d>=10 this exceeds 5U^d. Every primitive rectangle member
therefore meets H022's exact real cutoff with Q_threshold=1. Rounding
the threshold down to an integer does not remove any qualifying integer
norm. No leading-exponent substitution is being used to decide membership.

Take a delta^2=2. The actual count exponent is
2a-delta^(-2)=3a/2. In H022's formula gamma=1, z_H022=2 and
Q_threshold=1 give F_1(2,1)=1 and would give exponent at most a.
The strict gap persists beyond all polynomial exceptional populations
and o(D) errors. This accepts the submitted counterexample to the
geometry-free count. The accepted geometry-conditional count is unchanged.

## 5. Original rectangle: complete real optimization

The submitted model fixes u=a+c>0, 0<c<=u/2, delta>0 and b>0, with

    W=1/delta+max((u-c)delta,1/delta+c delta),
    u>=b+W/(3b),   C>=u,   C>=2b.

For fixed u,delta the crossing is c0=(u-delta^(-2))/2. When
u delta^2>1 it is admissible and minimizes the maximum, giving
W_min=u delta/2+3/(2delta). When u delta^2<=1, the increasing
second branch is active throughout c>0; the closure c=0 gives
inf W=2/delta>=2sqrt(u). The first regime attains its smaller global
minimum sqrt(3u) at delta^2=3/u, a=2u/3, c=u/3.

Collection implies b<u and

    sqrt(3u)<=W<=3b(u-b)<=3u^2/4.

All sides are positive; squaring and dividing by u gives u^3>=16/3.
Since C>=u, no choice sacrificing collection optimality to the 2b
matrix charge improves the result. Equality at b=u/2 and C=u is
feasible in the displayed real inequalities. For u above this threshold
the same assignments give collection slack.

The a=c boundary gives W=2/delta+u delta/2, whose minimum is
2sqrt(u). At c=0 the closure has W=1/delta+max(u delta,1/delta),
also minimized at 2sqrt(u). Limits delta->0 or infinity cannot improve
the minimum at fixed u; b->0 or b>=u is infeasible for collection.
This confirms the claimed boundary coverage. A literal one-row strip
does not acquire the two-growing-axis Mobius asymptotic from a limit.

For a selected subset with attempt exponent v<=u, the additional assumption
that the same yield law applies gives W>=sqrt(3u)>=sqrt(3v) and
v>=b+W/(3b), hence v^3>=16/3. This is correct only with that
strategy-valid yield assumption, as the report expressly states.

The optimization has been accepted as mathematics about these inequalities.
It neither proves the assumed rate exp((-W/(3b)+o(1))D) nor sufficient
concentration, rank, squares, splitting, or a complete conditional algorithm.

## 6. Processing and extraction audit

H016's accepted integer construction applies to these polynomial-width
integer values and costs (B+S)poly(n), including exponent recovery.
With collection u>b, this fits the raw-scan exponent u. A separate
trial division by every prime for every candidate would instead cost
S B times polynomial factors and is not the invoked construction.

For G, irreducibility really supplies a degree-d field and beta is integral.
The map Z[beta]->Z/NZ with beta->q follows from G(q)=N. If a prime p
divides Q(x,z) for a primitive pair, p cannot divide x, since reduction
would otherwise give z^d=0 mod p. Thus any ideal over p containing
x beta+z must have beta=-z/x in its residue field. At
p not dividing disc(G) this labels a unique degree-one prime ideal,
and its exponent equals the integer p-adic norm exponent. This justifies
the linear specialization of the restricted good-prime accounting.

Factor-base construction, finite-field root work, joins/table access,
valuations and output widths remain charged. Expected polynomial work
per prime and candidate fits max(b,u); the accepted deterministic
B^2 preprocessing allowance fits max(2b,u). These are processing
compatibility statements, not yield or distribution results.

The discriminant is nonzero and has polynomial bit length, so computing it
and testing gcd(Q,disc(G)) can be done in polynomial work per candidate.
No factorization of the discriminant is necessary for that exclusion test.
Its effect on useful supply is still unknown. Modulo 2, G has only even
powers and is a square; hence 2 is bad. Nevertheless, for primitive x,z,

    Q(x,z) mod 2 = z^d+x^2 z^(d-2)+x^d = 1.

This checks the submitted local observation in all three allowed parity
cases; it establishes nothing about other bad primes.

Because G has no real roots, the field has signature (0,d/2) and unit
rank d/2-1. Absence of real sign columns does not eliminate units,
torsion, ideal-class obstructions, or the need for adequate characters.
An even norm valuation vector is not a certificate that an algebraic
element is a square. Even ideal valuations alone need not make it a square.

The report properly leaves character construction, useful dependencies,
algebraic square-root reconstruction, coefficient/denominator growth,
modular denominator invertibility, and proper gcd probability/restarts
unproved. More rows than columns guarantees a linear dependency, not a
productive split. The matrix exponent 2b remains part of the stated model.
No extraction theorem is accepted here by referring to standard NFS alone.

## 7. Alternative representations in the proposer report

For m=sM+r0 the exact polynomial identity is

    P(X)=(X+1)^k(sX^2+X+s-r0)+s,   P(m)=sN.

If M=floor(m/s), 0<=r0<s and log s=O(d), then all coefficients of
P have logarithmic size O(d), using binomial coefficients at most 2^k.
The negligible-height conclusion is valid on the stated V scale. It
does not assert that P is irreducible or that a complete factoring bound
has thereby been proved.

For independent M, the alternative s=floor(m/M) only gives r0<M.
Comparable remainders can retain log-height of order log m. The report
correctly does not convert absence of this particular simplification
into a lower bound on every polynomial-selection method.

For h=d/2 and K0=2m-M, direct expansion verifies both

    H(T)=T^h-K0 T^(h-1)+1,   H(q^2)=N,
    H(Y^2)=G(Y)+2Y^(d-2)(Y-q).

On |T|=1, K0>2 strictly dominates T^h+1. There are h-1 inside
roots and exactly one outside; the constant-term argument again proves
irreducibility. This argument does not require h even. Actual
log K0=(1/delta+o(1))V, while delta_H=delta/2, so gamma_H=1/2.
H is not being misidentified as a nonnegative ordinary-base polynomial.

For general h its exact linear resultant is

    Res(H,xT+z)=z^h+K0 x z^(h-1)+(-1)^h x^h.

This sign check is an expansion of the submitted polynomial, not a new
algorithmic extension. On an isotropic positive upper-edge rectangle,
K0(z/x)^(h-1)>=K0/2^(h-1) tends to infinity. Thus even when h is
odd the middle term dominates the possible negative x^h term uniformly.
The stated isotropic norm sum W_H=3/delta+u delta/4 and its minimum
sqrt(3u) at delta^2=12/u are valid.

For even h, all three terms are positive. Minimizing

    W_H=2/delta+max((u-c)delta/2,1/delta+c delta/2)

gives interior c=(u-2/delta^2)/2 when u delta^2>2, with
W_H=u delta/4+5/(2delta). Its global minimum is sqrt(5u/2)
at delta^2=10/u, a=3u/5, c=2u/5. In the complementary regime
the closure c=0 gives W_H=3/delta>=3sqrt(u/2), which is worse.
The same collection argument then gives inf C cubed = 40/9.
This confirms the boundary as well as the proposed interior calculation.

When both interiors apply at the same u,delta, subtraction gives exactly

    W_H-W_G=(4-u delta^2)/(4delta).

Thus H is not the better of these two optimized shapes at G's own
u delta^2=3. Different global degree optima must not be compared as
fixed-input dominance. The even-h positive-term result requires d=0 mod 4.

Finally, for s|k, ell=k/s,

    F_s(T)=T^ell+A0,   L_s(T)=q^s T-1,
    Res(F_s,L_s)=(-1)^ell (1+A0 q^k)=(-1)^ell N.

The sign follows from the linear resultant formula; it is not an omitted
unit. Also N=1 mod q, so q is invertible modulo N. The factorization
N-1=q^k A0 is publicly recoverable but is not a prime factorization of
q or A0. It does not establish smoothness of p-1 for any prime p|N.
The bivariate identity gives genuine structure without supplying an
unpaid small univariate pair or an automatic negligible-height model.

## 8. Parent extension I1–I4

All four equations pass independent review. Fix s>=1 as an integer,
require ell=(d-2)/s even and at least 2, and restrict M=1 mod 4.
For even m, A0=m^2+M+1=2 mod 4. Hence T^ell+A0 is Eisenstein
at 2 and irreducible. Testing the congruence costs polynomial work;
no factorization of A0 is needed. This congruence takes a fixed positive
fraction of the permitted odd M as their interval grows. Degrees
d=2 mod(2s) admit the same asymptotic scale sequences for each fixed s.

The common root is q^(-s) mod N, since

    q^k F_s(q^(-s)) = 1+A0 q^k = N mod N.

At positive primitive x,z, both exact resultants are as stated:

    Res(F_s,xT+z)=z^ell+A0 x^ell,
    Res(L_s,xT+z)=x+q^s z.

The rational resultant retains the leading coefficient q^s of L_s;
it is not just evaluation at q^(-s) with its denominator forgotten.
Using the integer numerator therefore gives the correct s/delta norm
coefficient. This norm calculation alone does not solve the rational
denominator/square-root bookkeeping for a complete factoring algorithm.

For c>=a>0 the transposed primitive edge count has exponent u=a+c.
Since ell D=(delta/s+o(1))V and log A0=(2/delta+o(1))V,
the two positive algebraic terms have coefficients c delta/s and
2/delta+a delta/s uniformly on that edge. The rational coefficient
is s/delta. This proves I1, including actual sizes and population,
without presuming smoothness.

At fixed u,delta, vary 0<a<=u/2 with c=u-a. The branches cross at

    a0=(u-2s/delta^2)/2.

When u delta^2>2s this lies in the allowed interval and minimizes
the maximum. Substitution yields I2:

    W_s=(s+1)/delta+u delta/(2s).

Arithmetic–geometric mean gives I3 with equality at

    delta^2=2s(s+1)/u,
    a=us/[2(s+1)],   c=u(s+2)/[2(s+1)],
    W_s=sqrt(2u(s+1)/s).

This equality is interior for every fixed s>=1. When u delta^2<=2s,
the second branch is active and increases with a; its closure minimum
is (s+2)/delta. At the best endpoint in that regime its square exceeds
2u(s+1)/s by us/2. The a=c endpoint cannot improve the fixed-delta
minimum. Delta tending to zero or infinity cannot improve the global
minimum at fixed u,s. Thus no omitted unbalanced or boundary regime
changes I3.

With exactly the same hypothetical collection and work inequalities,

    sqrt(2u(s+1)/s)<=3b(u-b)<=3u^2/4.

Squaring and dividing by u proves

    C^3>=u^3>=32(s+1)/(9s).

Equality in the real relaxation occurs at b=u/2, C=u and the I3
parameters; hence the displayed value is the infimum, proving I4.
The numerical substitutions s=1,2,4 give 64/9, 16/3, 40/9 as claimed.

The infimum of this sequence of fixed-s model constants is 32/9.
It is not attained by a finite s in this comparison, and it is not
the cost of a proved uniform algorithm with s=s(N)->infinity.
For fixed s, construction of q^s and the polynomial pair is polynomial
bit work. A growing-s assertion would require new uniform size, degree,
yield and processing estimates. Even at fixed s, an individual input
must actually have s|(d-2), even ell, the M congruence, and its given
delta; one cannot substitute its globally optimal delta at will.

The equality of some numerical constants does not identify the subfamilies:
the parent's s=4 construction requires d=2 mod 8, whereas the proposer's
positive even-h comparison requires d=0 mod 4. The documents make no
claim that those two particular restrictions hold on the same inputs.
All useful-yield and extraction limitations in Section 6 still apply.

## 9. Input density and composite scope

For fixed d, injectivity follows from recovering m by the strict floor-root
inequality and then recovering M uniquely. For each allowed even m, the
number of odd M is m/2^(d+4)+O(1). Summing over even m<=X gives
order X^2/2^d with absolute constants once X/2^(d+7) tends to infinity.
The rounding error is O(X); the excluded small-m prefix is negligible
under that same condition. This condition matters when d grows.

For N<=T use X=T^(1/d). The upper bound follows from m<X;
for the lower bound all even m<=floor(X)-1 satisfy N<(m+1)^d<=T.
This proves the report's uniform

    #family_d(T)=Theta(2^(-d) T^(2/d)).

At the usual growing-degree scale its logarithm is
2t/d-d log 2+O(1), and its fraction among integers up to exp(t)
is exp(-t+2t/d-d log 2+O(1))=exp((-1+o(1))t).
A polynomial number of degrees in a fixed positive compact range of
delta has total count at most exp(O(V)), so has the same sparse
fractional upper scale. No collision assumption across degrees is needed
for this union upper bound.

Keep that degree restriction: it is not a density bound for the entire
recognizer trying every even degree from 4 to n. In particular the
submitted fixed-d count at d=4 already gives Theta(T^(1/2)) members.
This is a scope check using the accepted formula, not an extension of
the proposed density theorem or a duplication of H025.

The submitted composite subsequence also checks directly: m=0 mod 6
and M=1 mod 6 give q=1 mod 3, A0=2 mod 3, and N=0 mod 3.
For sufficiently large m the interval contains these congruence classes
and N>3. Such subsequences retain the asymptotic scale and disprove
uniform geometry even within the composite-input promise. They are
easy composites, not evidence about hard or balanced-semiprime inputs.

## 10. Primary-source check and baseline wording

The following bounded checks were made online on 2026-10-08. They support
the classification of methods, not the family-specific derivations audited
above. No exhaustive priority search or best-possible baseline theorem
is claimed.

- LLMP explicitly develops special-form NFS and a rational/algebraic
  coprime-pair relation construction, gives the heuristic constant whose
  cube is 32/9, and says its expected-time analysis is not proved.
  Sections 1–3 support the report's historical and heuristic scope.
  [The number field sieve](https://wstein.org/129/references/Lenstra-Lenstra-Manasse-Pollard-The%20number%20field%20sieve.pdf).
- Murphy describes skewed rectangles and, in Section 5.1.2, translations
  and polynomial rotations preserving the modular root. This supports
  treating coefficient shape and anisotropic regions as established
  polynomial-selection practice.
  [Polynomial Selection thesis](https://maths-people.anu.edu.au/~brent/pd/Murphy-thesis.pdf).
- Kleinjung distinguishes special from general representation availability
  in Section 6.3 and discusses skewness in Sections 6.5–6.6. The clearest
  displayed f1+i f2 rotation passage is Section 6.7. Revise the proposer's
  pinpoint to include **6.7**; no claim about this particular high-degree
  rotation or its optimum is attributed to the chapter.
  [Polynomial selection chapter](https://www.joppebos.com/montgomery/book_ch6.pdf).
- Coxon's abstract explicitly treats nonlinear polynomial selection via
  small modular geometric progressions and short lattice vectors. It
  supports the existence of further selection architectures, not an
  automatic negligible-height result for the displayed bivariate family.
  [On nonlinear polynomial selection](https://arxiv.org/abs/1109.6398).
- Coppersmith's primary record describes reuse of smoothness computations.
  Lee–Venkatesan Remark 4.31 explicitly gives the multiple-polynomial cube
  (92+26 sqrt(13))/27 for the stated square-congruence construction. These
  do not supply a smoothness or proper-factoring theorem for H023's fixed
  family. [Coppersmith record](https://research.ibm.com/publications/modifications-to-the-number-field-sieve),
  [Lee–Venkatesan](https://arxiv.org/html/1805.08873v1).

The supported wording is: **H023 supplies an explicit sparse-family failure
of the ordinary-base separation premise and of its geometry-free count
extension. Its proposed relation mechanism is translated, skewed NFS on
a special family, with explicit alternative special-form representations.
Its optimized constants are values of conditional real relaxations. No
new algorithmic record or full factoring improvement has been established.**

## 11. Acceptance and next action

The parent may now promote the submitted finite geometry counterexample and
primitive candidate-population theorem to independently reviewed informal
mathematics, with the exact finite/sequence hypotheses and scope above.
The original and binomial optimizations may be recorded only as conditional
model calculations. The one suggested edit is the primary-source section
pinpoint; no correction to their algebra or constants is required.

No new research extension is proposed in this review. The intermediate
expansions and boundary checks above audit submitted claims; they are not
a new family, optimization domain, distribution law or algorithm. There
is therefore no separate reviewer-extension theorem to promote without
follow-up checking.

No finite experiment is warranted to decide these symbolic claims or to
test novelty. Close the current geometry question with this counterexample
and retain the established special-form baseline. Reopen an algorithmic
branch only for a concrete new primitive or a precisely stated post-filter
useful-yield/extraction claim that survives comparison on the same inputs
and allowed representations. This review does not initiate such work.

Shared code, Lean, STATE, registries, hypotheses, proposer report, parent
intake and old evidence were not edited. No shared test was run for this
document-only review. **Verified full factoring complexity improvement: NONE.**
