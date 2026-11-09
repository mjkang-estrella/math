# W002 Lens B — First independent symbolic review

2026-10-08. **Recommend acceptance of the scoped arithmetic, kernel, extraction,
and all-cap failure results after the two proof/specification completions below.
Reject promotion to a new COMPLETE classical factoring bound. Verified improvement:
NONE.** Acceptance of shared research results remains the coordinator's action.

The submission's core mathematics survives review. Its H026 paragraph does not,
as written, prove the asserted noncontainment: varying values or saying that
outside primes are possible is insufficient. Section 5 supplies an exact
arithmetic-support proof and narrower replacement text. The cubic trial bound
is supportable on a fixed finite multitape bit machine, but the original ledger
needs an access schedule. Section 6 supplies one, including coincident-column
updates, elimination, full provenance, certificates, and every basis extraction.
Neither completion changes the finite-trial L-constant or repairs useful yield.

The decisive failure is unconditional for the specified multiplier-one source:
every continuing composite N=s^2+1 fails at every positive cap. It is not a
factoring lower bound. The independent-uniform random-integer square-subset
theorem is a different probability model and supplies no law for this stream.

**Evidence and independence.** This is the FIRST review. There are no previous
review findings, proposer responses, or unresolved earlier-round objections.
The exact constructive report and preserved original both have SHA-256
`9d91b8b17dfeea5c36785a5c9a82512798b041fb230c67c8383c43b8bc588a80`.
The intake has SHA-256
`dcccf72ba83ec15ef67ad7e5b18be2b5a68f34e646826b6198b176d04b2ab958`.
The original W002 brief has SHA-256
`5f34c276110ba4ad79781b16b4a86d7ea3860671d168939aca9c399b0480f723`.

I independently verified all 22 original frozen inputs, all 42 original delivery
entries, and all 10 hashed primary-source records. There were no hash failures.
At review intake, STATE and W001 synthesis differed from their constructive-time
snapshots; both historical and review-intake versions are preserved separately.
The other 20 current input files matched those snapshots. The review freeze contains 69 files,
including governing documents, the original brief, both submissions, intake,
original manifests, current and historical dependency files, and primary sources.
See [freeze inventory](W002-adaptive-review-evidence/freeze.json) and
[identity checks](W002-adaptive-review-evidence/identity-checks.json).
At delivery all 69 frozen files and 78 delivery entries verify. Only mutable
STATE and W001 synthesis changed again during the review; the constructive
submission, original snapshot, intake, original manifests, and primary sources
remain unchanged. See [closing checks](W002-adaptive-review-evidence/closing-checks.json).

I read AGENTS.md, README.md, docs/SPECIFICATION.md, RESEARCH_LOOP.md,
RESEARCH_TEAM.md, current STATE, W001 synthesis, W001 Relations Card B,
H021/H024-H028/H031 dispositions, the H026 report and independent review,
and relevant corrected H027/H028/H031 sections. H031 is complete; stale lower
checkpoint paragraphs do not reopen it. The full 495-line Lens B submission
and coordinator intake are the objects of this review. No sibling W002 draft
or sibling review was read. No recursive delegation occurred.

## 1. Exact arithmetic generator and continuing domain

**Accept.** Interpret the procedure under the project's composite-input promise.
For an even composite, returning 2 is proper. If N=a^b with a>1 and b>=2,
returning a is proper. Testing b=2,...,n suffices: any nontrivial perfect-power
exponent is at most log_2 N. Binary-search roots with exact powering/comparison
give polynomial bit cost; aborting a power comparison above N keeps widths
bounded, or a polynomial larger-width implementation also suffices. Square
inputs are removed. An odd nonsquare composite is at least 15. A primality
test is outside this promised trial and would have to be paid in a recursive
factorer. No successful general splitter is established by this trial.

Let u=sqrt(N), s=floor(u), and alpha_i=(u+m_i)/d_i. Initially d_0=1.
The first step has m_1=s, d_1=N-s^2>0 and

    alpha_1=1/(u-s),       alpha_1'=-1/(u+s).

Thus alpha_1>1 and -1<alpha_1'<0. If these inequalities hold at i>=1,
a_i=floor(alpha_i)>=1 and

    alpha_(i+1)=1/(alpha_i-a_i)>1,
    alpha_(i+1)'=1/(alpha_i'-a_i) in (-1,0).

Irrationality prevents a zero fractional part. Rationalization gives exactly
the submitted m and d updates. Inductively d_i divides N-m_i^2, since
m_(i+1)=-m_i modulo d_i. Hence the new division is exact. Positivity of the
new d also follows from alpha_(i+1)-alpha_(i+1)'>0. The conjugate bounds give

    0<d_i=2u/(alpha_i-alpha_i')<2u,
    u-d_i<m_i<u, hence |m_i|<u                         (i>=1).

The integer-floor implementation is exact: write s+m_i=a d_i+b with
0<=b<d_i; then 0<=b+(u-s)<d_i, so adding the discarded fraction does not
change the quotient's floor. Initial a_0=s is consistent. Also a_i<2u
for i>=1. State values, intermediate products/divisions, and modular
numerators therefore have O(n) bits. For N>=15, d_i<2sqrt(N)<N; the full-gcd
branch is unreachable, while the declared meaning of that branch is correct.

Here is an independent derivation of the norm identity, without storing large
convergents. In the proof only, set A_-2=0,A_-1=1,B_-2=1,B_-1=0 and apply the
ordinary numerator/denominator recurrence. The complete-quotient identity is

    u=(A_i alpha_(i+1)+A_(i-1))/(B_i alpha_(i+1)+B_(i-1)).

Equating rational and irrational coefficients gives

    A_i=m_(i+1) B_i+d_(i+1) B_(i-1),
    N B_i=m_(i+1) A_i+d_(i+1) A_(i-1).

Subtract the second equality times B_i from the first times A_i, and use
the recurrence determinant A_i B_(i-1)-A_(i-1) B_i=(-1)^(i+1). This proves

    A_i^2-N B_i^2=(-1)^(i+1) d_(i+1).

Reduction of the numerator recurrence modulo N proves X_i=A_i mod N by
induction. The stored relation is exactly X_i^2=r_i mod N, with the sign
attached to original index i. No B_i or unreduced A_i is an algorithm input
or stored operand. Attempted steps, including the step finding an early gcd,
are charged. Any retained r_i is a unit, and so is X_i: a prime dividing N
and X_i would divide r_i, contradicting gcd(|r_i|,N)=1.

For the cap, k=ceil(log_2(n+1)), e=ceil(sqrt(nk)), and H=2^e are computable
using integer comparisons and roots. Writing H is cheap; iterating to H is
not. With natural logarithms,

    n=ln(N)/ln(2)+O(1),       k=ln(n)/ln(2)+O(1),
    ln(H)=ln(2)*sqrt(nk)+O(1)
         =(1+o(1))*sqrt(ln(N)*ln ln(N)).

Consequently H has L_N[1/2,1] scale. This confirms the submitted conversion;
there is no missing factor sqrt(ln 2) or ln 2.

## 2. Coprime refinement and equality of square kernels

**Accept, with the simultaneous-update specification made explicit.** Start
with distinct norms greater than 1 while retaining every original row and
its root. Duplicate norms can share a base column; duplicate rows are still
separate coordinates of the dependency space.

For an overlapping pair a,b and g=gcd(a,b), replace their contributions in
each row simultaneously by

    a^x b^y = g^(x+y) (a/g)^x (b/g)^y.

Then discard unit factors and merge equal integer-valued columns with all
unchanged columns, adding exponents. In particular, if g=a, or a/g=b/g, or
a new value equals another old value, use the old x,y once before merging.
Do not repeatedly substitute a newly introduced column merely because it has
an old name. This precise rule handles divisibility and all coincidences.

The product of the distinct base entries decreases by at least a factor g:
before merging the replacement multiset has product ab/g, and merging
duplicates only reduces that product. Therefore

    P=sum_(current base elements c) log_2(c)

decreases by at least 1. Initially P<=S=sum_i bit_length(|r_i|), and every
current entry contributes at least 1. There are at most S refinements and
at most S simultaneous entries. The process ends with all distinct entries
pairwise coprime. Exact decompositions are preserved at every step, with
nonnegative integer exponents. Every entry descends by divisibility from an
input norm, remains a unit modulo N, and has O(n) bits. In any row, each
exponent and indeed the sum of its exponents is at most log_2 |r_i|=O(n).
No factorization of a hard residual is used.

For each resulting c_j, an exact square test distinguishes c_j=b_j^2 from
a nonsquare; save b_j in the square case. Define a row matrix R with its
sign column and the exponent-parity columns of the nonsquare c_j. Then

    E in ker(R^T)
      iff product_(i in E) r_i is a positive integer square.       (K)

The forward implication follows by the submitted explicit root formula.
For the converse, the product must have even sign. A nonsquare c_j has at
least one prime of odd valuation. Pairwise coprimality excludes that prime
from all other c_k, so its total valuation has the parity of V_j(E).
Thus V_j(E) is even. Mathematical unique factorization proves necessity;
the algorithm never asks for that prime. Square columns impose no parity
condition, but their roots and full exponents must remain for extraction.

Equation (K) is exactly the same signed square kernel as full prime
decomposition of the original list, including residuals 1 and empty bases.
It says nothing about creating new relations, increasing productive rank,
or ideal-square conditions in an NFS number field. Singleton peeling is
valid only on a fixed list; preserving original rows when enlarging a list
is necessary. The submitted implementation correctly retains them all.

## 3. Quotient by global sign, basis sufficiency, and certificate scope

**Accept for every odd continuing N, without a squarefree assumption.** Put
q(E)=sqrt(product_(i in E) r_i)>0 for E in K, with q(empty)=1. All these
roots are units. The implementation's Y(E) is q(E) mod N, because it uses
the saved positive roots of square columns and half the even exponents of
nonsquare columns. A huge integer q(E) is a proof object only.

Let I=E intersect F and D=E xor F. Positive integer roots satisfy

    q(E) q(F)=q(D)*product_(i in I)|r_i|.

Meanwhile X(E)X(F)=X(D)*product_(i in I)X_i^2 modulo N. Division by units
therefore gives, exactly,

    z(E)z(F)/z(D)=product_(i in I) sign(r_i),
    z(E)=X(E)/q(E) in R_N={z in (Z/NZ)^*:z^2=1}.

Thus phi(E)=[z(E)] is a homomorphism K -> R_N/{+1,-1}. It need not be
a homomorphism into unquotiented R_N. The submission does not assume the
stronger assertion. The quotient is an elementary abelian 2-group, so a
homomorphism trivial on a basis is trivial on K. Conversely, if some
dependency has nontrivial image, at least one basis vector has nontrivial
image. Testing every basis vector is sufficient for this exact fixed list.

For completeness, write N=product p^a in the proof only. Since N is odd,
gcd(z-1,z+1) has no prime divisor of N. Since p^a divides (z-1)(z+1), the
whole prime power p^a divides exactly one factor. Hence

    gcd(z-1,N)*gcd(z+1,N)=N,
    gcd(gcd(z-1,N),gcd(z+1,N))=1.

Both are proper precisely when z is neither global sign. Multiplication by
the unit Y preserves these gcds, so the implementation using X-Y and X+Y
has the same outcomes. Repeated prime factors present no exception. If N
has only one distinct odd prime, the quotient is trivial, consistently with
the separately paid perfect-power branch.

Uniform sampling from finite K, if considered only for comparison, assigns
equal mass to every image fiber; its productive fraction is exactly
1-1/|image(phi)|. For two distinct odd primes the quotient has size 2,
so the fraction is 0 or 1/2. No uniformity of actual CFRAC roots follows.
The actual trial is deterministic and uses no sampled dependency or inverse.

A `FAIL(H)` certificate concerns only the retained H-prefix, its signed
integer-square subsets, and this root/gcd interface. It is not evidence that
no proper factor exists or that other arithmetic operations fail. Section 6
specifies sufficient stored data to check that the tested vectors really
span the full kernel, rather than merely checking a list of failed subsets.

## 4. Symbolic failure for every cap

**Accept.** For N=s^2+1 with s>=2, entering the relation phase entails that
s is even and N is composite and not a perfect power. Direct substitution
gives m_1=s,d_1=1,a_1=2s; substituting again preserves these values forever.
Here the denominator is the complete-quotient d_i, not the much larger
convergent denominator B_i. All gcd(d_i,N) equal 1 and r_i=(-1)^(i+1).

Since s^2=-1 mod N, X_0=s and the recurrence with coefficient 2s yields
X_i=s^(i+1) mod N for every i>=0: the induction step uses
2s^2+1=-1=s^2 mod N. The positive base is empty. For H>=1 the sign column
is nonzero, has rank 1, and the square kernel has dimension H-1. A subset
belongs to K exactly when sum_(i in E)(i+1) is even, and then

    q(E)=1,       X(E)=s^(sum_(i in E)(i+1)) in {+1,-1} mod N.

Consequently phi is trivial and every attempted extraction fails for every
positive cap, however large. When H=1 the kernel is zero-dimensional; for
H>=2 it has nonzero dependencies, and its dimension grows without bound.
The original sentence about not lacking dependencies should be understood
in this latter regime, not as denying the H=1 edge case.

The continuing composite family is valid without any experiment. For
s=50t+2, t>=1, s is even, N>5, and N=5 mod 25. Thus 5 divides N exactly
once. This both proves compositeness and excludes every nontrivial perfect
power. The algorithm itself is not told 5 or the family label and includes
no trial division by 5. Other algorithms may immediately split these inputs;
the failure is about the specified procedure.

The fixed-prime-screen extension also holds. Given a fixed finite P, put
B=2*product_(p in P)p. Any prime q dividing B^2+1 is odd, outside P, and
has order 4 for B modulo q; hence q=1 mod 4. This supplies the required q
and a root of -1 without an appeal to primes in arithmetic progressions.
For a root r mod q, exactly one j mod q makes r+jq a root mod q^2, because
the linear coefficient 2r is nonzero mod q. Choose another lift. CRT between
that residue mod q^2 and s=0 mod B gives infinitely many even s with

    v_q(s^2+1)=1,       gcd(s^2+1,product P)=1.

For sufficiently large members N>q, so N is composite and not a perfect
power, and the same infinite recurrence proof applies. This is an existence
proof for each fixed finite P. It supplies neither an efficient hard-input
generator nor a counterexample to every input-dependent growing prime cutoff.
Balanced semiprimes, changed multiplier laws, and arbitrary preprocessing
are outside this proof.

The useful-yield condition (Y) is necessary and sufficient for this trial's
success after its elementary cases: an early proper gcd, or nontrivial phi
on the generated square kernel. It is uniformly false on the family above,
even for an uncapped stream. Larger caps, better refinement, sparse matrices,
more nullity, and deterministic restarts do not change that conclusion.

## 5. H026 noncontainment: required repair and exact support proof

**Do not accept the original paragraph as a completed proof. Accept the narrower
statement proved here.** H026 does not say that an N-dependent rule is excluded
merely for being adaptive. Its union already permits arbitrary N-dependent
selection from

    U_n={e in Z^n: sum ceil(j/2)^2 e_j^2 <=40n^2},
    u_e=product p_j^max(e_j,0), v_e=product p_j^max(-e_j,0),
    w_N(e)=u_e-Nv_e,

where p_j are the first n primes. Thus varying selected values, changing an
index to (N,i), or using a new basis for the same fixed arithmetic pairs would
not defeat the proof. Moreover, H026's unrestricted residual w_N(e) can itself
contain outside primes: its counting theorem restricts the *eligible smooth*
residuals. Saying only that a CFRAC residual is rough does not by itself prove
that its generating pair lies outside U_n.

Here is an arithmetic-support witness for the generating pairs, entirely on
the continuing domain of this exact trial. Let q range over sufficiently large
primes different from 2 and 5. Choose the unique even a with 2<=a<=48 and

    a*q = 2 mod 25.

It exists because q is invertible modulo 25, and exactly one of each pair of
lifts differing by 25 is even. Put s=a*q and N=s^2+1. Then s is even and
s=2 mod 25, so N=5 mod 25. Consequently N is an odd non-perfect-power
composite for large q, and it reaches the relation phase. Section 4 shows
that it has no early gcd at any later time either. Its first exact arithmetic
pair and relation are

    (u,v)=(s^2,1),       u-Nv=-1,       X_0=s<N.

Now n=bit_length(N)=2 log_2(q)+O(1), uniformly in 2<=a<=48. The accepted
H026 dependency bound p_n<=4(n+1)^2 implies q>p_n for all sufficiently
large q. But q divides u=s^2. Every u_e from H026 is supported on primes
at most p_n. Therefore this literal generating pair is not (u_e,v_e) for
any e, even if H026's energy cutoff were removed. A permutation or renaming
of its fixed alphabet cannot change that prime-support contradiction.
There are infinitely many such q by infinitude of primes. The chosen q,a
are proof witnesses only; the algorithm obtains s by its paid integer root.

This proves absence of a blanket, arithmetic-pair-preserving containment of
the submitted generator on its continuing domain in H026's fixed alphabet.
It does not contradict H026, identify a counterexample inside H026's balanced
semiprime ensemble, or show that the same N lacks some *different* H026
relation. In fact these witnesses are divisible by 5 and are not in that
ensemble. Their adaptive positive base is empty: the failure of pair
containment must not be described as evidence that every completed base
introduces new primes. The squared numerator already suffices.

For clarity, the report's separate intuition that actual admitted residuals
can contain outside primes can also be justified, with a different and
strictly limited witness. Take a sufficiently large prime q=2 mod 3.
Choose an even s in (q,q+18) with s not divisible by 3 and
s^2+q not divisible by 9. Such a residue modulo 18 exists: there are six
nonzero-mod-3 choices modulo 9, and exactly two solve s^2=-q mod 9
(each of the two roots modulo 3 has a unique lift, since 2s is a unit
modulo 3). Parity then fixes a lift modulo 18. Put N=s^2+q. We have s=floor(sqrt N),
v_3(N)=1, and N is odd composite and not a perfect power. Also
gcd(s,q)=1, because q<s<q+18<2q for large q. Thus d_1=q is actually
retained, with gcd(d_1,N)=1, and q>p_n again follows from n=2log_2 q+O(1).
Infinitely many primes 2 mod 3 follow elementarily by taking a prime factor
2 mod 3 of 3Q-1 if Q were the product of all such primes. This is a symbolic
existence proof, not a prime search or finite congruence experiment.

That second witness proves outside support in the admitted stream. It does
not prove that the input reaches the final base-construction phase at the
prescribed H; a later early gcd might succeed. No assertion about its full
trial's base or useful yield is needed or made. The first witness already
establishes the required literal pair noncontainment with all-cap survival.

**Proposed replacement for the H026 paragraph and corresponding opening and
handoff claims:**

> H026 counts a fixed set of first-n-prime-supported arithmetic pairs (u,v)
> at a specified aligned energy, and only its eligible base-smooth residuals.
> N-dependent selection alone would remain covered. The present CFRAC source
> has no blanket literal-pair containment in that universe: the family
> s=a*q, a even in [2,48], a*q=2 mod 25, N=s^2+1, has first pair (s^2,1)
> with q>p_n for sufficiently large q, and passes the stated preprocessing.
> Hence that particular fixed-universe counting proof does not directly
> bound this whole generator. This is a scope separation, not useful supply,
> a statement on H026's semiprime ensemble, or a theorem excluding a newly
> proved containment/encoding for a restricted input set.

Retain the support proof with the replacement. A new controlled union of
arithmetic pairs or a different encoding would require its own proof and
cardinality/width bounds. Nothing here excludes one. The cost of building
the actual coprime base remains fully charged, but the base's N-dependent
name is not the mathematical reason for the scope separation.

## 6. Sequential-tape ledger: required completion, same upper envelope

**Accept the claimed envelope for the concrete schedule below. The original
counts alone are not a complete access proof.** Use a fixed finite number of
ordinary tapes, each with bit encoding, delimiters or fixed padded fields,
and sequential scans. A record index has O(log(H+1)) bits. Scalar arithmetic
on O(w)-bit quantities, where w=n+ceil(log_2(H+1))+2, takes a fixed polynomial
in w by schoolbook multiplication, long division, Euclid, binary powers, and
binary-search integer roots. Logarithms in the potential are never computed.

Let h count all attempted recurrence steps, including a successful early
step. On the no-factor path h=H and there are h retained rows. Put
S=sum_i bit_length(|r_i|); on this path h<=S<=h(n+1). For a path exiting
earlier, omit all later-stage charges. Arrays below are tapes, not randomly
indexed constant-cost objects.

**Generation and initialization.** Keep the recurrence's scalar registers on
short work tapes and append one original record per retained row. This costs
(h+1)poly(w). Build the increasing distinct base list by sequential insertion
or repeated minimum selection from the h norms; O((h+1)^2 poly(w)) suffices.
Build a dense, row-major decomposition tape by a full base scan per original
row, putting a 1 in the column for its norm and zeros elsewhere. Norm 1 has
an all-zero row. This costs O(h(S+1)poly(w)), with every duplicate row retained.

**Finding the specified overlapping pair.** Maintain an increasing base-value
tape and a duplicate scan tape. Hold the outer value a in a scalar buffer and
scan every later b on the other tape, rewinding it between outer values.
This uses at most O((t+1)^2 poly(w)) bit work when the current length is t.
It finds the first overlapping pair in the specified increasing order and
does not traverse the entire decomposition matrix for each gcd. This last
point prevents an extra factor h from entering the pair search.

**Merging values and updating decompositions.** Only a,b are removed and at
most three values g,a/g,b/g are proposed for insertion. Sort these constant
many scalar values and merge them into a sequential pass over the unchanged
increasing list. Unit values are dropped, equal values are coalesced, and
the new list is written to another tape. A constant-size description of the
affected old/new values suffices to synchronize the old and new column orders.

For each original row, first scan its old exponent row to collect x,y and
the exponents at any unchanged columns colliding with the at-most-three
new values. There are at most five affected integer labels altogether.
On a second pass, stream its unchanged entries into the new order and insert
the updated contributions g^(x+y),(a/g)^x,(b/g)^y with coincidences added.
The row may be copied to a scratch tape for this two-pass operation. Scanning
the old and new base lists for each row, and rewinding those lists, is also
charged. All this takes O(h(t+1)poly(w)) per refinement, not a hidden
random lookup or an h*t^2 remapping. Values and row exponents retain the
width bounds proved in section 2. Discard the previous matrix once the new
one is complete; do not retain every historical matrix.

With at most S refinements and t<=S, pair search and row updates together
cost at most

    O((S+1)*[(S+1)^2+h(S+1)] poly(w))
       <= (S+1)^3 poly(w).

Square-test each final base value once, keeping its root if square. Assemble
the sign/nonsquare parity matrix with sequential scans of the original sign
and full-exponent records. These costs and the output writes are within the
same bound. No product of all base values or all residuals is materialized.

**Elimination with full provenance.** Let m<=S+1 be the parity-column count
and D=m+h the width of a parity row with its h-bit provenance vector. Process
original rows in order. Start the current row with its parity vector and
the appropriate unit provenance. Keep prior nonzero pivot rows on a tape,
ordered by their leading 1 positions. For each pivot, locate its position
in the current row by a charged scan; if that bit is 1, xor the full parity
and provenance row with a scratch copy of the pivot. Rewind the current
row and scratch tapes as needed. Each pivot comparison/xor/copy uses O(D)
bit visits times polynomial scalar/control overhead. There are at most h
pivots per input row.

After all prior pivots, a nonzero reduced row is inserted into the pivot tape
by copying that tape in order. If it is zero, append its provenance to the
kernel tape. An inserted row has zero in every earlier leading position;
future pivot insertions do not invalidate the distinct-leading-position
independence of stored pivots. Total work is

    O((h+1)^2(S+h+1) poly(w)),

including pivot scans, ordered insertion, identity-provenance construction,
and all tape rewinds. This is a deterministic dense elimination with fixed
pivot choices. It avoids treating m separate whole-matrix searches as free.

Each zero-row provenance has a 1 at its own original row index and zeros
at all later original indices, since only earlier input rows were used to
reduce it. These vectors are independent. If there are rho nonzero pivots,
they are independent row combinations, while the h-rho zero provenances
are independent dependencies. Rank-nullity now proves that these h-rho
vectors are a full basis of K. This handles rank deficiency, square-only
bases, empty positive bases, and zero-dimensional kernels uniformly.

**Certificate content.** Retain the original rows, exact decompositions,
base values/square roots, nonzero pivot rows with their provenances, the
zero-row kernel provenances, and the two gcd outcomes for each tested
basis vector. The triangular last-index property certifies independence
of the latter; distinct leading pivot positions certify independence of
the former. Their counts sum to h. Checking their claimed row combinations
against R takes O(h^2(S+h+1)poly(w)) with sequential scans, if an explicit
verification pass is desired. Thus basis completeness has a finite certificate
at the same envelope. No exponentially long enumeration of all dependencies
or stored transcript of every intermediate elimination state is required.

**Testing every basis vector.** Copy the next h-bit selection mask onto a
scratch tape. Stream the h original roots and the row-major full exponents
in original-index order. Maintain a sequential tape of t aggregate exponents;
for each included row, make a full accumulator pass in parallel with that
row, updating and writing the accumulator tape. Rewinds cost O(t poly(w))
per row. Accumulate the selected X_i modulo N along the same original-row
scan. Finally scan base values/roots and aggregate exponents together to
perform the t modular binary powers and products, the congruence check,
and both gcds. Each V_j<=O(hn) needs only O(log(hn+1)) bits. A single
dependency therefore costs O((h+1)(S+1)poly(w)); all at-most-h vectors cost
O(h(h+1)(S+1)poly(w)). There is no inverse in this implementation and no
uncharged large integer square root. Every failed vector is paid.

**Space and final substitution.** A constant number of copies of the dense
h-by-t decomposition, parity/provenance matrix, pivot tape, kernel basis,
original records, and scratch tapes fits

    O([h(S+1)+h^2+S+1] poly(w))
       <= (h+1)^2 poly(w).

The certificate can be retained in that bound and written by sequential
output. Intermediate copies replace old copies; histories of all refinement
steps are not retained. Generation, arithmetic, initialization, all scans,
elimination, roots, powers, verification, gcds, and output are therefore
bounded by (H+1)^3 poly(n+log H), with (H+1)^2 poly(n+log H) space.
The polynomial factors have logarithm O(log n)=o(sqrt(ln N ln ln N)) under
the constructed H. This yields the advertised L_N[1/2,3] time and
L_N[1/2,2] space *upper envelopes for a finite trial*.

**Proposed cost repair:** incorporate this schedule, or an equivalent one,
into section 4 of the working report. At minimum specify simultaneous
coalescing row updates, separate short base-pair scans, streaming dense
elimination with provenance, the basis-completeness certificate, and
sequential full-exponent accumulation for every dependency. The original
snapshot and original manifests must remain unchanged. This is an on-paper
bit-machine realization, not a runtime claim about an unprovided program
or a Lean refinement. No implementation was executed for this review.

## 7. Primary prior art and probability-model boundaries

**Accept the comparisons at their stated scopes, with an additional attribution
to Morrison–Brillhart Remark 3.13.** These are checks of relevant primary
passages and theorem statements, not an independent audit of every proof in
the literature. Exact inspected artifacts and read scopes are recorded in
[source inspection](W002-adaptive-review-evidence/source-inspection.json).

1. **CFRAC:** Morrison–Brillhart, *A Method of Factoring and the Factorization
   of F7*, pp. 184–191, gives the norm identity, numerator computation modulo
   N, exact denominator division, bounds, signed exponent/history vectors,
   reconstruction, and gcd extraction. Remark 3.5 discusses short periods
   and using a multiplier, illustrating the period-one issue with Fermat
   numbers. The general s^2+1 proof in this review is a direct derivation;
   it need not be attributed to a source statement about every such composite.
   Remark 3.13 on p. 191 also explicitly notes that multiplying failed square
   congruences produces another failure. The quotient proof above supplies
   the precise signed-overlap and all-odd-N basis formulation; the underlying
   closure observation is already prior art. The original generator is
   known CFRAC, not a novel source of small norms. Text and rendered pp. 186
   and 191 were inspected. [Primary paper](https://www.ams.org/journals/mcom/1975-29-129/S0025-5718-1975-0371800-5/S0025-5718-1975-0371800-5.pdf).

2. **Coprime bases:** Bernstein's 2004-04-04 manuscript, permanent identifier
   `f32943f0bb67a9317d4021513f9eee5a`, and the author's index identify the
   2005 *Journal of Algorithms* paper. Sections 1–2 define the primitive;
   section 8 explains aggregate-bit M-time and multitape arithmetic;
   Algorithm 18.1/Theorem 18.2 construct the natural base;
   Algorithm 21.2/Theorem 21.3 recover decompositions. The essentially-linear
   claim is in the aggregate bit size, not in the number of residuals while
   ignoring widths. Its sparse nonzero decomposition output is included;
   materializing this submission's dense matrices costs extra. This review
   uses its own slower schedule for the submitted
   algorithm and does not silently substitute Bernstein's bound. I did not
   re-audit the full recursive complexity proof. [Primary manuscript](https://cr.yp.to/lineartime/dcba-20040404.pdf).

3. **QS:** Pomerance, *Smooth numbers and the quadratic sieve*, pp. 75–80,
   distinguishes smoothness of structured polynomial values from proved
   smooth-number counts and labels the substitution heuristic. Page 79
   includes the matrix cost and the sparse-linear-algebra route to the
   conventional heuristic L_N[1/2,1] estimate. The submitted L_N[1/2,3]
   unsuccessful trial is not an improved complete model. The chapter's
   historical claims about practical digit ranges or then-best deterministic
   factoring are not being adopted as current benchmarks.
   [Primary chapter](https://math.dartmouth.edu/~carlp/PDF/qs08.pdf).

4. **Random-integer surrogate:** Balister–Bollobás–Morris, pp. 50–52,
   defines independent uniform positive integers from {1,...,X}, with
   replacement, and the first *nonempty* square-product subset time T(X).
   Its Theorem 1.1 states the high-probability threshold at exp(-gamma)J(X),
   with J(X)=min_(2<=y<=X) pi(y)X/Psi(X,y), and the introduction gives
   log J(X)~sqrt(2 log X log log X). For X=floor(2sqrt N), direct substitution
   yields log J(X)~sqrt(log N log log N). Thus allowing arbitrary composite
   samples and free postprocessing does not lower this law's leading
   square-availability scale. This is a statement about positive iid samples,
   not signed, periodic, correlated CFRAC data, root choices, or productive
   factoring. No lower bound for the actual generator follows. I checked
   the definitions and theorem, not the full 95-page proof.
   [Primary paper](https://annals.math.princeton.edu/wp-content/uploads/annals-v188-n1-p02-p.pdf).

5. **NFS:** Coppersmith's pp. 169–170 explicitly qualify the smoothness
   substitution and estimates as heuristic. Section 3, including pp. 175–177,
   includes common rational columns, separate field columns, roots, and the
   approximately 1.902 general-NFS constant, compared with approximately
   1.923 for ordinary GNFS. The separate section-4 factory is amortized
   precomputation, not that cold bound. H028's accepted scoped reconstruction
   is compatible with these passages. No NFS success law or constant is
   inherited by this CFRAC stream. The complete analytic justification of
   NFS is not asserted to have been proved by that primary paper or audited
   here. [Primary paper](https://link.springer.com/content/pdf/10.1007/BF00198464.pdf).

6. **Rigorous square congruences versus factoring:** In the archived
   Lee–Venkatesan v1, Theorem 2.1 supplies a square-congruence result for
   their randomized NFS variant. Theorem 2.3 has a Blum-semiprime promise
   and Conjecture 7.82; section 7 specifies the productive-character
   nondependence condition, and Remark 7.85 extends that question to their
   multiple-polynomial construction. The relevant passages were inspected,
   not the full analytic proof. Neither that conjecture nor the distribution
   law applies to the deterministic capped CFRAC stream or automatically
   to H031's different law. [Primary v1](https://arxiv.org/html/1805.08873v1).

7. **Rigorous complete baseline:** Lenstra–Pomerance's printed p. 483
   states existence of a probabilistic algorithm factoring any positive
   integer completely with expected time at most L_N[1/2,1+o(1)]. The
   scanned theorem page was visually checked against the archived image.
   This is an expected complete-factorization result, distinct from both
   a heuristic GNFS bound and the submitted deterministic failing trial.
   Its full proof and section-12 machine conventions were not re-audited
   here. [Primary paper](https://math.dartmouth.edu/~carlp/PDF/paper85.pdf).

8. **Schnorr-type methods:** Vera v1, sections 1–2 and Figure 1, describes
   fixed-first-prime smooth-product relation search, its close-vector target,
   and sufficient norm conditions. These passages do not prove useful supply
   for this new residual list. The PDF's own header identifies arXiv
   1003.5461v1. The original retrieval log records two blocked Schnorr 2021
   PDF interfaces; there is no archived full Schnorr PDF and I did not treat
   its abstract or a search snippet as a checked proof. The comparison remains
   confined to the accessible Vera mechanism and accepted H026 scope.
   [Primary Vera v1](https://arxiv.org/abs/1003.5461v1).

Fresh web inspection during this review succeeded for the BBM primary PDF
but returned 403 for the Morrison–Brillhart URL and 502 for the Bernstein
manuscript URL. Those failures do not remove the already archived full PDFs,
whose bytes verify and whose relevant contents were read locally. The
Lenstra–Pomerance text extraction has no useful text layer; the theorem-page
image, not missing OCR or an inferred snippet, supports its scope. All reused
archives are identified as copies rather than new downloads. The source
ledger records these distinctions and the uninspected-proof limitations.

## 8. Precise repairs and narrow disposition

**R1 — Required mathematical completion, H026 scope.** Replace the unsupported
varying-value argument with the first support proof and replacement text in
section 5. Narrow the opening and handoff accordingly. The second witness
may be retained only as an admitted-stream statement; it does not establish
outside-prime support in a completed H-step base. If a stronger claim is
retained about H026's semiprime ensemble, growing pre-screens, or all completed
adaptive bases, that claim remains unresolved and is not accepted by this
review. No such stronger claim is needed for the trial's scoped closure.

**R2 — Required cost/specification completion.** Add the sequential schedule
in section 6 (or an equally explicit one) to support the cubic trial envelope
and quadratic retained-space envelope. Specify that column substitutions are
simultaneous, collisions are merged arithmetically, all original rows survive,
and only a constant number of current tape copies is kept. Specify what makes
`FAIL(H)` a complete fixed-list certificate. With this completion, the
original time, memory, and natural-log L-constants can stand unchanged.

**C1 — Prior-art clarification.** Add Remark 3.13 to the CFRAC discussion:
failed-congruence closure is already observed there. The quotient-by-global-sign
proof remains a useful precise formulation, without a novelty claim. State
that Remark 3.5 uses Fermat numbers as its short-period example; the general
s^2+1 assertion follows from the supplied symbolic recurrence proof.

**C2 — Edge-case clarification.** Say that the family has kernel dimension
H-1, with nonzero dependencies for H>=2 and arbitrarily large
nullity as H grows. H=1 has no nonzero dependency but still fails. The
rank/nullity formulas themselves require no correction.

**Recommend accepting after R1/R2:** the finite N-only recurrence and its
exact divisions/widths; sound early factors; the costed composite coprime
decomposition; equality of signed integer-square kernels; the quotient
homomorphism and basis sufficiency for all odd continuing N; the full
fixed-list failure certificate; the finite-trial cost/space upper bounds;
the all-cap s^2+1 failure and fixed-finite-screen extension; and the stated
primary-literature distinctions. These are reviewed on-paper results, not
an executed implementation, formal refinement, or new factoring algorithm.

**Reject:** any successful complete-factoring interpretation of
L_N[1/2,3]; a positive restart probability for this unchanged deterministic
trial on the failure family; the inference that more dependencies force
productive roots; transfer of the uniform random-integer theorem to the
actual CFRAC stream; or any factoring-hardness conclusion. The exact
multiplier-one realization is closed as a new uniform factoring mechanism.

There is no remaining algebraic objection to these narrowed results once
the two completions are adopted. There is also no positive-yield theorem
left to infer: condition (Y) is actually false uniformly for this procedure.
Nothing proves failure on balanced semiprimes, under arbitrary growing
prime cutoffs, for different multiplier laws, for all adaptive generators,
or for classical factoring generally. A different algorithm would need its
own complete-cost and actual-success argument.

**Next proof/test: none selected.** No computation is essential to this
review, so no computational protocol is proposed. Increasing the cap or
implementing the same processor cannot overturn the symbolic obstruction.
A new candidate or another review round is not needed merely to fill a quota.
The coordinator can adopt the local repairs and record this narrow disposition
while preserving the original submission and evidence.

All executed processing was document reading/discovery, archival copying,
hashing, HTML text extraction, primary-source inspection, PDF page rendering,
and report/evidence authoring. No mathematical experiment, arithmetic sweep,
benchmark, solver implementation, Lean work, package installation, outside-
project write, shared-file edit, commit, publication, scheduler, or delegation
occurred. All owned artifacts are this report or the exclusive
`W002-adaptive-review-*` prefix. The delivery seal is
[W002-adaptive-review-delivery.sha256](W002-adaptive-review-delivery.sha256).
**Verified COMPLETE classical factoring complexity improvement remains NONE.**
