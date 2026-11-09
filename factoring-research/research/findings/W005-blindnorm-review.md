# W005 — independent review of the new joint blinded Norm2 sampler

2026-10-08. **Recommend scoped acceptance of the sampler, its conditional
independence, and the improved reference-wrapper upper bound. Parent decides
acceptance.** No algebraic repair is needed for the stated odd, unit-norm domain.
Adopt the explicit stopping probabilities and interface qualifications below.
**Verified new improvement over established complete classical factoring: NONE.**
No useful-packet probability or novelty claim is established.

The new sampler really removes the two full Norm2 lists from the joint factoring
trial. Its output has the same law for every outer root of a fixed R, including
unequal odd prime-power factors. This is a different acquisition contract from
an N,R-only solver. The changed contract is valid for this wrapper; it does not
silently preserve the old deterministic certificate/field distribution.

Throughout the joint factoring branch, gcd(N,30)=1 and R is a unit square.
The finite-ring sampler lemma alone needs only odd N and invertibility of 5R.

The exact authorized finite screen ran once: **8 PASS, 0 REJECT, 0 UNKNOWN**,
62,504/62,504 sampler pairs. Both controls detected dependence in all eight cases.
All 12 repository tests, source audit, pinned Lean build and Audit.lean passed.
These are finite implementation checks, not a proof of the general theorem.

## 1. Scope and preserved evidence

This is the first review of this new sampler. The task's accepted predecessor
dispositions govern W003/W004; the other W005 field-point, reflection, orthogonal
pair and strip reviews were not reopened. I read the required instructions and
specification, README, the complete assessed sampler and preregistration, and the
W004 extraction/cost passages. Exact local read scopes, bounded primary-source
searches and retrieval failures are in the
[scope ledger](W005-blindnorm-review-evidence/source-review.md).

Fourteen input snapshots were frozen before execution in
[inputs.json](W005-blindnorm-review-evidence/inputs.json), including the parent
mechanism, protocol, instruction files and task registry. The exclusive
[evaluator source](W005-blindnorm-review-screen.py), byte-identical
[frozen source](W005-blindnorm-review-evidence/frozen-screen.py), and
[execution completion](W005-blindnorm-review-evidence/execution-completion.txt)
were hashed before the first and only run. Source hash:

    8753dee670931e970502f22dc125369a26b20ade4f206e50a98dd7df99248ffa

Frozen parent protocol hash:

    f4344d8019b7aaa3a60b8add1a60f65845e45a7962f23185c9b1b05a32bfe553

All 39 delivery files are listed in the
[delivery manifest](W005-blindnorm-review-delivery.sha256); frozen-input,
saved-Counter and local-link verification found no mismatches.

Only this report and the assigned prefix were authored. No task was launched,
cancelled or modified; no package, shared solver, registry, scheduler, publication,
commit or Lean source change occurred. The required baseline check was executed;
it checks existing Lean code and proves nothing new about this sampler. The
experiment is a primitive distribution audit, not the repository's factoring
benchmark. Its explicit user authorization takes precedence over older
symbolic-only and general register/iterate defaults.

## 2. The two contracts and what the outer root legitimately supplies

The old standalone Norm2 contract receives N,R only, on the accepted odd unit
domain with 5 invertible, and returns a verified pair with norm 5R. Its existence
argument even covers unit R that is not a square. The fixed deterministic
two-list reference has a fixed tie rule, O(N n²) bit time and O(N n) working bits.
It needs no root of R. Its output is generally one particular representation.

The new joint wrapper starts with a freshly generated outer word x. After its
range and gcd checks, x is a unit and R=x² mod N. The wrapper is therefore
entitled to compute x(1+2i); x is its own random choice, not advice or an oracle
input to the overall N-only factoring program. The new primitive receives this
x and returns a factor, a certificate, or FAILURE. A certificate alone is passed
to the field/packet routine. There is no claim that an unrelated N,R-only call
can efficiently reproduce this sampling procedure without a root or another
known representation. Equality of observable output distributions does not
construct such a simulator.

The surviving fact needed for the factoring reduction is independence from the
hidden choice of root **conditional on N,R**. It is not equality with the old
Norm2 output distribution. The following proof establishes exactly the former.

## 3. Finite-ring surjectivity, fibers and uniform norm representations

Let A=Z/NZ and S=A[i]=A[T]/(T²+1), with N odd, gcd(N,5)=1. It is a free
rank-two A-module, even when it splits or has nilpotents. For ξ=a+ib,
Norm(ξ)=a²+b². A unit norm gives inverse conjugate(ξ)/Norm(ξ); conversely the
norm of a unit is a unit. Thus the gcd test recognizes S* exactly.

Write H={w in S: Norm(w)=1}. It is a group. The homomorphism

    f:S* -> H,       f(ξ)=ξ/conjugate(ξ)

has kernel A*: f(ξ)=1 implies ξ=conjugate(ξ), so 2b=0 and b=0. A scalar
unit in S is precisely a unit in A. Therefore every nonempty fiber has φ(N)
elements, with no squarefree assumption.

To prove that every fiber is nonempty, work first in A_p=Z/p^kZ. For
w=c+ie with c²+e²=1, at least one of 1+c and 1−c is a unit: their sum is 2,
and A_p is local. If 1+c is a unit, take

    ξ=(1+c)+ie,       Norm(ξ)=2(1+c),       ξ=w*conjugate(ξ).

Otherwise 1−c is a unit, and take

    ξ=e+i(1−c),       Norm(ξ)=2(1−c),       ξ=w*conjugate(ξ).

Both identities follow directly from c²+e²=1; both chosen ξ are units. The
second chart has the stated positive sign, so it also covers w=−1. Choose charts
independently at the different prime powers and apply CRT to a and b. This is
an existence proof only; the sampler performs no factorization or CRT search.
Using one global chart is not sufficient over a composite ring.

For additional cardinality detail, let χ_p=(-1|p). Modulo p, S is F_p×F_p
if χ_p=1, and F_(p²) if χ_p=−1. Each residue pair has p^(2k−2) lifts,
and being a unit depends only on its reduction modulo p. Hence

    |S_(p^k)*| = p^(2k−2)(p−1)(p−χ_p),
    |H_(p^k)|  = p^(k−1)(p−χ_p),
    |H|        = product_(p^k || N) p^(k−1)(p−χ_p).

Uniform a,b conditioned on the norm being a unit is uniform on S*. Equal
fibers now prove that f(ξ) is exactly uniform on H. Its coordinates are
(c,e)=((a²−b²)/h,2ab/h), precisely those in the proposal.

Fix a unit x with x²=R and let z_x=x(1+2i). Its norm is 5R, a unit. The
map H -> T_R={z in S: Norm(z)=5R}, w -> z_x w, is a bijection: for any
z in T_R the unique inverse image is z/z_x, which has norm one. Thus every
certificate in T_R has exactly φ(N) preimages among all unit input pairs,
for every fixed x. Its distribution is 1/|H| at each certificate and is
independent of which root x was used. Individual u or v need not be units;
only their norm has to be. This is enough for the construction and its later
separate gcd/denominator tests.

Equivalently, for two roots x,x', the scalar x'/x belongs to H because its
square is one. Multiplication by this scalar permutes uniform H. This directly
identifies the invariance needed to conceal the full CRT sign pattern.

## 4. Exact law with both rejection caps and early factors

Use independent fair raw bits. Put

    n=bitlength(N),  q=N/2^n,  L=2(n+1),  B=2(n+1)^3,
    s=[1−(1−q)^L]^2.

Here s is the probability that both coordinates enter [0,N) within their
respective caps in one pair attempt. For any z in [0,N), the probability that
z first occurs as an accepted coordinate on draw j is
(1−q)^(j−1)/2^n. This does not depend on z. Conditional on entry, the coordinate
is exactly uniform; the entry index is independent of its accepted value.
The two coordinates remain independent. Skipping b when a has exhausted its
cap is equivalent to reserving an independent, unused block for b.

For a uniform pair in A² define

    α=Pr[gcd(a²+b²,N)=1],
    β=Pr[1<gcd(a²+b²,N)<N],
    γ=Pr[gcd(a²+b²,N)=N],       α+β+γ=1.

One pair attempt terminates in a certificate with probability sα and in a
factor with probability sβ. It continues with probability

    δ=(1−s)+sγ=1−s(α+β).

For j=1,...,B and any z in T_R,

    Pr[first terminal result is certificate z at j | x,R]
      = δ^(j−1) sα/|H|.

Consequently the complete capped sampler has probabilities

    C_B = α/(α+β) * (1−δ^B)       certificate,
    F_B = β/(α+β) * (1−δ^B)       verified proper factor,
    E_B = δ^B                    exhaustion/FAILURE.

There is no zero denominator: α>0. The certificate law conditional on the
certificate branch remains exactly uniform, independent of x. Each particular
factor's distribution is likewise independent of x, since it is computed
before x enters the arithmetic. All raw-entry failures are included in δ.
Earlier rejected pairs and the first terminal index do not alter this proof:
they depend only on earlier independent blocks, while the final pair is
uniform conditional on being a unit. No limiting or asymptotic uniformity is
being substituted for exact equality.

Prime-power full-gcd counts, although not required by the algorithm, also admit
an exact check. If χ_p=−1 then v_p(a²+b²)=2 min(v_p(a),v_p(b)) before
truncation; the number with norm zero modulo p^k is p^(2 floor(k/2)). If
χ_p=1, an invertible linear change gives norm XY. Counting v_p(X)=j<k
and the separate X=0 row gives p^(k−1)((k+1)p−k) zero-norm pairs. CRT
multiplies these counts, giving γ after division by N²; β=1−α−γ. These
are proof/evaluator quantities, not factorizations supplied to the sampler.

The proposed elementary bound is correct:

    α=product_(p|N) (1−1/p)(1−χ_p/p)
      >= (φ(N)/N)^2 >= 1/(n+1)^2.

For the last inequality, ordering the r distinct primes gives p_j>=j+1;
the product of (1−1/p_j) is at least the telescoping 1/(r+1), and r<=n.
Since q>1/2 on the stated domain,

    s >= κ_n=(1−2^(−2(n+1)))²,
    E_B <= exp[−B s α] <= exp[−2κ_n(n+1)] <= exp[−(n+1)].

The final looser inequality uses κ_n>1/2, already true for n>=1. The exact
κ_n is retained rather than charging truncated raw draws as untruncated draws.
This is a bound on **factor-or-certificate termination**, not on certificate
probability alone: early factors occupy F_B. That distinction needs to remain
in any later statement using a near-one success probability.

With uncapped coordinate rejection, expected words per coordinate are 1/q<2,
and the expected pair count to a factor or certificate is 1/(α+β)<=(n+1)^2.
If coordinates are capped but pairs are unbounded, it is 1/[s(α+β)]. Those
are valid expected-cost variants, but their random-bit count is not worst-case
bounded. The doubly capped version has both bounds.

## 5. The information boundary and precisely which conditioning is safe

Conditional on a raw outer word being a unit with square R, X is uniform on
the m=2^r roots of R. Each odd prime-power root lifts uniquely from one of the
two prime roots, and CRT multiplies their counts. The theorem above implies

    Pr[X=x, Z=z, certificate | R] = (1/m) C_B/|H|.

Let the inner routine be any function of N,R,Z and independent randomness,
with adaptive tests or filters of these values. Its entire permitted transcript
is a function of variables independent of X conditional on R. Therefore, for
every possible such transcript τ of positive probability,

    Pr[X=x | R, τ] = 1/m.

This remains true after conditioning on an inner field selection, failed packet
tests, a root-return event, or the value of the returned root. An adaptive filter
can make Z nonuniform among surviving certificates, but cannot create dependence
on X. This is the needed distinction between certificate uniformity and retained
root-choice independence. The complexity claims below apply only to bounded,
paid filters; unrestricted adaptive computation has no polynomial cost promise.

The interface restriction is real. From the accepted rotation (c,e) and Z one
can recover the original x without a square-root computation:

    A=c u+e v=x,       D=−e u+c v=2x.

An inner routine with that tape could return y=x identically, making the root
split probability zero even when r>=2. The raw pair a,b reveals c,e and causes
the same failure. A seed that reconstructs the blinding tape, shared mutable
state containing it, or a callback exposing x is equally disallowed. Merely
saying that the tape was generated independently of X does not help: its joint
observation with Z reveals X.

The claimed transcript is the subroutine's specified data/randomness, not all
machine state or arbitrary timing observations of accepted-pair arithmetic.
Use separate fresh random blocks, an explicit input boundary and no such
side channel in the mathematical program. Counts of earlier rejected pairs
and coordinate entry indices are safe by the argument above, but they need
not be passed. In particular an accepted pair's variable-time inverse trace
is not automatically safe merely because it was computed before using x.

Also, **x-independent selection alone is not a sufficient replacement stopping
condition**. For example, accepting only unit pairs with b=0 yields rotation
1 and exposes (x,2x), although the selection predicate itself never reads x.
The specified stopping law is valid because the first accepted pair is uniform
on all S*. It may not be replaced with a biased chart, extra final-pair filter
or operation-time cutoff without a fresh distribution argument. The finite
evaluator's wall-time cap is a measurement constraint, not a sampler rule.

## 6. W004 extraction and the raw-word success identity transfer

W004's selector and extraction need a verified canonical (u,v) with
u²+v²=5R mod N. They do not require the previous lexicographically chosen
representation. CRT lifting, shifts, positive nonsquare discriminants, distinct
fields, s_i≡5R, and f_i'(R)=−3R are valid for every such pair. Their heights
remain O(n), with the accepted small auxiliary-prime bound. They are functions
only of permitted inner inputs, so their adaptive early returns preserve §5.

The crucial localized square-root recovery is also pointwise. For an integral
packet whose exact field square root is z_i, monicity implies z_i is integral,
and

    (2α_i−s_i)z_i
       = Tr(α_i z_i)−s_i Tr(z_i)+Tr(z_i) α_i in Z[α_i].

After exact cancellation, reduce the right side and divide by −3R, a unit.
For the anchored packet its image squares to Rg²; a unit g gives y=zbar_i/g,
and y²=R is checked. Any nonunit branch retains its individual gcd/root/failure
test. The accepted reciprocal qualification also remains: for the weaker
rational conic require (s_1−s_2)l² in N Z_(N); the actual integer l=pq
satisfies it. A random auxiliary certificate removes neither condition.

To state the success law correctly, let g(R,z),j(R,z) be the disjoint
probabilities of an inner proper-factor/root return for certificate z, including
all of its internal failures. Average these under the NEW uniform T_R law:

    gbar(R) = |H|^(-1) sum_(z in T_R) g(R,z),
    jbar(R) = |H|^(-1) sum_(z in T_R) j(R,z),
    G(R) = F_B + C_B*gbar(R),
    J(R) = C_B*jbar(R).

Here G includes the new sampler's proper gcd returns, J requires it to deliver
a certificate, and 1−G−J includes E_B and all inner failures. Both probabilities
are independent of the choice of x over R. For a returned root y, exactly two
outer choices, x=y and x=−y, fail to split via gcd(x−y,N); all other CRT sign
patterns give a proper divisor. With repeated prime powers the agreeing signs
contribute whole p^k factors and the disagreeing signs contribute none, because
2y is a unit. For r=1 the useful-root contribution is exactly zero.

Thus the original algebraic FORM of the raw outer success identity survives:

    σ_N = [N−1−φ(N)
           + sum_(R in QR_N*) (2^r G(R)+(2^r−2)J(R))] / 2^n.

The first term counts all nonzero, nonunit raw words below N; x=0 and x>=N
remain failures. This formula is exact, not a lower bound on J. It uses the
new G,J above, not the old deterministic indicators. Changing the certificate
distribution can change field selection and useful packet frequency arbitrarily
within the stated probabilities. No former unproved supply law transfers.

## 7. Paid cost and the conservative complete expected upper bound

Each pair needs a constant number of arithmetic operations on O(n)-bit values:
two coordinate draws, norm, gcd, and on its unit branch one inverse and the
rotation/certificate products. All coordinates are reduced canonically. No
factorization, totient evaluation, group-order computation, table or CRT oracle
is used in the sampler.

The finite raw-bit allowance is at most

    2*B*L*n = 8 n(n+1)^4

bits per invocation, plus the outer n bits. The sampler uses at most B norm/gcd
tests and stops after its first unit inverse/certificate or proper factor.
Even pricing each arithmetic operation by a coarse schoolbook O(n³) envelope
gives O(n^6) worst-case bit work, including O(n^5) raw-bit handling. This bound
is deliberately loose. Constantly many O(n)-bit registers and counters suffice
for streaming sampler space O(n); storing all logs/tapes would cost extra.
The unbounded expected variants are polynomial in n by the paid pair-count
bounds; the doubly capped one is the finite-tape version used below.

Retaining W004's fixed selector and M=n² finite scans adds
poly(n)+M² poly(n+log(M+1)) time and polynomial space, with all discarded rows,
square tests, exact cancellations and verification charged. Thus a cold outer
trial now has a uniform polynomial bit-cost bound P(n). It is a specified
finite classical program, though no implementation/refinement of this complete
wrapper was added here. A replacement inner search with unbounded heights or
unbounded repetitions would require another cost proof.

For every continuing composite N>=4, a smallest prime p<=sqrt(N) gives
N/p−1 nonzero multiples below N. All have proper gcd with N. Since
2^n<2N and N/p−1>=sqrt(N)−1>=sqrt(N)/2,

    σ_N >= 1/(4 sqrt(N)).

This lower bound is taken BEFORE certificate sampling, so it cannot be reduced
by sampler exhaustion or zero useful-packet mass. For iid cold trials with mean
cost C<=P(n), the renewal identity E[T]=C+(1−σ_N)E[T] gives

    E[T_split(N)] <= 4 sqrt(N) P(n).

It does not assume trial cost and success are independent within a trial.
Primality testing must stop recursion at prime nodes; use the contract's paid
deterministic polynomial primality ingredient. Extraction of 2,3,5, exact
division, and any perfect-power preprocessing are likewise paid polynomial
work. Perfect-power preprocessing is optional for this upper bound, since the
old gcd branch also splits composite prime powers.

Every factor return is checked. The complete factor tree has at most
floor(log2 N_0) leaves counted with multiplicity, and fewer internal nodes.
At any encountered node its conditional expected splitting cost obeys the
same uniform bound with N<=N_0 and n<=n_0. Summing over the at most O(n_0)
nodes proves

    E[T_complete(N_0)] = O(sqrt(N_0) poly(log N_0)).

The algorithm terminates almost surely with correct complete factorization;
fresh cold retries and primality termination are part of the claim. A
depth-first implementation uses polynomial working space, retaining only
polynomial-size arithmetic state and the factor stack. No exponential lists
are needed.

This validates the proposed improvement from the OLD W004 **reference upper
envelope** O(N_0^(3/2) poly(log N_0)). It is not a matching lower bound for
either wrapper or a measured ratio of their actual expected times. Complete
trial division already has the new conservative envelope deterministically;
no improved established factoring bound follows. The literal computation saved
is the construction, sorting and merging of two N-record lists, and their
O(N n) working bits, on each unit trial reaching setup. The replacement has
polynomial capped work while preserving exactly the required hidden-root law.
It creates a cheaper field/packet input stream, not a useful mixed packet.

## 8. Authorized finite screen: every outcome and its limits

[Machine-readable summary](W005-blindnorm-review-evidence/screen/summary.json)
and [stdout](W005-blindnorm-review-evidence/screen-stdout.jsonl) retain every case.
Each per-case JSON stores roots, exhaustive φ, gcd class/factor counts, exact
root-conditioned Counters and hashes, exhaustive norm support, controls,
processed/expected pairs, elapsed time, traced peak and stop reason.

All cases completed before the 0.96-second work deadline and the one-second
case cap. Recorded case time including serialization, in the frozen order:
0.034651, 0.033042, 0.122784, 0.102846, 0.130326, 0.132632, 0.179785,
0.189919 seconds. Whole-screen recorded time was 0.960133 seconds. No case was
restarted or added. Peak traced allocation was 259,914 bytes; this is Python
traced allocation, not a process RSS measurement. Per-case evidence was at most
10,641 bytes, and all eight case JSONs total 67,636 bytes. Summary, logs, source,
protocol and other review evidence also fit the 16 MiB overall allowance.

For each N below, both R=1 and R=4 had the same gcd counts and support sizes;
their actual roots and distinct output Counters are preserved separately:

- N=49: 2,401/2,401 pairs; 2,352 unit, 0 proper, 49 full gcd; 56 norm
  outputs per root, all with multiplicity 42=φ(N). Affine control has 49
  outputs per root, multiplicity one, all 49 parameters unit.
- N=77: 5,929/5,929 pairs; 5,760 unit, 168 proper, 1 full gcd; 96 norm
  outputs per root, multiplicity 60. Proper factors are 7 (120 pairs) and
  11 (48 pairs). Affine control has 77 unit parameters and 77 outputs per root.
- N=91: 8,281/8,281 pairs; 6,912 unit, 1,344 proper, 25 full gcd; 96 norm
  outputs per root, multiplicity 72. Proper factors are 7 (144 pairs) and
  13 (1,200 pairs). Affine control has 77 unit parameters/outputs per root,
  14 proper-gcd parameters returning 13, and no full gcd.
- N=121: 14,641/14,641 pairs; 14,520 unit, 0 proper, 121 full gcd; 132
  norm outputs per root, multiplicity 110. Affine control has 121 unit
  parameters and 121 outputs per root.

Every full-sampler root-conditioned Counter was identical within its case,
every support equalled the independently enumerated norm set, and every
supported multiplicity equalled the independently gcd-counted φ(N). All proper
factors verified, and no invalid certificate was produced. There were no
invariant rejections, timeouts, memory/evidence exhaustions, unstarted cases or
evaluator errors. Stderr is empty. Hash/serialization checks of all saved
Counters and case files passed in
[evidence-verification.json](W005-blindnorm-review-evidence/evidence-verification.json);
that check did not rerun the mathematics.

Passing (x,2x) unchanged failed root-choice independence in all eight cases.
The separately enumerated affine a=1 control also failed independence, full
support and equality of its conditional law to the full sampler in every case.
Those are observed control outcomes, not eight additional rejections of the
proposed sampler. Symbolically, its image is exactly the chart where 1+c is
a unit, with inverse b=e/(1+c); it contains rotation 1 and omits −1. Thus
opposite roots already distinguish it. Adding just one global point at infinity
would still omit mixed local charts over general composite N.

This screen checks the listed finite maps and controls only. It does not
enumerate raw-bit tapes, the B-attempt stopping law, arbitrary prime powers,
field packets, useful-root frequency, recursion or bit complexity. Those claims
stand on the symbolic arguments above and remain subject to parent disposition.
The required [repository check log](W005-blindnorm-review-evidence/repository-check.log)
records exit 0, 12 passing Python tests, source-screen success, seven Lean build
jobs and the existing Audit.lean assumptions. No new Lean theorem was proved.

## 9. Prior art and recommendation to the parent

The map ξ/conjugate(ξ) is the familiar quadratic Hilbert-90 form; norm-one
conic arithmetic and rational parametrization are established constructions.
A successful inspected primary document, Marc Joye's
[WO2010145983A1 description](https://patents.google.com/patent/WO2010145983A1),
already discusses norm-one/Pell-conic groups over N=pq, projective coordinates,
affine-chart exclusions at mixed CRT points, and a Delta=−1 specialization.
Its inspected scope does not prove this exact homogeneous-pair probability law
for arbitrary repeated powers or the stopped W004 interface. This comparison
concerns mathematical prior art, with no legal conclusion.

The root-to-factor reduction and its hidden-choice argument appear explicitly
in [Shoup §12.5.3, pp.352–353](https://www.shoup.net/ntb/ntb-v2_5.pdf).
The displayed example uses a total deterministic square-root subroutine for a
semiprime. Sections 3–6 here independently justify its extension to random
auxiliary certificates, failures and arbitrary odd prime powers; the source
is not treated as a theorem about the new tape boundary.

The eight-query search also identified Rubin–Silverberg's torus papers and
Williams's p+1 paper, but the five attempted primary PDF endpoints for these
works failed; two bounded transport fallbacks also failed. Their full relevant
proofs remain **UNKNOWN/uninspected** in this review. Exact failures and read
scopes are recorded, and the failed TR85-001/Wiley/AEM loop was not repeated.
No exact-priority or novelty conclusion follows from this bounded search.

Recommend acceptance of the finite-ring equal-fiber theorem, capped conditional
uniformity, inner-transcript independence, pointwise W004 extraction transfer,
the redefined raw outer success identity, polynomial trial cost and conservative
complete expected reference bound. Required statement completions are the
explicit s and C_B/F_B/E_B factors; fresh independent tapes and the strict input
boundary; and distinguishing near-one terminal mass from certificate mass.
Do not generalize to arbitrary tape-dependent acceptance, adopt the affine-only
control, or reuse the old deterministic field law.

The sampler's acquisition gap is resolved for this joint wrapper. The remaining
research obligation is a paid useful-packet/root-supply bound under its actual
uniform-certificate law, or a different direct factor mechanism. This review
selects no further experiment. A completed finite screen cannot supply that
missing probability or an improved state-of-the-art factoring complexity.
