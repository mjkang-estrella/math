# W007 — independent Fourier envelope and restart-cost audit

2026-10-08. **Disposition: ACCEPT within the specified implementation and
depth range.** Equations (1)–(6) in the frozen parent note are correct. The
early-stopping argument can be completed with a uniform explicit constant:
for distinct odd primes p<q, k>=2, t>=1, 2^k<=sqrt(p), and the stated
A<=1/4, B<=1/8,

    E[total modular multiplications until a proper factor] >= p/(40k).

Here the trial uses the explicit triangular coefficient acquisition, fixed
depth-k chain probes, and independent restarts with the same k,t. It ends
early only on a proper factor. The inequality counts multiplications actually
performed before success, including acquisition and failed trials. It does
not assume that trial cost and success are independent. A sufficient uniform
size condition for A<=1/4 and B<=1/8 is p>=1024.

This is a scoped rejection of the proposed random-training tower as a way to
match the paid sqrt(p)*poly(log N) control **in this depth range and evaluator**.
Verified new factoring improvement: **NONE**. No adaptive-depth, later-depth,
general-circuit, or general factoring lower bound is established. The
component factorization, irreducibility, and fixed-depth geometric mean were
not audited here.

The primary source was independently opened and its theorem statement checked:
[Kowalski, *Exponential sums over finite fields: elementary methods*,
Theorem 3.2, printed p.31](https://people.math.ethz.ch/~kowalski/exponential-sums-elementary.pdf#page=33),
version September 14, 2021. Its hypotheses are a nontrivial additive character,
polynomial degree d<q, and gcd(d,q)=1, and its bound is (d-1)sqrt(q).
The proof of Weil's theorem itself is imported, not independently reconstructed.
The remaining calculations and probability argument below are this audit's
derivations.

**Normalization and the conditional estimate.** Fix the current polynomial f
over F_p, put n(y)=#{x:f(x)=y}, and let C=sum n(y)^2. In this report T and D
include the zero value:

    T = sum_(y,w) n(y)n(w)n(y+w),
    D = sum_y n(2y)n(y)^2.

In particular D here is not the zero-deleted residual D in the prior review.
The next parameter a=f(r) has probability n(a)/p. For h_a(y)=y(y-a),

    h_a(y)-h_a(w) = (y-w)(y+w-a).

Counting ordered pairs and subtracting the intersection y=w=a/2 gives

    C_next(a) = C + sum_y n(y)n(a-y) - n(a/2)^2.
    E[C_next-C | f] = (T-D)/p.
    E[C_next/p-C/p | f] = (T-D)/p^2.                 [accepted (1)]

The half argument and its one-point intersection use odd characteristic.
There is no extra factor 1/2: C counts ordered pairs. The identity includes
a=0, repeated fibers, and all zero-atom contributions without exceptions.
Also D>=0 (and T-D>=0, since D is the y=w part of T).

Take S(t)=sum_y n(y) exp(2*pi*i*t*y/p). Character orthogonality applied to
y+w-u=0 gives

    T = (1/p) sum_t S(t)^2 S(-t)
      = (1/p) sum_t |S(t)|^2 S(t).

The conjugation is correct because n is real and S(-t)=conj(S(t)). Although
an individual summand need not be real, the terms at t and -t are conjugates;
their total is real. Using the opposite Fourier sign would give the conjugate
sum and the same answer. S(0)=p and Parseval gives

    T/p^2 = 1 + p^(-3) sum_(t!=0) |S(t)|^2 S(t),
    sum_t |S(t)|^2 = p*C,
    sum_(t!=0) |S(t)|^2 = p*C-p^2.

C>=p follows from Cauchy–Schwarz and sum n=p. Therefore

    |T/p^2-1|
       <= p^(-3) max_(t!=0)|S(t)| * (p*C-p^2)
       <= (d-1)/sqrt(p) * (C/p-1).                 [accepted (2)]

For every realized training history, P_i is monic of exact formal degree
2^i: both P_i and P_i-a_i are monic with that degree. This remains true for
zero parameters and repeated polynomial roots. Apply the cited theorem with
field size q=p and character y |-> exp(2*pi*i*t*y/p), t!=0. For 2^i<p its
hypotheses hold; p is odd and hence coprime to 2^i. There is no genericity,
squarefreeness, critical-value, or component-irreducibility assumption. For
i=0 the nontrivial sums vanish exactly and the degree-one bound is valid.
Weil is applied only in this eligible range, not to an arbitrary high-degree
representation of the same field function.

**Iteration and root count.** All expectations here are over the UNSTOPPED
independent uniform training tape, with no survival conditioning. Define

    U_i = E[C_(P_i)/p]-1 >= 0,
    delta_i = (2^i-1)/sqrt(p),
    A_i = sum_(h=0)^(i-1) delta_h = (2^i-1-i)/sqrt(p).

Dropping D and applying the uniform conditional estimate yields

    U_(i+1) <= (1+delta_i)*U_i+1,   U_0=0.

Unrolling, with empty products equal to one, yields for i>=1

    U_i <= sum_(r=0)^(i-1) product_(h=r+1)^(i-1) (1+delta_h)
        <= i*exp(A_i).                              [accepted (3)]

This uses 1+x<=exp(x) for x>=0. To obtain U_i, the Weil applications only
need 2^h<p for h<i; the parent's stated 2^i<p condition is sufficient.
No independence between the current C and its history is needed because
delta_i is deterministic and the estimate holds conditionally on each f.

Let m_i=n_(P_i)(0). Absorbing the a fiber adds n(a) roots when a!=0 and
adds none when a=0. Thus, exactly,

    E[m_(i+1)-m_i | P_i]
        = (1/p) sum_(a!=0) n(a)^2
        = C_(P_i)/p-m_i^2/p.

Starting from m_0=1 and dropping the last nonnegative term gives

    E[m_k] <= 1+k+sum_(i=0)^(k-1) i*exp(A_i)
           <= 1+k+[k*(k-1)/2]*exp(A_(k-1)).          [accepted (4)]

A_i is nondecreasing. For j>=1 with 2^j<=sqrt(p),

    0 <= A_(j-1) = (2^(j-1)-j)/sqrt(p) <= 1/2.

The elementary series comparison exp(1/2)<sum_(n>=0) (1/2)^n=2 then gives
E[m_j]<=1+j+j(j-1)=j^2+1. At j=0 the assertion is equality. Hence

    E[m_j] <= j^2+1 for every 0<=j<=k,
    provided 2^k<=sqrt(p).                          [accepted (5)]

This is an expectation, not a bound on every realized root count. Keeping
exp(A_i) constant at later, unrestricted depths is invalid. In particular
there is no optimization over polynomial-sized k under this logarithmic
depth restriction.

**Exactly which factor checks are covered.** Presample independent uniform
r_0,...,r_(k-1),x_1,...,x_t modulo N, and construct the full training tower
even on tapes where a stopped execution would already have returned a factor.
This is a mathematical coupling, not additional work charged to the algorithm.
The stopped execution agrees with this tape until its first proper factor.

Evaluation of P_d(u) uses y_0=u and

    y_(ell+1)=y_ell*(y_ell-a_ell),  0<=ell<d.

The permitted checks in this audit are gcds with N of y_ell,
y_ell-a_ell, their computed products, and the endpoint y_d. Either
multiplicand vanishing modulo a prime forces y_(ell+1) to vanish, and every
later y persists at zero at that prime. Therefore any proper factor from
these checks implies y_d=0 at p or q. Stored factors of a full-gcd product
are among these same values; inspecting them recovers masked successes but
does not escape the endpoint-zero implication. Rechecking a previously
acquired coefficient cannot create an uncharged new channel: it was an earlier
training endpoint.

For training stage j, set d=j and u=r_j; a_j=P_j(r_j). A check at j=0
is simply gcd(r_0,N). For a probe, set d=k and u=x_h. The list does not
authorize gcds of arbitrary differences between samples or coefficients,
derivatives, discriminants, new shifted endpoints, or other extra expressions.
Such checks would require a different analysis. The newly planted expression
P_j(r_j)-a_j is identically zero modulo N and itself gives no proper factor.

Let E_tr be the union of the events that a presampled training endpoint
P_j(r_j), 0<=j<k, vanishes at either prime. Let E_h add the corresponding
endpoint-zero events for the first h presampled depth-k probes. These events
include all actual proper-factor successes in their respective prefixes,
and may also include full-gcd endpoints with no successful intermediate.

For either prime ell, r_j is independent of P_j, and x_h is independent of
the whole training tower. Consequently

    Pr[P_j(r_j)=0 mod ell] = E[m_(j,ell)]/ell,
    Pr[P_k(x_h)=0 mod ell] = E[m_(k,ell)]/ell.

The smaller-prime condition implies the same depth condition at q. With
eta=1/p+1/q, define a(k)=sum_(j=0)^(k-1) (j^2+1) and b(k)=k^2+1. Then

    A = eta*a(k) = eta*[k+k*(k-1)*(2k-1)/6],
    B = eta*b(k),
    Pr(E_tr) <= A,
    Pr(E_h) <= A+B*h.                               [stronger form of (6)]

These are ordinary union bounds on the full tape. They imply the parent's
proper-factor bounds, including both CRT orientations and all the stated
pre-multiplication checks. Independence between different endpoint events
is unnecessary. The unstopped CRT tapes are indeed independent, but even
that joint-history fact is unnecessary here: their marginal uniform laws
suffice. No survival-conditional root law or independent hazard is asserted.

**Early stopping and all probe budgets.** Let W be the number of actual
multiplications in one stopped trial, and s its success probability. Write
L=k(k-1)/2 and h0=floor(1/(4B)). Since B<=1/8, x=1/(4B)>=2 and

    h0 >= x-1 >= x/2 = 1/(8B).

On E_tr's complement, the trial has no training success and completes all
L triangular multiplications. For h<=min(t,h0), E_h's complement has
probability at least 1-A-Bh>=1/2. On that event the execution reaches and
completes the h-th probe's k multiplications. Summing these indicators,

    E[W] >= (1-A)*L + (k/2)*min(t,h0)
         >= (3/4)*L + (k/2)*min(t,h0).              [actual-work bound]

This proves the parent's cost conclusion. Using the stronger endpoint-zero
events makes the completion justification explicit: their complements contain
neither a successful gcd nor any full/partial zero in these evaluations.
Thus even omitting the remainder of a chain once its modular value is known
to be zero does not undermine this lower bound. Other arithmetic shortcuts
or shared evaluation algorithms are outside the specified explicit chain.
Under that chain, the parent's simpler argument from no proper success also
works because failed trials complete their fixed budgets. Ending a trial or
restarting solely on a full gcd would change the premise.

For k>=2, L>=k^2/4, a(k)<=k^3, and b(k)<=5k^2/4.
If t<=h0, the actual-work bound and the prefix success bound give

    E[W] >= (3/16)*(k^2+k*t),
    s <= A+B*t <= (5/4)*eta*k*(k^2+k*t),
    E[W]/s >= 3/(20*eta*k) >= 3*p/(40*k).

If t>h0, count only the first h0 completed-probe events. Since s<=1,

    E[W]/s >= E[W] >= k*h0/2 >= k/(16*B)
             >= 1/(20*eta*k) >= p/(40*k).

The last comparisons use eta<=2/p. These constants are uniform in every
eligible integer k>=2 and t>=1. Floors and the equality t=h0 are covered.
The proof requires no estimate of the probability of success after h0.

For completeness, p>=1024 is a sufficient size condition throughout the
specified depth range. If k<=4, a(k)<=18 and b(k)<=17, so A<=36/1024 and
B<=34/1024. If k>=5, p>=4^k and the sequences a(k)/4^k and b(k)/4^k
are decreasing for k>=2. Hence A<=70/1024 and B<=52/1024, again below
1/4 and 1/8. Their monotonicity follows from the positive polynomials
4a(k)-a(k+1) and 4b(k)-b(k+1); the exact certificate checks them. No
finite-prime search or asymptotic guess supplies this threshold.

**Renewal with correlated cost and success.** Independent restarted trials
with fixed k,t give identically distributed pairs (W_n,I_n), where I_n is
the success indicator. Within each pair these variables can be correlated.
Let J be the first successful trial. Nonnegative summation and independence
of the n-th trial from previous trials give

    E[sum_(n=1)^J W_n]
      = sum_(n>=1) E[W_n * 1_(I_1=...=I_(n-1)=0)]
      = E[W] * sum_(n>=1) (1-s)^(n-1)
      = E[W]/s.

The independence used is between W_n and PREVIOUS outcomes, not between
W_n and I_n. The mandatory first training gcd already succeeds with
probability (p+q-2)/(pq)>0, so s>0, eventual success is almost sure, and the
identity is finite: a trial's multiplication count is bounded by L+kt.
Combined with the two regimes, this proves the displayed p/(40k) lower
bound, including the partially paid successful trial. Gcds, subtractions,
randomness, storage, and bit operations have not been counted as free in a
runtime upper bound; they are simply omitted from a multiplication lower
bound. On balanced semiprimes k=O(log p), this already grows faster than
sqrt(p) times any fixed power of log N. The comparison is to the established
paid batch control in the project, not an imported unconditional theorem
about the practical Pollard-rho walk.

**What changes the gate.** The exact lost assumption is that exponentially
growing formal degree produces exponentially growing expected useful roots
under fresh uniform training. Up to degree sqrt(p), the conditional cubic
Fourier estimate instead supplies a quadratic root envelope and the above
complete restarted cost obstruction. No new evaluation or acquisition
procedure was found or needed for this audit. The substantive addition is
the rigorous stopping/cost theorem with an explicit constant.

For the unchanged tower, the next decisive mathematical question is whether
one can control the history-averaged cubic Fourier sum beyond this range,
including its correlation with C_i, well enough to continue a useful root
envelope; the degree-only maximum of |S_i(t)| no longer keeps A_i bounded
when 2^i/sqrt(p) grows. For a constructive escape, a paid, different parameter
selector must demonstrate a different conditional drift and a proper-factor
law at both primes, or a different computation must change this evaluator's
cost. Neither question is settled by this audit. No candidate run or numerical
follow-up is proposed.

**Frozen evidence and inspected scope.** All writes are confined to this
report and `W007-fourier-envelope-review*` evidence paths. No shared state,
tasks, solver, Lean, dependencies, commits, or publication were changed;
there was no delegation, candidate run, parameter sweep, or finite-prime
enumeration. The previous review was read as historical evidence with its
authoritative disposition's corrections. Its enumeration checker was not run.

- [Input manifest](W007-fourier-envelope-review-evidence/input-manifest.json)
  records byte-for-byte snapshots and SHA-256 hashes of the five required
  guidance files, STATE, both residual review/disposition files, and the parent
  Fourier note. Guidance and both review/disposition files and the Fourier note
  were read in full. STATE was inspected through its current resume section
  (lines 1–145) and its headings/W007 references; the full file was frozen for
  provenance. No live component-factorization source was inspected.
- [Literature manifest](W007-fourier-envelope-review-evidence/literature-manifest.json)
  records the primary PDF's URL, retrieval time, and hash. The title/version and
  Theorem 3.2 on printed p.31 were inspected. The local PDF and extracted page
  preserve the exact source; unrelated theorems on that page are not imported.
- [Exact checker](W007-fourier-envelope-review-evidence/verify_exact.py) and
  [results](W007-fourier-envelope-review-evidence/exact-checks.json) verify 19
  symbolic identities, nonnegative-coefficient certificates, and rational
  comparisons with standard-library exact arithmetic. They do not formalize
  Weil, orthogonality, the probabilistic coupling, or the whole proof.
- [Delivery hashes](W007-fourier-envelope-review-delivery.sha256) cover this
  report and all accompanying evidence, excluding the hash file itself.
- [Verification record](W007-fourier-envelope-review-evidence/verification.json)
  confirms all nine frozen input hashes, the primary PDF hash, and the 19 exact
  checks. At that check only the live STATE file differed from its snapshot;
  the audited mathematical sources were unchanged. This report uses the frozen
  inputs and does not incorporate concurrent STATE changes.

The frozen parent Fourier note has SHA-256
`13d2b3961ba4d8a96eac3252811347c3fe2910c559a5f0c06d14e2aa9150c58e`.
The authoritative residual disposition has SHA-256
`ff85414bc948d2f7b28fdd7195aae10842f6bac2a592aa30c5c42921e780a781`.
The cited primary PDF has SHA-256
`ff30b82d143cedcaf76f1ef2f15a49856c0eabc2c95ba7ac0da2e3e43da9a866`.
