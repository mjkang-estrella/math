# W030 review: unbalanced conditional costs and public scaled cover

**Disposition: accept the parent's conditional cost envelope and the scaled covering construction, with the explicit interface and schedule completions below.** Public rescaling balances the coordinate counts but increases the root width enough to leave the optimized cost at `O~((N/P)^(1/3))`. Combining it with the paid small-factor branch retains the displayed worst exponent **1/5**, although the balanced branch has exponent **1/6**. These are optimized upper envelopes of the specified constructions, not lower bounds on factoring, root representations, or possible consumers. **No fast aggregate consumer is supplied. Verified complete factoring improvement: NONE.**

The full object of review is the frozen [parent derivation](W030-unbalanced-frontier-review-evidence/inputs/research/findings/W030-unbalanced-cost-frontier.md), SHA-256 `a04b1ea446f631d84652604ebbe767a2e4b9e715e8561fc3a78360052ccf3cae`. The [brief](W030-unbalanced-frontier-review-evidence/brief.txt), [input manifest](W030-unbalanced-frontier-review-evidence/input-manifest.json), and [read scope](W030-unbalanced-frontier-review-evidence/method-and-read-scope.json) fix the review boundary. Root acquisition, the uncarried representation, and its localization interface are imported from the frozen W030 root disposition and root audit. The digit-cut recursion and kernel literature are outside this review and remain assigned to the live separate task. No numerical experiment or prior-art search was needed.

## 1. Precisely what is conditional

Let `n=bitlen(N)`, let `p` be a prime divisor with `p<=sqrt(N)`, and put `q=N/p`; **q may be composite**. The public algorithm receives N only. A range `[P,2P]` is an enumerated public candidate range, not advice containing p. Throughout, `1<=P<=sqrt(N)`. Write `D=N/P`; on a covered range, `q<=D<=2q`.

The granted hypothesis is a **uniform, exact, complete supplied-table consumer** with cost

    O~(U_c + V_c + sqrt(U_c*V_c*T)),

where `U_c,V_c` count supplied coordinate occurrences, not the largest numerical row or column label. It must include exponent setup, its workspace/traffic, product computation, paid product-preserving restrictions, nonunit localization, decoding, and the stipulated extraction/success overhead. It must accept the actual row/column labels and the signed padded carries. Dependence on the public base and precisions must be polynomial in n. This assumption is not proved by the root audit or by this report.

For the scaled construction the rows have labels `s,2s,...,sA`, then their primitive-stratum variants. A consumer promised only for consecutive unweighted rows of a synthetic input `Ns` is **not** automatically this consumer. Charging by a maximum row label would reintroduce `sA`; replacing the column label `Nb` by `Nsb` would break the exponent identity. The parent's conditional transfer is valid under the stated supplied-list/actual-label interpretation. Whether a future concrete kernel supports that interface is still its own obligation.

Here `O~` suppresses fixed powers of log N, including the paid public prime/range schedules, Hensel precision, bucket labels, arithmetic widths, and localization depth. It does not suppress a power of s, M, or a coordinate count. With the imported W020 extractor, a resulting full splitter is an **expected Las Vegas** composition (expected at most two trials after preprocessing), not an unconditional deterministic time theorem. No actual new splitter or exponent improvement is established.

## 2. The original cost and its legal domain

Ignore constant and polynomial logarithmic factors only for this optimization. Put `a0=sqrt(N)/P>=1`. The original parameters are

    U ~ a0*sqrt(M),      V ~ sqrt(M)/a0,      UV ~ M,
    W ~ sqrt(N*M),       T = O~(1 + sqrt(N)/M^(3/2)).

The supplied-table envelope is therefore

    F(M) = a0*sqrt(M) + sqrt(M) + N^(1/4)*M^(-1/4).

The first term dominates the second. Balancing the increasing and decreasing terms gives the scale

    M0 = P^(4/3)*N^(-1/3),
    F(M0) ~ (N/P)^(1/3),
    V0 = P^(5/3)*N^(-2/3).

This is the minimizer up to constant factors; differentiating the literal two-term sum changes only its constant multiplier. The real interior condition `V0>=1` is equivalent to `P^5>=N^2`, or `P>=N^(2/5)`. At equality, the formal `U=M,V=1` is illegal. Both coordinates of an admissible W022 rectangle are strictly below M, hence V is at least 2.

The parent's boundary repair `U=floor(M/2), V=ceil(M/U)` works for **M>=5** (odd M here), with U and V strictly below M. At M=3, take U=V=2. At the transition, the repaired W, coordinate sum, and consumer bound differ only by constants. This is not an appeal to a unit-only or modulus-one branch.

There is also a uniform recipe covering every rounded interior target. For each scheduled odd prime ell, take the least positive power `M=ell^k` such that

    N*M^3 >= P^4.                    [M >= M0]

Use

    Uhat = least integer h>=0 with P^2*h^2 >= M*N,
    U = min(M-1, max(2,Uhat)),
    V = ceil(M/U),
    W = 2*P*U + ceil(N*V/P).

Since `P^5>=N^2`, one has `M>=M0>=N/P^2`. Consequently the ideal U is at most M, the ideal V is at least 1, and this clamping changes each by at most an absolute factor. In particular

    U ~ sqrt(M*N)/P,   V ~ P*sqrt(M/N),   W = O(sqrt(M*N)).

Thus rebuilding the rectangle retains the **tight range-dependent width**, not merely the much larger generic fallback `N(U+V)`. The construction is legal for every M>=3, including k=1. Also `M0<=M<=ell*M0` in this branch, so rounding costs at most a polynomial logarithmic factor. All comparisons can be performed on integers; no floating-point threshold decision is required.

For orientation only, below the interior threshold the constrained original rectangle has scale `M>=N/P^2`. Optimizing the same envelope over that constrained scale gives `O~(N/P^2 + sqrt(P))`, not the unjustified continuation of the interior optimum. The scaled construction below extends the `(N/P)^(1/3)` envelope into this smaller-P region. The small-factor comparator is already cheaper there, so this domain extension does not improve the displayed combined frontier.

## 3. The scaled cover is valid, including the nonunit strata

Fix a scheduled ell with `gcd(ell,N)=1`. Define the public integer

    s0 = ceil(N/P^2),
    s = s0 if ell does not divide s0, otherwise s0+1.

Since ell is prime, the alternative is an ell-unit. With `N/P^2>=1`,

    N/P^2 <= s <= N/P^2+2 <= 3N/P^2.

Thus the adjustment has constant relative cost. Do not discard a scheduled prime dividing s0: change s on that prime. Computing `gcd(s,N)` is optional; return it only if proper. No assumption `gcd(s,N)=1` is needed. The modulus for root construction is an ell-power, where s, p, and q are all units.

Choose any `2<=A<M`, `B=ceil(M/A)<M`. For a completely public balanced choice, use

    A = ceil(sqrt(M)),   B = ceil(M/A).

For every integer M>=3 these are legal, are `Theta(sqrt(M))`, and satisfy `M<=AB<M+A<2M`.

**Sorted-residue argument.** Set `z=sp/q mod M` for proof only. The residues `jz`, `0<=j<=A`, are distinct because z is a unit and A<M. Among their increasing representatives in `[0,M-1]` there is a positive consecutive gap

    1<=d<=floor((M-1)/A)<=B.

Let h be the signed difference of the original indices corresponding to that ordered gap. Then `hz=d mod M`, `0<|h|<=A`. Taking `a=|h|` and `b=sign(h)*d` gives

    1<=a<=A,   1<=|b|<=B,   M | s*a*p-b*q.

The hidden ratio is used only in the existence proof. The public construction enumerates coordinate lists from N, P, ell, and M; it never sorts hidden-ratio residues. Negative b is essential. Also, `u=s*a` may exceed M: the proof is in the **a,b rectangle**, so this is a new covering argument, not a literal application of W022 with a now-illegal bound on u.

For the covered pair put `S=s*a*p+b*q`. Then exactly over the integers,

    S^2 - 4*N*s*a*b = (s*a*p-b*q)^2,
    E = s*a+N*b-S = (p-1)*(b*q-s*a).

Hence `S^2=4Nsab mod M^2`. The first identity uses radicand Ns; the second still uses the original input N in `Nb`. Neither identity needs q prime. Primality of p is used later for Fermat's theorem modulo p.

For valuation stripping, let `r=ell^j`. Since a,b are nonzero and have magnitude below M, their valuations are below k. The congruence, and the units sp,q, force the two valuations to coincide. Divide **a and b**, equivalently both actual weights sa and b, by r. Enumerate

    0<=j<=floor(log_ell(min(A,B)))<=k-1,
    m_j=M/r,  Q_j=m_j^2,  L_j=2(k-j),
    A_j=floor(A/r),  B_j=floor(B/r),  W_j=ceil(W/r),
    1<=a'<=A_j,  1<=|b'|<=B_j,  ell does not divide a'b'.

The primitive witness satisfies `m_j | s*a'*p-b'*q`, has `S_j=s*a'*p+b'*q`, and obeys both displayed identities with a',b',S_j. The auxiliary modulus never becomes 1; `L_j>=2`. The divided a',b' remain below m_j, although s*a' need not. Every positive-valuation witness is retained, and strata retain distinct occurrence tags.

## 4. Transfer of the root interface and the filter

The imported W030 table algebra applies to the actual primitive row weight `w=s*a'` and column weight b'. Equivalently, with the usual nonsquare delta and matching square class epsilon, lift one root per listed coordinate:

    X_(a')^2 = 4*N*s*delta^epsilon*a'   mod Q_j,
    Y_(b')^2 = delta^(-epsilon)*b'     mod Q_j.

Class membership uses `chi(N*s*a')=chi(b')=(-1)^epsilon`. Because `ell` divides none of N,s,a',b', the roots are units; both pair signs exhaust the rooted pairs. The imported small square table, digit Hensel lifting, and uncarried convolution therefore have the same construction cost per **entry**. No square root modulo N, factor of s, or explicit pair array is acquired.

With low root digits x,y, the row weight and column weight have residues

    s*a' = (4*N*delta^epsilon)^(-1)*x^2   mod ell,
    b'   = delta^epsilon*y^2             mod ell.

Thus the constant exponent residue on a class/digit/sign block is

    e = (4*N*delta^epsilon)^(-1)*x^2
        + N*delta^epsilon*y^2 - sigma*x*y    mod ell.

This is the original filter formula applied to the actual weight. In particular, the inverse in the row-label term is **not** `(4Ns delta^epsilon)^(-1)` without the compensating s. Keep exactly the nonzero-residue blocks. The carry term is divisible by ell, so every retained padded exponent is a nonzero integer.

For the primitive true leaf the covering congruence gives `b'q=s*a'p mod ell`, whence

    E_j = (p-1)*(b'q-s*a')
        = s*a'*(p-1)^2 mod ell.

The leaf survives precisely when `p!=1 mod ell`. Changing s per base leaves this criterion unchanged. This includes `p=-1 mod ell`, and does not infer witness retention merely from the survival of some sign. Use the divided row weight s*a', not the unstripped sa.

Use the imported common signed carry interval

    c_j=L_j*(ell-1),
    H_j=ceil(W_j/Q_j)+c_j,   -H_j<=tau<=H_j,
    T_j=2H_j+1,
    E_j(a',b',sigma,tau)=s*a'+N*b'-sigma*R_j(a',b')-Q_j*tau.

Freeze s, roots, lists, blocks, signs, bounds, and tags before evaluation. Restrictions partition that frozen family without reacquiring another s or representation. Empty products are 1; signed columns and singleton lists are supported. All low-digit blocks use shared coordinate references as in the root audit. No digit-cut consumer claim is used here.

## 5. Tight widths, strata, and scaled cost

For `p in [P,2P]`, `q<=N/P=D` and `sp<=6D`. A valid public integer width is

    W = 2*P*s*A + ceil(N*B/P) <= 6D*A + D*B + 1
      = O(D*sqrt(M)).

The integers in this bound are computed directly. There is no scan of an interval of length s, W, or Q to construct it. For this schedule s and every other integer are polynomially bounded in N, up to polynomial logarithmic factors. In particular the bound for every represented exponent is

    |E_j| <= s*A_j + N*B_j + W_j + (2c_j+1)*Q_j.

Thus their bit lengths, and the root radicands' bit lengths, are O(log N). Large row-label values add arithmetic bit cost, not s times as many entries.

The carry and signed pair-count bounds, writing `r=ell^j`, are

    T_j = O(1 + ell*k + W*r/M^2),
    A_j*B_j <= AB/r^2 = O(M/r^2).

The ceiling error in W_j is harmless because `r<M`; it adds at most a constant to T_j. Therefore

    sum_j (A_j+2B_j) = O(A+B),
    sum_j sqrt(A_j*B_j*T_j)
      = O(sqrt((1+ell*k)*M) + sqrt(W/M)).

The two sums use geometric ratios `ell^(-1)` and `ell^(-1/2)`, uniformly bounded for ell>=3. There is no factor equal to the numerical size of a deepest carry interval left outside this sum. Splitting into the O(ell^2) low-digit/sign blocks changes these estimates by at most polynomial logarithmic factors, with the block calls and repeated bucket references charged. Table acquisition additionally pays O(k*ell^2) labels and the accepted per-entry digit/root work.

Granting the specified consumer, the total local envelope, including acquisition and all strata, is consequently

    O~(1 + sqrt(M) + D^(1/2)*M^(-1/4)).

Balance at `M_s=D^(2/3)`, obtaining `O~(D^(1/3))`. Implement the target by choosing the least positive ell-power satisfying

    P^2*M^3 >= N^2.

Then `M_s<=M<=ell*M_s`, including the case `M_s<ell`, where k=1. The balanced A,B recipe works even at M=3 and retains the same tight W. Increasing M by a factor f increases the table term by sqrt(f) and decreases the width term by f^(-1/4); with f<=ell the advertised exponent is unchanged. No large base is dropped, and no unjustified small-target width fallback is used.

At `P=N^(2/5)`, the scaled optimum has `M=N^(2/5)`, `A,B~N^(1/5)`, and `W~N^(4/5)~M^2`. The unscaled optimum has `M=N^(1/5)` and a row table of that scale. Both cost N^(1/5). At the balanced endpoint `P~sqrt(N)`, both give `M~N^(1/3)` and cost N^(1/6). These are formal scale identities, not evidence of actual factor distributions or running times.

## 6. Complete public schedules and the matched small-factor branch

Handle even inputs and exact perfect powers by the imported polynomial-bit preprocessing; the latter returns a proper base. One explicit finite-input convention is trial division through 4 when N<=16. Remaining inputs have at least two distinct prime factors. No primality/termination contract on prime inputs is asserted.

**Prime schedule.** Import W024's explicit schedule: sieve odd primes until their product exceeds N, testing `gcd(ell,N)` first and returning any proper factor. The accepted bound uses at most n primes, each at most `16(n+1)^2`. On the no-factor path all scheduled bases are legal. Some base has `p!=1 mod ell`, since otherwise their product would divide p-1<N. For each range, the adjustment of s makes it a unit at **every** base, preserving this argument. Process all scheduled bases needed for coverage; no hidden choice of a good base is allowed.

**Small-factor comparator, constructed on equal input.** For a public bound B<N, the ordinary block-product procedure either returns a factor of N or certifies that no integer from 2 through B shares a prime factor with N. Set `h=ceil(sqrt(B))`, construct the monic polynomial

    F(X)=product_(i=1..h)(X+i) mod N,

and evaluate it at `0,h,2h,...,(m-1)h`, where `m=floor(B/h)`. These are disjoint complete blocks up to mh. Inspect gcds of the m values; handle the fewer than h remaining integers directly. A proper block gcd finishes. If a block gcd is N, scan that one block's at most h integers: at least one has a nontrivial gcd, and each integer is <N, so its nontrivial gcd is proper. Do not pad the last block with N or larger integers and silently assume such a leaf is proper.

Using the same standard fast monic product/remainder-tree arithmetic as the accepted comparators, construction and evaluation cost `O~(h+B/h)` ring operations on O(log N)-bit residues. Monic division requires no inversion of a nonunit of `Z/NZ`. All gcds, the terminal scan, and data acquisition fit `O~(sqrt(B))` bit cost with polynomial logarithmic factors. Thus B=2P gives the displayed **deterministic** `O~(sqrt(P))` comparator when the range lies below the final sqrt(N) endpoint and N>16; `2P<=2sqrt(N)<N`. This is a constructive matched upper bound, not a novelty assertion or a comparison against toy trial division.

**Range schedule and threshold.** Enumerate P as successive powers of two with `P^2<=N`. The closed intervals `[P,2P]` cover every smaller prime factor (endpoint duplication is harmless). When `P^5<=N^2`, run the small-factor procedure through 2P. When `P^5>N^2`, use the rounded unscaled construction, or the scaled one, at every scheduled base. These decisions use N and P only. In particular, a range straddling `N^(2/5)` belongs to the small-factor branch and is fully covered; there is no interval gap at the threshold. At most O(n) ranges are processed.

On the unresolved path, freeze the complete family for the remaining ranges/bases/strata. Use W020's original uniform alpha in `{1,...,N-1}`, including its initial gcd, signed unit powering, and full two-adic recovery. A trial is this complete covering schedule, with early stops on factors or localized full collisions as permitted by W020; it is not one possibly uncovered range. All preprocessing is paid, all restricted evaluations are within the hypothetical cost contract, and fresh independent trials have expected count at most two. Processing a product for one bad base and resampling before the covering schedule completes would not justify this bound.

The displayed per-range envelope is

    C(P) = O~(sqrt(P))       for P<=N^(2/5),
    C(P) = O~((N/P)^(1/3))  for P>=N^(2/5).

For `P=N^x`, `0<=x<=1/2`, its power is `min(x/2,(1-x)/3)`. The intersection is x=2/5 and its maximum is 1/5. Summing O(n) ranges and at most n bases, paying their setup, and applying the imported expected-trial bound preserves `N^(1/5)*poly(log N)` **conditionally**. No uniform prime-distribution assertion is needed to maximize this formal envelope. The full schedule is public; the algorithm is not given the actual p or permission to run only its range.

## 7. Accepted result and the remaining obligation

The scaled cover is a valid coordinate change with a new proof in a,b. It changes table geometry and extends the legal `(N/P)^(1/3)` branch below the unscaled interior threshold. It does **not** improve the all-input envelope after the standard small-factor branch is included. The compensating term is the larger width `W=O((N/P)*sqrt(M))`, giving `D^(1/2)*M^(-1/4)` in the consumer cost. There is no further uncovered power term from valuation strata, prime scheduling, rounding, small targets, unit checks, composite q, or label widths under the completed interfaces above.

This conclusion is limited in two ways. First, optimizing a conservative width/cost upper envelope cannot prove that every other cover or evaluator must pay it. Second, a fast consumer for the required supplied lists, labels, and frozen restrictions still does not exist in the reviewed work. Repeating a root identity, assuming the desired evaluator as an oracle, or using only its balanced-factor target does not close that gap.

A result that changes the displayed frontier would need a paid construction that reduces the long-table burden or this transition-range width, improves the small-factor branch in the matched model, or uses another mechanism outside this composition. Establishing the currently granted consumer would make this conditional bookkeeping algorithmic, but by itself would still leave this composition's all-input envelope at one fifth. No experiment was indicated by an unresolved identity, so no certificate, sweep, solver run, or Lean check was performed.

Only this report and its assigned evidence directory were written. No recursive delegation, installation, commit, shared solver/Lean/STATE/task edit, kernel literature duplication, or novelty claim occurred. The [verification record](W030-unbalanced-frontier-review-evidence/verification.json) distinguishes frozen-input integrity from concurrent source drift. The [delivery manifest](W030-unbalanced-frontier-review-evidence/delivery-manifest.json) hashes the complete report and every retained payload except itself; its external SHA-256 is supplied at handoff.
