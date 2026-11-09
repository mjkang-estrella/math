# W032 lift-breakpoint sweep: independent symbolic review

**Disposition: ACCEPT the lift law, exact signed carry update, complete breakpoint enumeration, and small-base event compression, conditional on the stated polynomial interfaces. ACCEPT the proposed soft O(R²(log N+R)) primitive bound conditionally on the separate base-acquisition audit and fast finite-width arithmetic. No algebraic change to equations (1)–(4) of the target is required. Make the precision, storage, interval, and success qualifications below explicit. Verified complete factoring improvement: NONE.**

This is an exact compression of one specified N-parameter family. It neither proves that this family contains a proper split nor supplies an independent-uniform-output model. The saved work is a bounded number of attained carry values after paid base acquisition. It can exhaust an entirely unsuccessful family.

The complete target is [the frozen lift-breakpoint note](W032-lift-sweep-review-evidence/inputs/research/findings/W032-lift-breakpoint-sweep.md), SHA-256 `d98f052ff7f572e724b54623d50f5b3ceaa32cbc6a63aa5c9b68981ebb481c28`. The [brief](W032-lift-sweep-review-evidence/brief.txt) and [input manifest](W032-lift-sweep-review-evidence/input-manifest.json) preserve the assignment and 20 complete input files. Initial inspection preceded the freeze; this mathematical review uses the frozen bytes.

## 1. Scope and dependencies

The accepted scalar/carry review and full-lift coordinate review supply the scalar polynomial for every **integer** unit input, including large unwrapped representatives. They also supply its coefficient ring and derivative after normalization. Their prior numerical evidence and full delivery packages are not reaudited here. No current literature, novelty, or matched factoring-baseline claim is made.

The complete displayed modulo-polynomial interface in [W032-exact-carry-quotient.md](W032-lift-sweep-review-evidence/inputs/research/findings/W032-exact-carry-quotient.md) is a **provisional import**. Its coefficient recurrence and general multipoint-evaluation (MPT) complexity remain owned by the separate LIVE task `factoring-w032-carry-quotient-review-r1`. This review checks this consumer's precision, divisions, signs, lift, enumeration, and incremental costs. It does not independently certify that task's general polynomial algorithms, multi-start convolution, implementation, or conclusions. If the interface changes, reassess the affected conclusions here; if only its acquisition cost changes, substitute that cost in section 7.

The accepted period results are background, and the small-tail failure proposal is outside this scope. No period or small-tail guard is needed for the present conditional theorem. The explicit brief supersedes older live-task descriptions in the frozen STATE and parent disposition.

The complete [preregistered sweep protocol](W032-lift-sweep-review-evidence/inputs/research/findings/W032-lift-sweep-protocol.md) is frozen and read for separation of scope. It was not edited. No assay implementation or result was inspected, no candidate was evaluated, and no numerical experiment, parameter sweep, symbolic computation program, or project/Lean check was run. Only file inspection, evidence writing, and integrity operations were executed. No delegation, installation, commit, shared code, STATE, or task-registry edit occurred. Only this report and its assigned evidence directory were written.

## 2. Legal inputs and three distinct precisions

Let N>1 be composite, R>=2, and set

    m=2R+1,  L=2R-2,  M=N^(2R)=N^(L+2),
    D=4^R(2R+1)!,  S=Z[1/D].

Require the checked branch gcd(D,N)=1, equivalent to leastprime(N)>m. All polynomial congruences below are in S or its reduction modulo a power of N. The proof works for general composite N, including prime powers; it does not use a field or a prime-adic valuation for composite N. In particular 12 and 24 are units.

Choose a positive canonical base stencil

    a_i=a0+i,  0<=i<=m,  1<=a0,  a0+m<N,
    gcd(a_i,N)=1 for every i.

Never delete, replace, or wrap a failed point while calling the result the same stencil. A proper initial gcd is an ordinary preprocessing factor; a full gcd is a failed normalization. All checks and failed branches cost work. The checkable denominator condition can use individual gcds with the integers through m or an equivalent paid product/localization procedure; it does not require the unknown least prime. A product gcd equal to N is not itself a proper factor.

For a0=1 the unit and endpoint conditions follow on the composite guarded branch: every integer at most m+1=2R+2 has all its prime factors at most m, and N has at least two prime factors counted with multiplicity, each greater than m. Thus m+1<N. This gives a public base with no unit-search oracle; explicit checks may still be performed and charged as required by the assay. Arbitrary a0 selection and rejected starts are additional work.

Keep these quantities separate:

    V_R(a) in [0,NM),                   full scalar precision N^(2R+1);
    r(a)=[V_R(a)]_M in [0,M),           lower remainder precision N^(2R);
    u(a)=(r(a)-1)/N^2 in [0,N^L),       lower normalized precision N^L.

The exact full quotient U_full(a)=(V_R(a)-1)/N^2 is canonical modulo N^(L+1), not merely N^L. Its reduction modulo N^L is u(a). Accordingly, the target's U congruence modulo N^L is correct, but a canonical-integer equality at that precision must refer to u, not the full quotient.

The provisional lower-polynomial interface is

    r(a)=[P_R(a)]_M,
    P_R(A)=sum_(j=0..R-1) beta_j A^(2j) modulo M,
    beta_j=N^(2j) product_(v=1..j)((2v-1)^2-N^2)
                       /[4^j(2j+1)!] modulo M.

The name beta_j here avoids confusing coefficient residues with the top digits b_i below. In particular r=1 modulo N^2. Division of r-1 by N^2 is exact and loses two powers of N in precision. One must acquire r modulo M before that division; N has no modular inverse. Equivalently, the imported scalar diagonal gives

    u(a)=F(a) modulo N^L,
    F(A)=sum_(k=1..R-1) N^(2k-2)G_k(A^2) in S[A],
    deg F<=2R-2,  F(A)=A^2/24 modulo N^2,
    F'(A)=A/12 modulo N.

The k=R term of the full normalized polynomial has coefficient divisible by N^L and disappears at this lower precision. The full scalar polynomial modulo NM still has degree at most 2R. That higher-precision fact is needed for the original top-digit comparison below; knowing only r does not by itself determine the top digit.

For direct scalar controls, use the accepted pair-powering modulus N^(2R+3), exact A/N^2 division to precision NM, and the checked normalizing inverse. The control must use the actual integer inputs. The canonical-a formulas for individual second or later digits cannot simply be substituted at large a; their range-dependent carry proofs do not extend that way.

## 3. Exact base carry and the shared lift, including R=2

Write the acquired canonical integers as

    r_i=1+N^2 u_i,
    u_i=v_i+H b_i,  H=N^(L-1),
    0<=v_i<H,  0<=b_i<N.

Let lambda_i=(-1)^(m-i) binom(m,i) and Delta^m x=sum_i lambda_i x_i. For the affine stencil, a degree at most 2R-2 polynomial has zero mth difference. Therefore Delta^m r_i is zero modulo M and

    c0=Delta^m r_i/M=Delta^m u_i/N^L

is an ordinary signed integer. The constant 1 disappears since sum_i lambda_i=0. This division is exact even for a negative numerator. Canonical remainders must be acquired first; the polynomial's ordinary difference is zero, whereas its canonical representatives can have a nonzero difference divisible by the modulus.

For the shared parameter 0<=w<N set

    a_i(w)=a_i+12 H w.

Since L>=2, the shift is a multiple of N. Each point remains a unit, and the points remain an unwrapped step-one progression. For every polynomial F over S, binomial expansion gives

    F(a+h)=F(a)+h F'(a)+h^2 E(a,h),  E in S[a,h].

This polynomial identity introduces no additional factorial inverses. With h=12Hw, the quadratic remainder belongs to the ideal (N^(2L-2)), which is contained in (N^L) because L>=2. The derivative error F'(a)-a/12 is divisible by N; multiplying it by h puts it in (N^L). Hence

    F(a_i(w))=F(a_i)+H a_i w modulo N^L.

At the boundary R=2, L=2 and H=N. The quadratic remainder has exactly enough guaranteed precision: (12Nw)^2 is divisible by N^2. Directly from F(a)=a^2/24 modulo N^2,

    ((a+12Nw)^2-a^2)/24=aNw+6N^2 w^2
                           =aNw modulo N^2.

Thus no higher Taylor term survives at the lower normalized precision, even at R=2. This calculation is a formal identity, with no numerical substitution or trial.

There is a unique canonical representative of the resulting residue:

    u_i(w)=v_i+H[b_i+a_i w]_N.                         (A)

It lies in [0,N^L); the v_i block stays fixed, and any wrap in b_i+a_i w subtracts a multiple of N^L. No extra carry crosses from v_i, because 0<=v_i<H.

The materialized inputs satisfy

    0<a_i(w)<N+12N^L<13N^L,

so their bit length is O(R log N). Their normalization is legal at the original scalar precision. Reducing them all the way modulo N discards the lift and changes the consumer. Reduction at a sufficient polynomial precision is valid for the corresponding polynomial evaluation, but must not be confused with replacing the actual progression by unrelated canonical points in a top-digit comparison.

R=1 is outside (A): L=0 would make this proposed shift inappropriate. The separate symbolic boundary needed by the frozen protocol is simpler: P_1=1 modulo N^2, so every lower r_i is 1 and its order-three difference gives c=0. No R=1 sweep or new numerical case is proposed.

## 4. Integer update, strict bound, and top-digit sign

Define the nonnegative integer floors

    q_i(w)=floor((b_i+a_i w)/N).

Because [b_i+a_i w]_N=b_i+a_i w-Nq_i(w), equation (A) gives the exact integer identity

    u_i(w)-u_i=H a_i w-N^L q_i(w).

Taking the signed difference removes the linear term: sum_i lambda_i a_i=0 because m>=2 and a_i is affine in i. Thus

    c(w):=Delta^m u_i(w)/N^L
         =c0-sum_i lambda_i q_i(w).                  (B)

This proves integrality, not just a congruence modulo N. No nonintegral term has been rounded or discarded. Because m is odd, lambda_0=-1 and lambda_m=+1. At a jump of q_i, the update is **subtract lambda_i**. Reversing all weights changes the sign of every carry but preserves its gcd; mixing conventions between c0, updates, and scalar controls is an error.

The positive and negative weight totals are each 2^(m-1)=4^R. Since every u_i(w) is in [0,N^L),

    |Delta^m u_i(w)| <= 4^R(N^L-1),
    |c(w)| <= 4^R(1-N^(-L)) < 4^R.                  (C)

This is the same strict bound obtained from r. It does not rely on small ordinary values of the unwrapped inputs, a small-tail estimate, or equal carry labels.

To compare with the original filter, let V_i(w) be the full canonical scalar, and put d_i(w)=floor(V_i(w)/M). These obey

    V_i(w)=M d_i(w)+r_i(w).

The imported degree-at-most-2R polynomial for V modulo NM has zero mth difference on this actual unwrapped progression. Therefore for some integer t(w),

    Delta^m V_i(w)=NM t(w),
    Delta^m r_i(w)=M c(w),
    Delta^m d_i(w)=N t(w)-c(w),
    Delta^m d_i(w)=-c(w) modulo N.                   (D)

Consequently gcd(Delta^m d_i(w),N)=gcd(c(w),N). If the earlier filter includes the unit multiplier D, that multiplier also leaves the gcd unchanged. Equation (D), with its minus sign, is the correct comparison for a scalar control. It does not assert equality of the two signed integers or identify c with an individual top digit.

## 5. Exact thresholds, ties, and complete interval coverage

For any one index abbreviate a=a_i and b=b_i. Since 0<a<N and 0<=b<N,

    q(0)=0,
    q(w)-q(w-1) in {0,1} for 1<=w<N.

For positive k, q(w)>=k is equivalent to aw+b>=kN. The first integer w satisfying it is exactly

    t_k=ceil((kN-b)/a)=(kN-b+a-1)//a.                (E)

The numerator kN-b is strictly positive; this is an integer ceiling, with no floating point. Equality aw+b=kN triggers the jump at w itself, not at w+1. No event occurs at w=0.

All relevant crossings are included by generating k=1,...,a and retaining precisely 1<=t_k<=N-1. Indeed q(N-1)<=a. More exactly,

    q(N-1)=a-1 if b<a,
            a   if b>=a.                            (F)

Thus only the last generated crossing can be discarded, and it is at N when b<a. At b=a, the k=a crossing is at N-1 and must be retained. The formula covers b=0 and a=1 without a special rounding convention. Successive thresholds for a fixed i are strictly increasing because N/a>1, so a tied threshold contains at most one record for each i.

Let E be the number of retained records and let their distinct thresholds be

    1<=t_1<...<t_K<=N-1,  K<=E.

Use the sentinel endpoints t_0=0 and t_(K+1)=N. The following symbolic loop specifies the whole scan without evaluating individual parameters:

1. Initialize c=c0 and test gcd(c,N) for the interval [0,t_1-1], or [0,N-1] if K=0.
2. At threshold t_j, add the weights of **all** records with that threshold into J_j. Update c <- c-J_j once as a mathematical group, then test gcd(c,N) for [t_j,t_(j+1)-1].
3. Finish with the interval ending at N-1. Do not process an event at N.

Each interval is nonempty, since distinct integer thresholds differ by at least one. These intervals are disjoint, adjacent, and their lengths sum to N by telescoping. They include w=0, every threshold value, every one-point interval, and w=N-1. All floors are constant in each interval; (B) is therefore constant there. The scan tests every attained carry value. It may test a repeated value more than once, which is harmless and already charged by the upper bound.

A tie must be atomic **for factor testing and recording the current family value**. An intermediate sum after processing only part of a tie need not occur for any actual w. A proper gcd found there would be an observation from a different arithmetic consumer; it would not witness a proper split in this stated lift family.

A further reporting detail matters for the unchanged assay protocol: these are intervals delimited by floor changes, and need not yet be **maximal constant-c intervals**. If J_j=0, the adjacent intervals have the same c and must be coalesced when reporting maximal constant intervals. Preserve the tied event records and their original threshold in the evidence. Coalescing changes neither coverage nor any gcd result and requires no new case, control, seed, budget, or run. Nonadjacent occurrences of the same c stay distinct intervals, though a paid cache may avoid repeat gcds.

Zero carry has gcd N. A nonzero carry can also have full gcd N, so checking c!=0 alone is insufficient. A successful output requires d=gcd(|c|,N) with 1<d<N and a verified divisibility witness. Unit gcds and every full gcd remain failures. Testing each attained value separately avoids masking a proper leaf by a product gcd N; substituting one gcd of the product would require an additional paid localization method. Ordinary initial factors remain separately classified.

## 6. Event upper and lower counts have different meanings

The number of generated records is

    S_a=sum_i a_i=(m+1)a0+m(m+1)/2.

Equation (F) gives the exact retained count

    E=S_a-#{i:b_i<a_i},
    S_a-(m+1)<=E<=S_a.                              (G)

In particular, at a0=1,

    S_a=(m+1)(m+2)/2=O(R^2),
    E>=m(m+1)/2,

so this **explicit record-list algorithm** actually handles Theta(R²) individual retained events. For general positive a0, its generated and retained counts are Theta(R a0+R²), within the canonical endpoint guard. A large numeric a0 cannot be hidden by charging only its bit length.

In contrast, the number K of distinct thresholds, the number of maximal constant-c intervals, and the number of distinct carry values need not be Theta(E). Ties, zero-net updates, and repeated values can reduce them. The valid upper bounds are K+1<=E+1 and also K+1<=N. There is no proved Omega(R²) lower bound on gcd calls, successful values, or all possible algorithms for consuming this family.

The Theta(R²) count is a cost of the specified explicit enumeration and a possible source of symbolic compression beyond it, not a factoring lower bound. Nor does the upper count imply R² independent trials or a lower probability of success. The family still has exactly N parameter choices, represented by weighted intervals rather than by N materialized inputs or N output records.

## 7. Complete incremental cost and the conditional total

Let n=bit_length(N). Let F_int(t) bound the chosen t-bit multiplication, division, gcd/inversion, and routine arithmetic costs; specialize to soft O(t) only under the stipulated fast-arithmetic model. This is a theoretical bit-cost bound, not a claim about standard-library Python timing. Let C_base(N,R) denote the paid coefficient acquisition and batch lower-remainder evaluation supplied by the separate audit. For canonical a0 it has no unbounded input-width surcharge.

The additional work here is as follows.

- **Guards and setup:** O(R) small-input gcd checks, endpoint and input checks, and construction of the required powers of N. On the accepted branch log R=O(n). These are within soft O(R² n); any strategy searching many a0 or R values is additional.
- **Digits and c0:** O(R) exact divisions/remainder extractions from O(Rn)-bit r_i, O(R) binomial-weight recurrences with O(R)-bit weights, and O(R) products/additions to form the signed numerator. Its width is O(Rn+R+log(R+1)); exact division by M or N^L yields c0. A conservative bound is O(R F_int(O(Rn+R+log(R+1)))), which is soft O(R² n) with fast arithmetic. Generating the weights by the exact recurrence binom(m,i+1)=binom(m,i)(m-i)/(i+1) uses ordinary integer division, never a modular inverse.
- **Events:** set Q=n+log(a0+m+1). Every numerator kN-b_i, denominator a_i, ceiling result, and event index has O(Q) bits. Generating and retaining the S_a candidate records costs O(S_a F_int(O(Q))), including range checks and integer divisions. For a0=1, Q=O(n+log R).
- **Ordering and ties:** comparison sorting costs O(E log(E+1) Q) bit operations with ordinary comparisons. A linear pass groups equal thresholds and adds signed weights. Within a group each i appears at most once, so the sum of absolute weights is at most 2^m. Even intermediate group sums and a partially accumulated update have only O(R) bits, despite cancellation. This costs O(E R) bit work plus record access.
- **Gcds and output:** at most E+1 gcds have operand widths O(R) and n, hence cost O((E+1)F_int(O(n+R))). Proper-factor validation is included. Recording compact interval endpoints, lengths, carry, gcd, and references to tied events has O(E(n+R+log(a0+m+1))) worst-case bit output; its generation fits the same envelope. A solver that returns only a factor or failure need not retain this log.

Thus a transparent conditional bound is

    C_total <= C_base(N,R)
             + O(R F_int(O(Rn+R+log(R+1))))
             + O(S_a F_int(O(Q)))
             + O(E log(E+1) Q + E R)
             + O((E+1) F_int(O(n+R))),               (H)

with guards, modulus setup, and ordinary record traffic absorbed at these widths. The notation O inside the cost argument means a fixed constant multiple, not a unit-cost giant integer. All residues, products, exact divisions, signs, comparisons, and gcd widths have been priced.

For a0=1, using **the provisional** C_base=soft O(R² n) and fast integer arithmetic, (H) gives

    C_total=soft O(R²(n+R)).                         (I)

This accepts the proposed primitive envelope with its dependency made explicit. The general small-base-free version is conservatively

    soft O(R² n+(R a0+R²)(n+R)),

under the same acquisition interface, with no paid search for a0 included. If the separate audit revises C_base, replace that term in (H) instead of declaring (I) independently proved. A straightforward Horner acquisition has a larger honest bound and does not inherit the fast MPT rate merely because it returns the same values. The scalar controls and the diagnostic's corpus generation, metering, and complete logging also pay their actual additional work; they are not silently included in an implementation claim for (I).

For space, store events as (threshold,i,k) or (threshold,i), **referencing** a shared weight array. At a0=1 this costs

    O(R²(n+log R)) bits for the explicit event list,
    O(R²) bits for the O(R) weights,
    O(R) bits for the current carry and tied-weight sum,
    O(R² n) bits if all acquired base residues are retained,

plus polynomial-evaluation and integer-arithmetic workspace. The weights and retained base residues fit within the stated event-scale envelope (or the identified base workspace). Copying an O(R)-bit weight into every record would instead introduce O(R³) stored bits and must not be hidden in the target's event-list bound. Likewise, retaining every interval's O(R)-bit carry adds up to O(R²(n+R)) log storage; the lean event-space bound is for a streaming consumer, not an unqualified bound for a fully retained diagnostic transcript.

The scan does not materialize all lifted stencils. It computes their carry values through (B). A single lifted input has O(Rn) bits, which is paid whenever a direct control or a consumer actually constructs it. Requiring every input point or full scalar output at every interval adds corresponding generation, evaluation, and output costs; (I) is the bound for the described carry/gcd consumer and compact interval records, not such an expanded-output task. No factor, hidden period, ordering oracle, or unknown-prime-dependent lift is used.

For R=Theta(n), a0=1, and the guarded branch, (I) is soft O(n³), conditional on the base audit. More generally it is polynomial for polynomially bounded R. This is an upper bound for completing a **possibly unsuccessful** family, not a factoring-time upper bound, and not a matching optimality lower bound.

## 8. Remaining proper-split obligation and assay boundary

For a fixed valid (N,R,a0), the exact question is

    Does some attained interval value c satisfy 1<gcd(c,N)<N?

The sweep decides that question for the supplied family at the conditional cost above. It does not prove the answer is yes. For N=pq with distinct primes, success requires divisibility by exactly one of p and q; divisibility by both gives the full gcd. For prime powers and other composites the general proper-gcd criterion must be retained.

The magnitude bound (C) is support control, not useful supply. For example, if leastprime(N)>=4^R, every nonzero attainable c is too small in absolute value to share a prime factor with N, while c=0 has full gcd. This is a sufficient failure condition for this consumer, not a claimed converse, period obstruction, or small-tail theorem. Enlarging R removes that particular sufficient condition without forcing any proper output.

A uniform choice of w, if considered separately, has exactly the length-weighted success fraction

    (1/N) sum_over_intervals length(interval)
                         * 1_{1<gcd(c_interval,N)<N}.

Counting successful distinct values without their interval lengths is not this probability. The earlier full-fiber independent-digit result gives no independence for these coupled, shared-w, divided differences. Exhaustively testing all intervals also is not a collection of independent uniform trials.

An eventual deterministic factoring claim needs an N-only, fully paid schedule of R and a0, coverage of all promised composites and guard exits, and a proof that some visited family or preprocessing step supplies a proper factor. A randomized claim needs a justified per-input useful probability (or expected-work law) for its actual schedule, with all failures, restarts, acquisition, gcds, and output charged. Any claimed improvement needs comparison with an appropriate baseline under the same guarantee. Neither the event count nor a successful finite assay supplies these missing statements.

The independent assay already has fixed cases, depths, controls, budgets, and a one-run rule. This review does not change them, request another control, recommend retuning, or authorize a rerun. Its only protocol interpretation is that maximal constant intervals merge adjacent zero-net updates while retaining every event. Its direct lower-polynomial controls check (B) at the prescribed unwrapped inputs; its scalar control checks the minus sign in (D). Those finite checks can detect bookkeeping or implementation failure; they cannot establish the general proper-split obligation. The current report gives no execution result or prediction of the frozen cases.

The next proof that could change the factoring conclusion is a proper-split cover or useful-mass theorem for a uniformly specified, paid family schedule. The present computation supplies a concrete way to exhaust one family's actual carry values and a conditional cost for doing so. **Verified complete factoring improvement remains NONE.**

## 9. Delivery and limits of verification

The [read-scope record](W032-lift-sweep-review-evidence/read-scope.json) separates complete reads, coordination excerpts, and frozen-but-unreviewed context. The [validation record](W032-lift-sweep-review-evidence/validation.json) checks the brief and frozen-input byte hashes, records live-source drift, and lists the symbolic obligations resolved above. These are prose proofs, not a symbolic-program certificate, Lean proof, implementation test, or independent acceptance of the live carry-quotient audit.

The [complete delivery manifest](W032-lift-sweep-review-evidence/delivery-manifest.json) records this report and every evidence payload with path, byte length, and SHA-256. It excludes only itself and [terminal-manifest.sha256](W032-lift-sweep-review-evidence/terminal-manifest.sha256) to avoid circular hashing. Those two inventory files plus all listed payloads are the complete delivery. The final manifest hash is also returned externally in the terminal handoff. No report or payload is amended after sealing. Hashes establish byte identity relative to that external anchor, not mathematical correctness.
