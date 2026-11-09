# W032 unit-step remainder filter: independent symbolic review

**Disposition: ACCEPT the floor identities, varying-label reduction, small-tail sign guard, and stated operation/width bounds. REVISE the residual and parameter interpretation: the filtered residual is divisible by the unit D, leaving an integer c with |c|<4^R, even without equal labels. Moreover, the exact small-tail condition at all stencil points already forces R=O(log N/log log N). Therefore the guarded remainder-only filter cannot give a proper split for sufficiently large N with leastprime(N)>=N^eta, for any fixed eta>0. Verified complete factoring improvement: NONE.**

This is a pointwise obstruction to the final guarded filter, independent of how its valid starts are selected. It does not concern ordinary initial gcd exits, individual scalar digits, other consumers, or the same unit-step filter evaluated outside the small-tail guard. The latter still has the small residual proved below, but does not inherit this guard-induced restriction on R. No numerical test is selected or run.

## 1. Frozen scope and accepted inputs

The complete target, **including the conservative guard at the end of its cost section**, is frozen at [the input copy](W032-unit-step-review-evidence/inputs/research/findings/W032-unit-step-remainder-filter.md), SHA-256 `02f53c43eb782262bfd6470133204d365d1e0c4ea5902433566669afa75e20e0`. The [brief](W032-unit-step-review-evidence/brief.txt) and [input manifest](W032-unit-step-review-evidence/input-manifest.json) preserve the full assignment and 17 complete inputs. Initial file discovery/inspection preceded the freeze; the mathematical audit uses the frozen bytes. The target itself was not edited.

The five governing documents, original W032, scalar/carry review, current W032/W033 parent disposition, completed joint-lift, near-top and exact-period algorithm reviews, canonical-difference review, canonical-floor note, and two narrow comparator reports were read. STATE is a full snapshot used only for coordination excerpts; the explicit brief and current parent disposition supersede its older live-task descriptions. Exact coverage and exclusions are in [read-scope.json](W032-unit-step-review-evidence/read-scope.json).

The imported mathematical interface is the accepted scalar diagonal and canonical floor, including its exact denominator and lift semantics. Joint uniformity applies to full lift fibers only; it supplies no canonical-input law here. The near-top selector repair is retained. The exact-period algorithm is an accepted separate computation. The live label-period lower-bound target/review and W033 primitive-ratio target/review were not read or duplicated. No broad history or new external-source claim is made; the coefficient/height comparison below uses only the stated local theorem scopes.

All new evidence consists of general symbolic prose proofs. Terminal work was restricted to file inspection, evidence copying/writing, and integrity checks. No candidate evaluation, symbolic computation program, numerical substitution, parameter sweep, assay replay, Lean proof, project check, install, commit, delegation, shared code/STATE/task edit, or outside-project work occurred.

## 2. Exact lifts and legal inputs

Let N>1 and R>=1 be integers, with

    D_j=4^j(2j+1)!,    D=D_R,    m=2R+1,    M=N^(2R+1),
    gcd(D,N)=1.

For the factoring application N is composite. Since the primes dividing D are exactly those at most 2R+1, this checked gcd is equivalent to leastprime(N)>2R+1. It implies N is odd, all coefficient denominators through R are units, and R is within the accepted scalar expansion's index range. No factorization or least-prime oracle is supplied.

Write

    E_j(Y)=product_(v=1..j)((2v-1)^2-Y)
          =sum_(h=0..j) e_(j,h)Y^h,
    C_k(X)=sum_(j=ceil(k/2)..k) (D/D_j)e_(j,k-j)X^j.

Thus C_k belongs to Z[X], C_0=D, and deg C_k=k. The leading coefficient of C_k is

    (D/D_k) P_k,       P_k=product_(v=1..k)(2v-1)^2 > 0,

with P_0=1. This explicit leading coefficient will matter for the guard's range, not just for coefficient cost.

Take the **unwrapped** points a_i=a0+i, 0<=i<=m, all in [0,N) and all units. Necessarily

    1 <= a0 <= N-1-m.

The target's m<N is a necessary width condition, not the full input specification. Wrapping modulo N or deleting/replacing failed points does not preserve this polynomial-in-i stencil. A public valid unit choice is a0=1 on the checked denominator branch: every integer through 2R+2 has all prime factors at most 2R+1, and 2R+2<N. This supplies units, not passing tail guards or a useful gcd. General supplied starts require their own checks.

For a permitted a set

    F(a)=sum_(k=0..R) N^(2k) C_k(a^2),
    h(a)=[-F(a) M^(-1)]_D,
    T(a)=(F(a)+h(a)M)/D in Z.

Brackets denote the canonical integer residue. The inverse M^(-1) is modulo D. The accepted V_R is [T]_M. If V_R=T-vM, taking a floor after division by N^(2R) changes it by exactly vN. Hence, with mathematical floor also for negative numbers,

    d_R(a) = q(a) mod N,
    q(a)=floor((K(a)+epsilon(a))/D),
    K(a)=C_R(a^2)+h(a)N,
    epsilon(a)=sum_(k<R) N^(2k-2R) C_k(a^2).             (2.1)

All N-negative powers in epsilon are **ordinary rational numbers inside the real floor**, not residues modulo N. Define f(a)={(K+epsilon)/D} in [0,1). Then the exact rational equality

    D q(a)=C_R(a^2)+epsilon(a)+Nh(a)-D f(a)             (2.2)

has an integral right-hand side as a whole. Thus the target's congruence is valid as equality up to an integer multiple of N. It must not be split into separate congruences for epsilon and f modulo N. The argument below keeps (2.2) as a rational equality until its integral combinations have been identified.

## 3. The missing divisibility: D does not enlarge gcd support

For a sequence v_i define

    Delta^s v = sum_(i=0..s) (-1)^(s-i) binom(s,i)v_i.

Over Q, Delta^s annihilates every polynomial in i of degree less than s. Here deg_i F(a_i)=2R, deg_i C_R(a_i^2)=2R, and deg_i epsilon(a_i)<=2R-2. Consequently their order-m differences vanish exactly.

The label h need not be a polynomial as an integer-valued canonical representative. However, its defining congruence gives

    M Delta^m h = -Delta^m F = 0 mod D.

Since gcd(M,D)=1, this proves the exact integer divisibility

    D divides Delta^m h.

Let v=(Delta^m h)/D in Z. Applying the difference to (2.2) and dividing the resulting rational equality by D gives

    Delta^m q = Nv - Delta^m f.

Therefore

    c := Delta^m q-Nv = -Delta^m f in Z,
    Z=Delta^m d_R = c mod N.                            (3.1)

This is the omitted strengthening. Equal h labels are unnecessary: their difference has the particular divisibility needed after division by D. No period computation or lower bound is involved.

The positive and negative binomial weights each have total magnitude 2^(m-1)=4^R. With every f_i in [0,1), each corresponding positive sum lies in [0,4^R), strictly at the upper endpoint. Their difference obeys

    |c|<4^R,             gcd(Z,N)=gcd(c,N).              (3.2)

In the target's unnormalized notation, the integer residual is exactly Dc, and its bound |Dc|<D4^R is true. But gcd(D,N)=1, so the factor D contributes **no prime support** to the gcd. Merely making D large cannot make this residual see primes between 4^R and D4^R.

If c=0 the gcd is N. If c is nonzero and leastprime(N)>=4^R, the gcd is 1, since every prime dividing c is at most |c|<4^R. This holds for arbitrary multiplicities, including prime powers. No distributional hypothesis is used. The identity and bound in this section do **not** require the small-tail guard.

At R=1 the accepted d_1(a)=a^2/24 mod N has third difference zero, so Z=0 and the filtered gcd is N for every valid unit stencil. This is a symbolic boundary identity, not a sample evaluation.

## 4. Guarded floor, negative boundaries, and lower-polynomial evaluation

Suppose |epsilon(a)|<1. Put sigma=1 for epsilon<0 and sigma=0 for epsilon>=0, and define

    t=[K-sigma]_D,        y=sigma+t.

There is an integer q0 with K-sigma=Dq0+t and 0<=t<D. If epsilon>=0 then 0<=t+epsilon<D. If epsilon<0 then 0<t+1+epsilon<D; the upper endpoint is strict even at t=D-1 because epsilon<0. In both cases

    floor((K+epsilon)/D)=q0=(K-sigma-t)/D=(K-y)/D,
    f=(y+epsilon)/D.                                    (4.1)

This covers negative K as well: q0 is the Euclidean quotient, not truncation toward zero. If epsilon=0 and D|K, y=0 and the floor is K/D. If -1<epsilon<0 and D|K, t=D-1 and y=D, so the floor is K/D-1. The sign bit is essential at that negative boundary. The endpoints epsilon=+1 or -1 are not licensed by the strict guard.

Combining with (2.1) gives the target's accepted identity

    D d_R(a)=C_R(a^2)-y(a) mod N.                       (4.2)

Consequently D Z=-Delta^m y mod N and

    gcd(Z,N)=gcd(Delta^m y,N).

To compute K modulo D, start from F+hN^(2R+1)=0 mod D and multiply **in Z/DZ** by N^(-2R):

    K = -sum_(k<R) u^(2R-2k) C_k(a^2) mod D,
    u=N^(-1) mod D.                                    (4.3)

The term C_R cancels exactly. Formula (4.3) is legal because N is a unit modulo D; it does not obtain its meaning by reducing the rational epsilon modulo N. The scalar, h, C_R values, and V_R need not be evaluated. The polynomial in X=a^2 has degree at most R-1.

There is a second direct proof of the missing divisibility. Since y=K mod D, (4.3) makes y congruent to a polynomial in i of degree at most 2R-2. Hence

    D divides Delta^m y.

Using (4.1) and Delta^m epsilon=0 gives the sharper computational identity

    c=-(Delta^m y)/D in Z,
    |c|<4^R,
    gcd(Z,N)=gcd(Delta^m y,N)=gcd((Delta^m y)/D,N).       (4.4)

Thus one can divide the accumulated **integer** difference by D exactly before its gcd. This is not a modular inverse of N. The strict bound still comes from f in [0,1), not from the endpoint bound 0<=y<=D. All equations (1) and (2) of the target are accepted; (4.4) supplies the missing arithmetic constraint on their output.

## 5. The conservative sign guard is safe

For each point evaluate the integer values C_k(a^2), k<R, and put M_a=max|C_k(a^2)|. Since C_0=D>0, M_a>0. The finite geometric sum is exactly

    sum_(h=1..R) N^(-2h)=(1-N^(-2R))/(N^2-1).

Therefore M_a<N^2-1 implies

    |epsilon(a)| <= M_a(1-N^(-2R))/(N^2-1)
                  < M_a/(N^2-1) < 1.                   (5.1)

The strict intermediate inequality is justified by M_a>0; there is no overlooked zero-M boundary.

Let j be the largest k<R with C_k(a^2) nonzero. It exists because C_0=D. Factoring a positive rational power gives

    epsilon(a)=N^(2j-2R) [C_j(a^2)+L_a],
    L_a=sum_(k<j) N^(-2(j-k)) C_k(a^2).

For j>0 the same geometric argument gives |L_a|<M_a/(N^2-1)<1. For j=0, L_a=0. The integer C_j is nonzero, so |C_j|>=1 and C_j+L_a has its sign. Thus

    sign(epsilon(a))=sign(C_j(a^2)).                    (5.2)

The proposed guard and sign extraction are correct and require no N^(2R) numerator. Modulo-D coefficient values alone cannot supply M_a or the sign; the exact integers and their actual widths are required.

In fact the actual epsilon cannot be zero anywhere on the denominator-unit branch: its integer numerator S=sum_(k<R)N^(2k)C_k(a^2) is D mod N, a unit. Thus S is not zero. This does not license dropping the zero case from the general floor lemma; (4.1) correctly treats it anyway. The strict conservative guard is sufficient, not a necessary test, and its failure does not justify declaring the true epsilon large or choosing a sign.

## 6. Small tails themselves restore the depth obstruction

There are two independent ways to see the relevant restriction. First, the conservative guard has M_a>=D, so even one passing point implies

    D<N^2-1.

Since log D=Theta(R log(R+1)), this already forces R=O(log N/log log N), uniformly as N grows. This restriction arises from the guard, despite the absence of the old mD<N stencil-width condition.

More strongly, **every implementation using the exact condition |epsilon(a_i)|<1 at all points**, even one with a sharper guard or exact wide numerator, has the same order of depth restriction. For R>=2 put r=R-1 and s=2r. The polynomial epsilon(a) has degree exactly s. Its leading coefficient is

    A/N^2,       A=(D/D_(R-1)) P_(R-1)>0,
    D/D_(R-1)=4(2R)(2R+1)=8R(2R+1).

Only k=R-1 contributes at degree s; all lower k have degree at most s-2. Translation by a0 leaves the leading coefficient unchanged. The exact forward-difference identity therefore gives

    Delta^s epsilon(a0)=(2r)! A/N^2.                   (6.1)

The first s+1=2R-1 points are part of the required 2R+2-point stencil. Each has |epsilon|<1. Their binomial difference has absolute value strictly less than the sum of its absolute weights, 2^s=4^r. Since (6.1) is positive,

    N^2 > (2r)! A/4^r.                                (6.2)

This is an explicit, public necessary inequality for any passing stencil. It is independent of a0, label periods, hidden factors, or a sampling assumption. It can reject parameter choices before any point evaluation if implemented with its own paid arithmetic; no such implementation was run here.

For a simple uniform asymptotic proof, use A>=1 and (2r)!>=r^r. For r>=16, log r-log 4>=(log r)/2, so (6.2) implies

    r log r < 4 log N.

Let L=log N. If r>sqrt(L), then log r>(log L)/2 and r<8L/log L. If r<=sqrt(L), then r=O(L/log L) as well. Bounded r is included. Hence, uniformly over every R and a0 satisfying all exact guards,

    R=O(log N/log log N),
    log(4^R)/log N=O(1/log log N),
    4^R=N^o(1).                                       (6.3)

No Stirling approximation or extrapolation from a finite computation is needed. R=1 is covered by its exactly zero filter separately.

Fix eta>0. For all sufficiently large N, simultaneously for every guarded valid stencil, (6.3) gives 4^R<N^eta. If leastprime(N)>=N^eta, then (3.2)/(4.4) permits only gcd 1 or gcd N. **There is no proper filtered output.** This is stronger than an upper density estimate and remains valid for adaptive/nonuniform selection of starts and parameters, provided each selected filter satisfies the stated guards. It is not a statement about all output channels of a larger algorithm.

The target correctly removes the *old width* restriction mD<N. Its suggested opportunity from a large D4^R residual nevertheless fails for the guarded computation for two exact reasons: D divides that residual and is a known unit, and the small-tail condition reimposes sublogarithmic depth through (6.2). Better sign certification alone cannot remove this second restriction while retaining the same |epsilon|<1 premise at every point.

Outside that premise, the scalar or full-floor evaluator is a distinct paid computation. Section 3 still supplies |c|<4^R, but (6.2) no longer follows, and canonical unit-step width alone does not force R=O(log N/log log N). No useful separating support, full cost advantage, or impossibility theorem for that unguarded regime is supplied here.

## 7. Full widths, setup, and actual saved work

Let b=bitlen(N), w=bitlen(D)=Theta(R log(R+1)), and

    H=O(R b+R log(R+1)).

The coefficient recurrence E_j=((2j-1)^2-Y)E_(j-1) uses O(R^2) integer coefficient operations. Multipliers D/D_j must be formed by exact integer division **before** reducing modulo D; they are not modular divisions by nonunits. One can construct them recursively from D using the exact divisors 4(2j)(2j+1). Coefficient sizes obey

    sum_h |e_(j,h)|=product_(v=1..j)(1+(2v-1)^2)
                   <=(1+4j^2)^j.

Together with D/D_j<=D this proves O(w)-bit coefficients in every C_k. Polynomial-in-R setup and the claimed coefficient bound are justified; smoothness of D does not make these operations free.

For a<N, Horner evaluation at a^2 of a degree-k polynomial has intermediate and output widths O(w+k b+log(R+1))=O(H). It is invalid to truncate a failing point to the prospective guard's O(b) accepted-output bound. Cancellation can occur in intermediate sums; the displayed H is a safe bound on them too. If a0 is bounded by a fixed polynomial in R, all a_i are also polynomial in R, and the same calculation gives H=O(R log(R+1))=O(w) for these polynomial evaluations. Input N still has b bits, and its reading, checks, reduction and final gcd do not disappear.

A transparent implementation ledger for one supplied full stencil is:

- Construct D, the exact lower C_k tables, and the modulo-D polynomial in (4.3). The row/diagonal work takes O(R^2) integer operations at O(w) width. Constructing the powers of u^2 takes O(R) modular operations after reducing N modulo D and checking/inverting it.
- Evaluate all R lower polynomials at all 2R+2 points for the conservative guard. Straight Horner evaluation takes O(R^3) integer operations at O(H) width. Extract M_a and the last nonzero coefficient sign with O(R^2) value inspections/comparisons. Compute N^2 once and compare exactly; N^2 has O(b) bits. No N^(2R) numerator is formed by this guard.
- Evaluate the single degree-(R-1) polynomial (4.3) at the O(R) reduced points with O(R^2) modular operations at O(w) width. Reducing original b-bit N and points modulo D is paid separately. Products temporarily have O(w) bits up to a constant factor, including reduction costs.
- Check the supplied points and denominator branch. At most O(R) b-bit point gcds suffice; a publicly proved unit choice can reuse its certificate. A proper denominator/point gcd is an ordinary initial split. A full gcd is not a split; a denominator failure can be localized among its known small integer factors, with the actual work charged.
- Generate binomial weights using b_0=1, b_(i+1)=b_i(m-i)/(i+1), with exact integer division. Each weight has O(R) bits. Accumulate the signed products with 0<=y<=D; even the sum of all absolute terms is at most D*2^m, so O(w+R) bits suffice for products and partial sums, up to constant additions. The final exact division by D gives c with O(R) bits. Finish with gcd(c,N) and proper-divisor validation, paying for the b-bit input and division/remainder work as needed.

For example, let F_int(t) be a monotone bound for the chosen exact t-bit multiplication, reduction/division and gcd routines. A conservative bit envelope for this implementation, including the comparisons and ordinary checks, is

    O(R^3 F_int(H+b) + R^2 F_int(w) + R F_int(b+w)).     (7.1)

The formula names actual finite-width primitives rather than treating arithmetic operations as bits. It is intentionally not an optimized bound. The ledger gives the more informative separation when a0 is small: the polynomial arithmetic uses H=O(w), while N-related checks still use b. Arithmetic workspace is additional. Keeping all coefficient polynomials costs O(R^2 w) bits; retaining the entire evaluation table would add O(R^2 H) bits. Streaming a point's values, maximum/sign data, modular polynomial and running difference avoids that extra table storage. These costs are polynomial in the value R and b, not automatically in log R and b for arbitrarily supplied R.

Alternatively, the exact numerator guard uses

    S(a)=sum_(k<R)N^(2k)C_k(a^2),
    |S(a)|<N^(2R),      sign(epsilon)=sign(S).

It is correct, but the powers, combined polynomial coefficients, Horner work, and comparisons have O(Rb+w) widths and must be paid. It does not evade (6.2), which is a property of passing inputs, not of the chosen checking algorithm.

Relative to literally computing the top scalar digit separately at every point of a fresh valid stencil, the new evaluator eliminates **2R+2 point-dependent quadratic-algebra power calls**. This is an exact primitive replacement for the same final gcd, not an extraction of every individual digit for other consumers. Previously cached digits or a different acquisition algorithm change that comparator. The accepted scalar review already gave a direct public polynomial/floor evaluator; scalar removal at fixed R was therefore already available, while this target specifies a different lower-polynomial/modulo-D consumer under its guard.

No complete bit speedup follows from the operation count. The guard's O(R^3) full-integer work may dominate. In particular the existing combined-F floor evaluator uses O(R) wide Horner steps per point after setup; the conservative guard can perform more R-dependent work. The literal scalar-stencil comparator has the accepted soft O((R+1)^2 b^2) acquisition envelope under its fast-arithmetic model. Comparing upper bounds, or deleting power calls while adding guard work, is not a proof of an end-to-end improvement. All setup, parameter/point selection, unsuccessful guards, retries and localization remain paid.

A failed guard must leave the **whole specified stencil** uncomputed by this shortcut. One may record and skip it, or use a separately specified/charged algorithm. Dropping a bad point, resampling until a good stencil without charging rejects, assigning an unproved sign, or silently substituting scalar evaluations would change the algorithm. Every nonunit, failed guard, zero residual, unit gcd, full gcd, sampling failure and unstarted attempted case must retain its branch identity. No run log is supplied because no run was authorized or performed.

## 8. Scope of older bounds and required disposition changes

The W031 normalized-coefficient height theorem concerns separate gcds of a uniformly capped collection of fixed public rational-coefficient numerators. Its finite-union set is independent of N within the stated cap; new input-dependent combinations/evaluations were explicitly excluded. Here (4.3) depends on N modulo D, on the actual a values, and on signs determined by exact polynomial values under the guard. Its residue representatives and finite-difference consumer are different tested integers. The old fixed-coefficient prime-union argument therefore does **not** automatically cover this computation. The W028 coefficient-or-factor baseline has a different output contract and supplies no theorem about this carry filter.

The relevant older local result is the high-order finite-difference residual proof. Section 3 extends its algebra to varying labels by proving D|Delta^m h, rather than assuming h constant. Section 6 then supplies an independent guard-induced depth bound. These two exact arguments settle the large-factor guarded regime without a history survey, prime-density heuristic, or lower-bound audit of label periods. The present result neither uses nor reproduces the separate live odd-prime period work.

Required changes to the target's interpretation are precise:

1. Retain equations (1), (2), the small-tail/sign proof, and the full cost caveats. Add the exact identities D|Delta^m y and c=-(Delta^m y)/D, with |c|<4^R and gcd(Z,N)=gcd(c,N). State that D cannot enlarge gcd support.
2. Retain the removal of the old mD<N width requirement. Add the necessary guard inequality (6.2), or at least the conservative consequence D<N^2-1 when discussing that guard. The sharper consequence applies to every exact small-tail guard across the stencil, not only the conservative one.
3. Replace an unrestricted open-yield description of the guarded large-factor regime with its pointwise negative result: for fixed eta>0 and sufficiently large N with leastprime(N)>=N^eta, every valid guarded filter gives gcd 1 or N. Yield remains unresolved only in regimes not disposed of by that theorem, such as smaller least factors or changed consumers/guards.

A materially different next computation would have to retain useful information outside this bounded-tail, order-(2R+1) consumer: for example, specify a paid evaluator handling larger integer tail carries, or derive another consumer. Such a proposal would need its own actual expression, complete cost and proper-split guarantee. This report does not select or run a numerical diagnostic, promise that such a change works, or claim every future selector must use a particular correlation.

The tested failed premise is that the smooth D can enlarge the effective remainder support while all tails remain below one. Its exact failure is the removable unit D together with (6.2), not a heuristic lack of random-looking output. The accepted identities are useful acquisition reductions, but **verified complete factoring improvement remains NONE**.

## Delivery integrity

[validation.json](W032-unit-step-review-evidence/validation.json) records frozen-input/brief integrity, live-source drift, the symbolic-only action scope, and the proof obligations resolved above. The [complete delivery manifest](W032-unit-step-review-evidence/delivery-manifest.json) contains the report and every evidence payload with path, byte length and SHA-256. It excludes only itself and [terminal-manifest.sha256](W032-unit-step-review-evidence/terminal-manifest.sha256), avoiding circular hashes. Those two inventory files plus the listed payloads are the complete delivery. The final manifest hash is also returned outside the files in the terminal handoff. No report or payload is modified after sealing. Hashes establish byte identity relative to that anchor, not mathematical or machine-verified correctness.

Only this report and W032-unit-step-review-evidence/ were written. All proofs are prose; no candidate numerical computation or project test was performed.
