# I205 analytic record

2026-10-12. **UNRESOLVED; no substantial nomination.** All logarithms are natural unless indicated. The exact target is:

> There exist absolute A,C,b0 such that for every integer b>=b0 and every integer 1<=a<b, a/b is a sum of at most C loglog b distinct positive unit fractions, each with integer denominator at most b^A.

Fractions need not be reduced. Constants cannot depend on a or b. The source theorem and all lower operations at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb are accepted. Neither truth nor worldwide open status of the target is assumed. I204's literal-path obstruction, binary reservoir obstruction, and subquadratic common-denominator obstruction are accepted inputs, not re-proved here. In particular none implies a lower bound ruling out the target.

## 1. Actual source operations and where the budget enters

Read the full introduction, elementary reduction, residue construction, descent, counting, and prescribed-denominator sections in the I204 pinned source copies. The actual operations needed here are:

* `elementary.tex`, `lem:distinct`: Takenouchi replacement preserves the number of terms below total one, with termination supplied by finiteness. It supplies no uniform polynomial size bound.
* `counting.tex`, `lem:marked-cleanup`: odd-divisor-preserving duplicate removal at total one. It preserves a multiple of an odd marker, not necessarily its exact value.
* `counting.tex`, `eq:divisor-split`: for a proper divisor d of n, 1/n=1/(n+d)+1/(n+n^2/d). Avoiding a finite set of denominators excludes at most twice its size in choices of d.
* `prescribed.tex`, `lem:marked-greedy-prefix` and `lem:exact-marker-padding`: exact marker preservation by reserving a term and making the tail smaller than every reserved reciprocal; padding separately retains the marker. These do not bound the resulting maximum by a fixed power of the original denominator.
* `prescribed.tex`, `lem:rational-divisor-supply`: s=sum e_i/t_i, h<=16, e_i|K_m for every 1<=s<=m^4. The t_i need not agree. It uses log K_m=O(log m loglog m), three integer prime blocks each consisting of five divisor products over one common t, an optional 1, and a factorial for small s.
* `prescribed.tex`, `lem:marked-grouping`: a group d s contributes unit denominators (q/d)(K_m/e_i)t_i. Thus the t_i cost must be included; neither a residue identity nor bounds on q and K_m alone settle the cap.
* `residues.tex`, `eq:residue-step`, and `descent.tex`, `eq:rescaled-descent`: the rescaling factors multiply down a path; the C-to-1 transition adds a factor C. I204 rules out simply selecting polynomial-cost paths for the same dense family. It does not rule out changing the final sum.

No source operation above is offered as new. The source's own primary comparison is the simultaneous theorem of Tenenbaum–Yokota, whose term count is of order log b/loglog b, not loglog b.

## 2. Route A: bounded global replacement and distinctness

The intended new construction was to replace the large-denominator part of a short expansion, possibly borrowing some earlier terms, with a bounded collection of polynomial-size unit fractions. The following two deductions identify what can and cannot be handled locally.

### 2.1 A small positive tail cannot be replaced in isolation

For an integer B>=1, every nonempty positive sum of unit fractions with denominators at most B is at least 1/B. Consequently a tail of value 0<t<1/B has no such replacement, regardless of the number of replacement terms. More generally, if a block contains r terms with denominators all strictly greater than rB, its total is less than 1/B and it cannot be replaced independently.

If a prefix is held exactly fixed and its remaining positive value is below 1/B, no alteration confined to that tail can achieve the cap B. This excludes a naive local truncation/cleanup. It says nothing about a replacement that also changes prefix terms: such a replacement can transfer a larger amount into the tail. It is a positivity observation, not an impossibility theorem for the target.

The actual attempted carry operation was

1/n+t = 1/(n+1) + [1/(n(n+1))+t].

It preserves positivity and creates mass at least 1/(n(n+1)). If n is polynomially bounded, this overcomes the elementary small-mass obstacle for a sufficiently large polynomial cap. But if the bracket is represented over its reduced denominator, that denominator can still contain all the large factors of t. If instead it is represented over the original a/b and the retained prefix, its denominator divides b times the product of retained prefix denominators. That is polynomial only if the retained prefix already has a bounded total logarithmic size. No numerator-uniform short completion with that budget was obtained. Repeating the identity is not a proof of such a completion.

### 2.2 A divisor-rich multiplier gives bounded distinct cleanup

**Lemma (technical transfer operation).** Let k>=1, N>=1, and let n_1,...,n_k<=N be positive integers, with repetitions allowed. Let K be a positive integer with tau(K)>=4k+2r, where F is any set of r positive forbidden denominators. Then

(1/K) sum_{i=1}^k 1/n_i

has an expansion into exactly 2k distinct positive unit fractions, avoiding F, with every denominator at most 2(KN)^2.

**Proof.** Put v_i=K n_i. Use proper positive divisors d of K; each divides v_i and is strictly smaller than v_i. There are at least tau(K)-1 choices. Replace

1/v_i = 1/(v_i+d) + 1/(v_i+v_i^2/d).

The two new denominators are integers and satisfy v_i+d<2v_i<v_i+v_i^2/d. For a fixed forbidden value f, at most one d solves v_i+d=f and at most one solves v_i+v_i^2/d=f. At stage i the forbidden set consists of F and the 2(i-1) denominators already produced. Hence at most 2r+4(i-1) choices are excluded. Since tau(K)-1>=4k+2r-1>2r+4(i-1), a choice exists. The resulting two denominators are at most v_i+v_i^2<=2(KN)^2. Induction proves distinctness, avoidance, positivity, equality and the stated size. The proof also works when several v_i are equal. No iteration of quadratic replacement is used. □

This is the source's divisor-indexed splitting with a common multiplier supplying many choices. It is a useful new arrangement in this record, but not a new substantial mechanism relative to the paid source operations.

**Proposition (multisets suffice for the exact target).** Suppose that absolute A>=1,C>0,b0 give the target statement with repetitions allowed. Then the distinct target holds, for example with exponent 12A+3 and length coefficient 4C+3 after increasing b0.

**Proof.** Let L=loglog b and take b sufficiently large. Set s=ceil(16CL)+1 and K=2^s. Then K<=b eventually. Apply the source's ordinary greedy preparation to a/b with threshold T=b^3. It produces at most 3L distinct prefix terms for sufficiently large b, all denominators below b^6, and either finishes or leaves R/q with

1<=R<=b, b^3<=q<b^6.

The prefix is distinct and R/q is smaller than every prefix reciprocal. Indeed an ordinary greedy step with z=ceil(1/x)>=2 leaves 0<=x-1/z<1/(z(z-1))<=1/z, and later remainders only decrease.

If it finishes, there is nothing to prove. Otherwise 0<KR/q<=b^2/b^3<1. Apply the hypothesized multiset theorem to the integers KR,q, without reducing them. It gives k<=C loglog q<=2CL terms and denominators at most q^A. Apply the cleanup lemma to this expansion with multiplier K, which scales its value by 1/K and splits each term. Since tau(K)=s+1>=4k for large b, the lemma with r=0 gives a distinct expansion of R/q into 2k terms, of maximum denominator

2(K q^A)^2 <=2b^(12A+2)<=b^(12A+3).

Every new reciprocal is at most its positive total R/q and thus strictly below every prefix reciprocal. Hence the tail avoids the prefix automatically. The total length is at most (4C+3)L. Equality, positivity and all numerator-uniform bounds hold also when the input fraction is unreduced. The reverse implication is immediate. □

This proposition removes a genuine technical burden: a future bounded multiset construction would not need a separate delicate duplicate analysis. It does not manufacture a bounded multiset construction from the unrestricted source theorem. In particular the original source's enormous raw denominators remain enormous after multiplication and squaring. It does not close Route A and is not nominated.

## 3. Route B1: genuinely rational blocks, with all size factors counted

A route independent of the raw residue recursion is to start with a greedy remainder R/q, keep q divisor-dense, and use a rational supply as in the source, but with a polynomial-size integer K and controlled denominators t_i. For a group ds,

(ds)/(qK) = sum_i 1/[(q/d)(K/e_i)t_i],

provided d|q and s=sum e_i/t_i with e_i|K. This identity is exact and positive, and the different t_i allow the resulting lcm to be much larger than the individual denominators. The transfer in Section 2 handles repetitions once the bounded multiset construction exists.

A concrete sufficient strengthening would give fixed B,D,E such that, for every sufficiently large m, a common integer m<K<=m^D supplies each s<=m^4 as at most B positive e_i/t_i with e_i|K and t_i<=m^E. To spell out the implications: prepare an ordinary greedy remainder R/q with R<=m and threshold T=mK. The source's divisor-density proof applies with initial denominator m (the case m=b), so q has a divisor in [w/m,w] at every scale. Then X=RK<q, and `lem:marked-grouping` uses at most B((D+1)/2+2) terms. Here q<(mK)^2, and every emitted denominator is at most qK m^E<=m^(2+3D+E). The greedy prefix has O(loglog m) terms. Applying Section 2 to the resulting bounded multiset statement would settle the target. This is a sufficient missing input, not an asserted theorem.

The source's actual construction does bound its t_i: in a prime block p=(e_1+...+e_5)/t, each e_i<=K, so t<=5K/p<=5K. The optional 1 and the small-integer factorial cases use t=1. Thus uncontrolled arbitrary t is not the only issue in this source operation: K itself is m^{O(loglog m)}. Merely tracking that estimate is below the requested gate.

### 3.1 Why polynomializing the same integer-prime-block construction fails

For fixed integers h,r>=1 and fixed D>0, let 1<=K<=Y^D. Let B_h(K) consist of positive integer values

v=(e_1+...+e_j)/t, 1<=j<=h, e_i|K, t in the positive integers.

Repetitions are allowed. For a chosen numerator E=e_1+...+e_j<=hK, an integer value v must divide E, since E=vt. Consequently

|B_h(K)| <= (h+1)(tau(K)+1)^h max_{1<=E<=hK}tau(E) = Y^{o(1)}.

The elementary divisor estimate used in Section 4 below justifies the uniform o(1). Hence sums of at most r members of B_h(K), even with a bounded number of exceptional options, take at most Y^{o(1)} values. They cannot cover all Y integers in [1,Y]. This remains true with a fixed finite collection of polynomial-size K's in place of K, by taking a finite union.

It follows that the source's recipe through three integer prime blocks of five divisor products each cannot simply be run with a polynomial-size common K for all targets. It would produce only Y^{o(1)} integer outputs, rather than all integers through Y. The argument is stronger than counting the residues of the initial divisor list alone: it allows every common positive t per block and every possible resulting integer, not just primes.

**Scope check.** The obstruction does not apply to s=sum e_i/t_i when partial sums are nonintegral and the t_i are independent. For example, 1=1/2+1/3+1/6 has nonintegral singleton summands; requiring each singleton to be an integer would throw it away. Nor does it cover K chosen separately for every s, or a number of integer blocks growing with Y. It is a limitation of a specific attempted supply, not of the actual target.

**Gap.** The new construction would need to arrange exact rational cancellation between independent blocks, with both K and each (K/e_i)t_i polynomially bounded. No such common supply was proved. Allowing separate K_s does not by itself solve the grouping construction, because q and X=RK are chosen using the common K before the small integers s_i are selected. This order-of-choice problem cannot be removed by choosing the reservoirs retrospectively.

## 4. Route B2: independently sized prime-removal blocks

A second attempt inside Route B was to permit a changing lcm and eliminate prime factors using short sums of modular reciprocals, keeping the emitted denominators individually small. This is not the fixed-Q divisor-sum scheme excluded in I204.

For x=A/(pq), p prime and p not dividing q, choose positive m_1,...,m_j coprime to p with

sum_i m_i^(-1) = A q^(-1) (mod p).

Put L=lcm(q,m_1,...,m_j). Then

x - sum_i 1/(p m_i) = [A L/q - sum_i L/m_i]/(pL) = r/L,

where r is an integer. This proves cancellation of p exactly. It proves positivity only when the bracket is nonnegative; congruence alone gives no sign. The emitted denominators are p m_i. The remainder denominator divides L, which may exceed every p m_i. There is no global polynomial lcm assumption here.

In the especially clean q=1 case, x=a/p. If M=lcm(m_i), then the remainder is (aM-sum M/m_i)/(pM). For a>=j it is nonnegative because sum 1/m_i<=j. If the m_i are distinct and a=j>=2, strict positivity also holds; the one-term equality case is harmless. For small a, sign must be checked separately. A strict negative example with distinct terms is p=5, a=1 and (m_1,m_2,m_3)=(1,2,3): the inverse sum is 1+3+2=1 mod 5, but 1/5-(1/5+1/10+1/15)=-1/6. Thus even distinct residue matching does not establish positivity.

### 4.1 Uniform contraction costs choices

Fix epsilon in (0,1), let P=floor(p^(1-epsilon)), and consider the residue set

R(p,P,h)={sum_{i=1}^j m_i^(-1) mod p : 0<=j<=h, all m_i divide some M<=P}.

The M may vary with the target residue. Then

|R(p,P,h)| <= sum_{M<=P}(tau(M)+1)^h.

To justify the padding count, a length-j list of divisors is encoded by a length-h list of divisors and blank symbols; its modular sum is then determined. In particular, for fixed h,

|R(p,P,h)| <=p^(1-epsilon+o(1))=o(p).

Thus a bounded number of terms cannot uniformly remove p while requiring the new lcm to be <=p^(1-epsilon), even with a separately chosen M for each numerator. The class includes distinct lists and allows repetitions, so removing repetition restrictions does not repair the count.

Here is an explicit uniform estimate when h varies. Write S=log p. For n<=p, split prime factors at sqrt(S). The primes <=sqrt(S) contribute at most sqrt(S) log(1+S/log 2) to log tau(n), since there are at most sqrt(S) of them and each exponent is <=S/log 2. The total multiplicity of larger primes is <=2S/log S, and a+1<=2^a, so they contribute <=2(log 2)S/log S. The first contribution is o(S/log S). Consequently, for all sufficiently large p,

log(tau(n)+1)<=3S/log S uniformly for 1<=n<=p.

It follows that

|R(p,P,h)| <=exp[(1-epsilon)S+3hS/log S].

For h<=epsilon loglog p/6 this is at most p^(1-epsilon/2). This explicit coefficient is merely a convenient safe constant, not a claim of sharpness.

This supplies a quantitative obstruction to the proposed *uniform one-step contraction*. It is not a lower bound on the length of arbitrary polynomial-cap expansions. A permitted expansion can leave a much larger lcm, distribute cancellation over different prime groups, or solve different remainders by different mechanisms.

A product-budget variant emphasizes the separate issue. The number of ordered h-tuples with product <=P is at most P(1+log P)^(h-1). Induct on h using sum_{m<=P}1/m<=1+log P; padding with 1 accommodates shorter lists and changes only a factor h+1. For h=O(loglog p) and P=p^(1-epsilon), this is p^(1-epsilon+o(1)). Thus allowing all small factors but demanding a strict product contraction also misses almost all residues. Shared factors can make an lcm much smaller than this product; that possibility is not excluded by the product bound.

### 4.2 Literature implementation and the missing length estimate

Conlon–Fox–He–Mubayi–Pham–Suk–Verstraëte, *A question of Erdős and Graham on Egyptian fractions*, gives a real implementation of cancellation with small individual denominators. Their Theorem 5 supplies reciprocal sums from a dense subset of [q^delta,2q^delta] modulo a prime power q, with at most q^(delta/2) elements for fixed delta>0. Their Section 4 uses emitted denominators q m and permits new prime powers of size at most 2q^delta. It pays for the total real mass of all corrections and keeps a positive reservoir for completion. This is the relevant new external mechanism read for I205.

It does not give O(loglog b) terms for the desired uniform input class. The theorem's supplied length q^(delta/2) already exceeds that when q is comparable to b and delta is fixed. Letting delta tend to zero with q cannot be inferred from a theorem whose threshold depends on fixed delta. Its real-mass estimate likewise contains a delta-dependent cutoff. Furthermore the procedure must pay for all introduced prime powers, not just the largest along one branch.

Even a hypothetical constant number of terms per largest-prime removal would need an amortized bound for the entire branching collection of smaller primes. A bound on maximum new prime size alone is not that bound: one modulus can have many distinct smaller prime factors. No such amortized O(loglog b) bound, nor a uniform small-delta reciprocal-supply theorem with the required positivity, was proved here.

## 5. Counterexample and quantifier checks

1. The prefix-freezing obstruction concerns a fixed block value; the small denominator of the whole rational can arise from cancellation across blocks. No conclusion about arbitrary replacement follows.
2. The cleanup lemma scales the represented value by 1/K. Section 2's proposition applies the multiset theorem to K times the tail first, so the final value is exactly restored. Applying the lemma to the original a/b without this rescaling would be incorrect.
3. The cleanup result uses at most a square of the pre-cleanup maximum and doubles the number of terms; all choices are made with a single sufficiently divisor-rich multiplier. There is no hidden O(k)-fold squaring.
4. Integer-block counting fixes K across [1,Y]. The different rational t_i class remains open. Independent rational cancellations cannot be replaced by independent integer block counts.
5. Prime contraction counts union over all M<=p^(1-epsilon), not one chosen M. Nevertheless this is still a restriction on the next lcm, not a restriction on the individual denominators allowed in the target.
6. A large lcm is entirely compatible with small individual denominators: e.g. three distinct prime denominators each at most B have lcm equal to their product, potentially of order B^3. No inference from a subquadratic common-denominator obstruction to a b^A individual cap is made.
7. Residue solvability does not ensure positive remainder. The strict negative example above is exact. Distinctness can be handled by the transfer proposition only after a positive bounded multiset construction exists.
8. All positive deductions include every numerator, either explicitly (the transfer proposition) or in their stated residue-counting range. Neither “most numerators” nor fixed-rational asymptotics has been promoted to the target.

## 6. Verdict and contribution gate

No polynomial-cap construction or impossibility theorem for the actual target has been proved. The distinct/multiset equivalence is a technical transfer based on the source's already-paid divisor split and greedy preparation. The block-counting and contraction estimates delimit attempted constructions using elementary divisor counting; they are not substantial advances claimed new to literature. No intermediate statement is nominated to fill the quota.

The precise unpaid tasks are (A) a global, positive polynomial-size replacement of the unrestricted short expansion, or equivalently a polynomial-size multiset construction; and (B) an independent rational-block supply with exact interblock cancellation, or a prime-power absorption argument whose *total* length is O(loglog b) uniformly and whose positivity and individual sizes are controlled. Both routes survive outside the restricted classes eliminated above. Eight accepted findings remain eight; two independent acceptance reviews would still be required for any future nomination.
