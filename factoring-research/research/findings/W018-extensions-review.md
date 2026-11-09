# W018 extensions: independent degree-gap and norm-one review

2026-10-08 local. **Accept both mathematical cores with the explicit contracts below. Verified new complete factoring bound/improvement: NONE.** The torus result is an expected-time factor-or-order primitive for distinct odd semiprimes. The degree result excludes an intermediate range in one grid-polynomial representation. Neither supplies an improved N-only factoring algorithm.

The [original brief](W018-extensions-review-evidence/ORIGINAL_BRIEF.txt) and [input manifest](W018-extensions-review-evidence/INPUTS-MANIFEST.json) freeze the assignment and twelve source files before this audit. All claims below refer to those frozen versions. The ordinary-unit success proof in W018 is under its own review and was **not** duplicated here. Its bounded-order search is used as a generic finite-group algorithm. W016's completed supplied-progression comparator is context; W014 round two's expanded classifications and algorithmic exclusions are not adopted as authority.

## 1. Degree gap: accepted, including the constant

Let H,d be positive integers, 2<=d<=H/8, and let R have exact degree d, rational coefficients, and integer values at 0,...,H. Write its leading coefficient as a_d. The identity

    Delta_s^d R(0) = sum_(k=0)^d (-1)^(d-k) binom(d,k) R(ks)
                   = d! a_d s^d

follows by applying Delta_s to each monomial: each difference lowers degree by one and multiplies the leading coefficient by its old degree and s. Consequently c=Delta_1^d R(0)=d!a_d is a nonzero integer, even though a_d need not be integral.

Set m=floor(H/d). All km used above lie in [0,H], and m>=H/(2d), since H/d>=8. If |R(j)|<=V on the grid, then

    m^d <= |c|m^d = |Delta_m^d R(0)| <= 2^d V,
    V >= (H/(4d))^d
      >= H^2 2^(d-6)/d^2
      >= H^2/128.                                          (D1)

The middle inequality uses H^(d-2)>=(8d)^(d-2); it also holds at d=2, when both sides of that substitution equal 1. For the last inequality, d^2<=2^(d+1): d=2,3 are immediate, and (d+1)^2<=2d^2 for every d>=3 supplies induction. Thus H=8d and the lowest degree d=2 are included. If H<16 there is no admissible d. The proof needs no real-interval supremum, asymptotic degree restriction, or derivative bound. Only the indicated fine-grid integrality and coarse-grid bounds enter the proof.

For K=qN>0, X>0 and integer H>=0, choose integers c,a with

    |c-K/X|<=1/2,          |a+K/X^2|<=1/2.

On 0<=j<=H the exact remainder is

    K/(X+j) = K/X-Kj/X^2 + Kj^2/[X^2(X+j)].

Hence an integer-valued rational A satisfying |A(j)-K/(X+j)|<=E obeys

    |A(j)-(c+aj)| <= E+1/2+H/2+KH^2/X^3 = V0.             (D2)

Subtracting this integer affine polynomial preserves integrality and preserves exact degree whenever deg A>=2. Therefore **strict** V0<H^2/128 implies deg A<=1 or deg A>H/8. Equality of the two bounds does not imply exclusion. Ties in nearest-integer rounding are harmless.

With N asymptotic to X^2, H asymptotic to X^(3/5), q=O(X^(1/5)), E=O(X^(2/5)), and fixed implied constants,

    V0/H^2 = O(X^(-3/5)+X^(-4/5)+X^(-6/5)) -> 0.

So the stated application, including exclusion of degree comparable to X^(1/5), is correct for sufficiently large X.

For a positive integer stride s, use the nearest integer to -Ks/X^2 instead. The exact remainder is Ks^2j^2/[X^2(X+sj)], giving

    V_s = E+1/2+H/2+Ks^2H^2/X^3.                          (D3)

Apply (D1) in the consecutive **j-coordinate**. No assertion follows for an arbitrary retained subset, or for a negative stride without rechecking the denominator bound. The original sparse-stride claim is accepted with s>=1 explicit.

**Computational scope.** A dense coefficient list through degree d>H/8 has Omega(H) slots. An implementation that reads/materializes that list, or actually performs at least d degree-indexed operations, pays that cost. On the same supplied, properly clipped progression, the accepted product comparator has O~(sqrt(H+1)) modular work under its usual polynomial-logarithmic parameter widths. In the displayed balanced regime H is comparable to N^(3/10), so this rules out a power saving for that dense implementation. For very small H, compare the actual bit costs rather than claiming strict dominance from soft-O expressions that suppress logarithms of N. This is a representation/implementation comparison, not a lower bound on integer-root finding from arbitrary succinct input, early successful factoring, or all polynomial/circuit algorithms. For families the comparator may batch progressions; an artificially fragmented sum of separate square roots is not the stronger W016 comparator.

The example binom(h,H), H>=1, is a rational polynomial of degree H with values 0,...,0,1 on the grid. It correctly witnesses the high-degree escape from a universal bounded-grid claim. **Repair the computational reading of “succinct”:** short binomial notation does not establish a polylog(H)-size arithmetic circuit, cheap negative-offset evaluation, denominator preparation, or root recovery. None is proved or disproved by (D1). No new circuit lower bound is accepted.

## 2. Torus law and square chain: accepted independently

Assume N=pq for distinct odd primes, d a unit modulo N with Jacobi(d,N)=-1, M>=1 given in binary, and integer B>=1. Label the nonsquare component p and the square component q only in the proof. In R=(Z/NZ)[t]/(t^2-d), represent an element by the full pair (x,y). Its norm is x^2-dy^2.

At p the algebra is F_(p^2); conjugation is Frobenius and the norm kernel is cyclic of order p+1. At q choose s^2=d for analysis only: x+yt maps to (x+ys,x-ys), and norm-one elements are (w,w^(-1)), w in F_q^*, a cyclic group of order q-1. These descriptions follow from the cyclic multiplicative groups of finite fields; no hidden square root is needed in the algorithm. Both local norm-one groups have the unique order-two element -1, represented by scalar -1 and zero t-coordinate.

Draw a uniformly from **all** residues 0,...,N-1. The denominator D=a^2-d never vanishes at p. Therefore gcd(D,N) is either 1 or the proper factor q; it cannot equal N. On the unit branch compute

    z = ((a^2+d)D^(-1), 2aD^(-1)),                       (T1)
    norm(z)=1,           z^(-1)=conjugate(z).

Conditioned on this branch, CRT leaves a_p uniform on F_p and a_q uniform on F_q minus {s,-s}, independently. At q the map

    w=(a_q+s)/(a_q-s),       a_q=s(w+1)/(w-1)

is a bijection to F_q^* minus {1}. At p its inverse is a=t(z+1)/(z-1) for z!=1; conjugation fixes this expression, so it lies in F_p. This is a bijection to the norm-one group minus {1}. In **both** components a=0 maps to -1. Thus the parent sampling law is correct, including the split-image correction, and includes global a=0 as one possible failed trial.

For a cyclic group of even order h=2^s u, u odd, the numbers of elements with v2(order)=0 and j>=1 are respectively u and 2^(j-1)u before removing the identity. Afterwards the probabilities are exactly

    P(v=0)=(u-1)/(h-1),
    P(v=j)=2^(j-1)u/(h-1),  1<=j<=s.                    (T2)

The zero atom is <1/2; the largest positive atom is h/[2(h-1)]<=2/3 when h>=4. The inert group always meets this condition. Independence gives

    P(v_p=v_q | D unit) = sum_j P(v_p=j)P(v_q=j) <= 2/3, (T3)

even if q=3 and the split group has order two.

Now form beta=z^M. Use W018's bounded baby/giant search with keys **(x,y)**, identity (1,0), and pair equality; group multiplication, identity detection and sorted comparisons transfer directly. Its early repeated-baby handling and B=1 branch remain applicable. This uses the generic bounded-order procedure, not the ordinary-unit sampling proof. A scalar-coordinate key alone is invalid (z and z^(-1) have the same scalar coordinate).

If the search finds r=ord(beta)<=B, E=Mr is an annihilator of z. Write E=2^ell w with w odd, and let the two orders of z be 2^(v_i)c_i, c_i odd. From ord_i(z)|E we have c_i|w and v_i<=ell; therefore z^w has exact local order 2^(v_i). If v_max>v_min, at stage

    k=v_max-1,         z^(w 2^k)

the larger-valuation component is -1 and the other is 1. Consequently gcd(x_k-1,N) is proper, since N is odd. This stage is between 0 and ell-1, before the element is globally 1. **Test the initial z^w as well as subsequent squares.** Extra odd factors or excess powers of two in E do not spoil the proof. If the initial element is already globally 1, this trial may simply restart.

If ord(beta)>B, the trial has already succeeded with its order output. Thus a failed trial is contained in the equal-valuation event of (T3). There is no conditioning of (T2) on the small-order event, and no claim that beta itself has the same sampling law as z. Nonunit denominators succeed immediately. Independent fresh-a retries, with the same admissible d, therefore take at most three trials in expectation. Outputs are a verified proper factor or z,beta with beta=z^M and ord(beta)>B. This is Las Vegas expected time, not a bounded worst-case number of random bits or trials.

**Why the extra gcd(a,N) restriction is load-bearing.** Symbolically take N=15,d=11. The inert and split norm-one groups both have order four. Conditioning on both gcd(a,N)=1 and gcd(a^2-d,N)=1 leaves a in {2,7,8,13}; all satisfy a^2=4 mod 15. Formula (T1) then has x=0, so z^2=-1 and both local orders are four. The conditional valuation coincidence probability is **1**, exceeding 2/3. For M=4 the powered base is 1 and its annihilator chain has no proper scalar gcd on these retained draws. This refutes transplanting the old conditional law to that sampler; it does not refute a modified algorithm that counts the excluded draws as immediate factor successes. That algorithm needs its own accounting. This is a direct symbolic counterexample, not an executed finite experiment.

## 3. Width, sampling and common-base costs

Let n=bitlen(N), lambda=bitlen(M), and bbit=bitlen(B). Charge reduction/reading of d separately if its supplied representation is wider than n. Pair multiplication costs a constant number of modular operations; norm-one inversion is conjugation; (T1) needs one checked modular inverse. Exact uniform residue sampling via binary rejection has O(n) **expected** bit cost. Thus the “one trial” bound is a deterministic arithmetic bound once the random residue is supplied, and an expected bound when rejection sampling is included.

The bound bitlen(Mr)<=lambda+bbit prices both computing beta and powering to z^w, forming E, extracting its two-adic valuation, and at most lambda+bbit squarings/gcds. Sorted baby/giant lists contain O(1+sqrt(B)) pairs and indices of at most O(bbit) bits. A safe statement is

    expected total bit cost
      = O~((lambda+bbit+sqrt(B)+1) poly(n)),               (C1)
    space = O~(lambda+bbit+(1+sqrt(B))(n+bbit)).

Soft-O here includes sorting/index and arithmetic logarithms of the actual parameters, not an assumption B or M is polynomial in N. Since bbit=O(1+sqrt(B)), this agrees with the parent's displayed scale. The constant expected number of outer attempts includes all failed attempts. A very large numeric M is allowed; its bit length is not free.

If d is not supplied, draw it uniformly modulo N, return a proper gcd when available, retry d=0, and otherwise keep units with Jacobi -1. Among units exactly half have Jacobi -1, by CRT. The probability of either an acceptable d or a proper factor is

    1-[phi(N)/2+1]/N = 1/2+(p+q-3)/(2N) > 1/2.

So this initialization costs fewer than two expected draws, each with polynomial bit arithmetic. It establishes no extension to arbitrary nonsquarefree composites.

For signed exponents v, use a checked scalar inverse or torus conjugation and charge 1+bitlen(|v|). Line parameters, products such as (b+a)j+e, offsets, and giant initializations must retain their actual widths. Negative exponents are valid group operations, not free operations on arbitrarily large integers.

A prescribed common M is powered **once per preparation attempt**, not once per certificate. If M is the product of supplied positive moduli with total binary length L, its output width is at most L; its construction and reading are paid as in W018. Returning one beta gives a base that can be reused where the relevant exponent-transfer identities have separately been proved. It does not automatically prove those identities for every torus certificate or create useful certificates/coverage. Recomputing independent bases for each record would lose the advertised sharing. No unknown order is used to reduce a huge exponent for free.

## 4. Two-dimensional table: accepted sufficient condition, paid dependency

Use slope a in Z, b>=1, and integer H1,B0>=1; this a is unrelated to the Cayley random parameter. For g=(u,z), h=(u,z^(-1)), g'=g^b h^a, the baby key is exactly

    g'^j h^e = (u^((b+a)j+e), z^((b-a)j-e)),
    0<=j<H1, 0<=e<B0.

Set

    T_u=|b+a|(H1-1)+B0-1,
    T_z=|b-a|(H1-1)+B0-1.                                (I1)

Equality of two full keys makes ord(u) divide A=(b+a)Delta j+Delta e and ord(z) divide C=(b-a)Delta j-Delta e. Their absolute values are at most T_u,T_z. Strict global-order bounds ord(u)>T_u, ord(z)>T_z force A=C=0. Hence 2b Delta j=0 **over the integers**, then Delta e=0. The exponent matrix has determinant -2b (absolute determinant 2b). No modular inverse of 2b, generator independence, or componentwise order bound is needed. Cases a=b or a=-b are included. These conditions are sufficient, not necessary.

For T=0 the relevant order inequality is automatic; otherwise use the appropriate factor-or-order routine with B=T and M=1. Equivalently max(1,T) is a harmless stronger target covering all boundaries. The torus routine is established above. The ordinary-unit M=1 routine is the explicit dependency of the separate live W018 review, not independently accepted here. **Conditional on that dependency**, the two acquisitions either factor N or obtain the stated orders with expected cost

    O~((1+sqrt(max(1,T_u))+sqrt(max(1,T_z))) poly(n)),       (I2)

plus actual input/threshold-construction widths. Sequential acquisition suffices; independence between u and z is unnecessary. If a threshold exceeds every possible order, a factor output is the allowed successful alternative.

The table still has H1*B0 explicit entries. Pay those entries, all giants (with integer ceilings), every tag/verification, exponent setup, and all needed tables. Bases can be reused across several supplied slopes by paying acquisition at the maximum respective thresholds, but different slopes generally give different g' and different baby tables. Common bases alone do not merge those tables. Global injectivity here does **not** certify the componentwise uniqueness needed by a different W013-type collision/removal algorithm; that consumer requires its separate checks and proof.

## 5. Disposition and next useful obligation

- **Accepted:** (D1)-(D3), their balanced-regime application, and the dense-input comparison; the exact denominator-conditioned torus law; scalar-gcd separation and the <=3 expected-trial primitive; signed/big-exponent accounting; and (I1)'s global injectivity.
- **Repaired/qualified:** “succinct” binomial notation is not an efficient arithmetic-circuit construction; the dense cost comparison is an exponent comparison in the stated large-H regime, not an unqualified bit-cost comparison for tiny H; sampling time is expected when exact rejection sampling is used; both coordinates are order-search keys; zero thresholds, exponent widths, failed attempts and per-slope table costs are explicit. The scalar half of (I2) remains dependent on its separate live review.
- **Rejected scopes:** unchanged use of the valuation law after additionally conditioning a to be a unit; free dense high-degree processing; free table sharing from common bases; deterministic worst-case interpretation of the retry theorem; arbitrary-composite extension; and any general factoring/circuit lower bound or improved complete factoring bound from these notes.

This accepts a **partial primitive** (factor OR powered order), not a splitter whose every successful return is a factor. W016 separately gives an expected algorithm under a **supplied factor-progression promise**; that promise and its N-only acquisition are not supplied by either extension. No **verified complete bound** is established. W014's original rho/collision bottlenecks and round-two classifications do not become barriers to every algorithm through this review.

No parameter/performance sweep or executable certificate was necessary or run. No solver, Lean, STATE, registry, task-handle file, or other author's report was changed; no install, commit, or recursive delegation occurred. No prior-art/novelty claim is made, so no literature result is imported without verification. These are independent symbolic proofs, not Lean-checked theorems.

The next useful constructive obligation is a priced certificate/domain family or collision computation that saves work **after** common-base acquisition: include coverage, scalar/pair order contracts, error and coefficient widths, giant ceilings, all recoveries, and the matched batched progression or sum-search comparator. A high-degree escape needs an explicit inexpensive representation and recovery procedure; degree alone supplies neither. These remain open computations, not requests to repeat a parameter sweep.

Delivery hashes cover this report and all evidence. [integrity-check.json](W018-extensions-review-evidence/integrity-check.json) records frozen-byte verification and live-source drift. [delivery-manifest.json](W018-extensions-review-evidence/delivery-manifest.json) inventories payload hashes and sizes; [delivery.sha256](W018-extensions-review-evidence/delivery.sha256) additionally hashes that manifest, excluding only itself. The final handoff supplies the hash of delivery.sha256 as the external trust anchor. Integrity checks establish artifact identity, not mathematical truth.
