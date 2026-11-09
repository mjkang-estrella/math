# W018 independent decisive review: common powered-base acquisition

2026-10-08 local / 2026-10-09 UTC. **Accept the factor-or-powered-order theorem and the conditional shared-base application, with the implementation and cost qualifications below. Accept the stronger shared progression-product comparator; for supplied progressions it is deterministic. Verified new complete factoring improvement: NONE.**

The parent’s correlation argument is correct. The small-order branch need not itself have conditional success probability at least one half. What matters is that a failed trial lies in the unconditional equal-valuation set. No counterexample to the stated primitive was found in the proof audit or the single preregistered exact certificate.

This is an elementary extension/composition of established bounded order finding and classical extraction from an annihilating exponent. The primary-source search did not locate the arbitrary-prescribed-power formulation verbatim. That negative search result does not establish priority. Neither this primitive nor its application establishes a new end-to-end factoring bound or a useful sparse-certificate generator.

**Frozen scope and authority.** The reviewed W018 is the complete 8,807-byte parent construction, SHA-256 `9fe64b2d1360ea46371b94572d57e33baac4389feefc89e43b1fa2f09d9569b9`. Its [frozen copy](W018-powered-base-review-evidence/inputs/research/hypotheses/W018.md), the exact [review brief](W018-powered-base-review-evidence/brief.txt), and all local load-bearing sources are preserved. [inputs-manifest.json](W018-powered-base-review-evidence/inputs-manifest.json) identifies the 13 snapshots. The five mandatory instructions/specification files were read; STATE was consulted for context without resuming the parent’s research agenda. W013’s consumer/disposition, W014’s parent disposition and W015’s parent disposition/routing review are the local authorities used. W016 is read only for the transfer interface needed here; its separate full audit and W017 are not duplicated. No shared solver, Lean, STATE, registry, task file or parent hypothesis was edited. No delegation, installation or commit occurred.

**Accepted primitive, including its precise promise.** Let N be odd, composite, and have at least two distinct prime factors. Let M be an arbitrary positive binary integer, and B an integer at least one. There is a uniform classical Las Vegas procedure returning either a verified proper divisor of N or a unit a and beta=a^M mod N with ord_N(beta)>B, in expected

    O~((bitlen(M) + sqrt(B) + 1) poly(log N)) bit work.

This is an expected stopping-time statement with always-correct outputs, not a deterministic worst-case bound. B is a numerical search radius: sqrt(B) can be exponential in the binary input length. No bound on M’s numerical value, factorization of M, factorization of N, group order, or order oracle is required. The high-order branch is optional; when the power image has no element of order greater than B, the procedure instead finds a factor in the same expected bound.

An exact high-order *decision* by completed bounded search suffices. The output pair by itself is not claimed to be a succinct independently checkable order certificate. A verifier can rerun the bounded search at its charged cost. Proper factors have the usual direct divisibility check.

**Exact bounded order search.** Put b=ceil(sqrt(B)). Generate beta^i for 0<=i<b consecutively. If the order is below b, its first positive return to 1 occurs among these babies. Stop there and return that index. This handles every possible duplicate: beta^i=beta^j with i>j implies beta^(i-j)=1, so a positive return to 1 would already have occurred. In particular, no quadratic enumeration of equal-baby pairs is necessary.

Otherwise babies are distinct. Generate beta^(kb), 1<=k<=ceil(B/b), and match them against babies. A match with index i gives h=kb-i>0 and beta^h=1. Ignore h>B. Return the least permitted matched h, or declare order>B if there is none. If the true order r<=B, take k=ceil(r/b), i=kb-r. Then 0<=i<b and this match is in the menu. Every permitted h is a positive multiple of r, so its minimum is exactly r, without factoring h or the group order. For B=1 the sole baby is 1 and the sole giant is beta: the answer is 1 exactly when beta=1. Perfect-square boundaries, r=b, r=B, and a match just outside the radius all obey the same argument.

There are O(sqrt(B)) residues and generated giants. For a deterministic bit-machine implementation, generate and sort both lists and merge them, rather than assuming random-access hash-table operations are constant-time. Distinct babies ensure at most one match per giant, even if giant residues repeat. An additional powering check of a reported r is harmless but not needed for the mathematical exactness proof.

**Extraction from E=M r: every branch.** On a small-order result, a^(M r)=beta^r=1 mod N. Thus E=M r is a multiple of ord_N(a), even when it greatly exceeds that order. Write E=2^s u with u odd and compute x_j=a^(u 2^j), 0<=j<=s, by one binary powering followed by squaring. Check gcd(x_j-1,N) before proceeding past a nonidentity x_j, and stop or retry when x_j=1 if no proper gcd has appeared. Always verify a factor before returning it.

For proof only, write N=product p_i^e_i, and ord_(p_i^e_i)(a)=2^v_i d_i with d_i odd. Because each local order divides E, d_i divides u and s>=max v_i. The local order of a^u is exactly 2^v_i. Consequently

    x_j = 1 mod p_i^e_i  if and only if  j >= v_i.

When the v_i are unequal, j=min v_i precedes the global return to 1 and gcd(x_j-1,N) contains at least one entire prime-power component but not all of them. It is proper. Equivalently the last nonidentity global square-chain element is a nontrivial square root of one. Extra odd factors in E preserve each 2-power order; extra powers of two add terminal redundant stages and cannot erase the earlier separation.

For completeness, at an odd prime power the reduction kernel from units mod p_i^e_i to units mod p_i is a p_i-group. A 2-power-order element reduces to 1 only if it is already 1. Thus when all v_i are equal, every gcd in this particular chain is either 1 or N: a partial p-adic gcd cannot create an unaccounted exception. When s=0 every v_i=0 and a^u=1 immediately, so retry is correct. The always-present a=1 trial is another legitimate retry, not an invalid factor.

The implementation must inspect the chain, not just gcd(a^(E/2)-1,N). That single final exponent can be useless when E has surplus factors of two. For example, algebraically N=15, a=2, M=8, B=1 gives E=8 and a^(E/2)=1 mod 15, while the chain starting from a^1 finds gcd(4-1,15)=3. This is a proof illustration, not another executed experiment. The parent already specifies the full chain; the clarification prevents a faulty implementation shortcut.

**Exact success probability; no conditional-independence assumption.** Draw a uniformly from {1,...,N-1}. If gcd(a,N)>1, it is a proper factor because 0<a<N. Conditioned only on being a unit, CRT makes the local components independent uniform units. The group at an odd prime power is cyclic of order p_i^(e_i-1)(p_i-1), whose 2-part is 2^s_i with s_i=v2(p_i-1)>=1. Counting in its cyclic 2-part gives

    Pr(v_i=0)=2^(-s_i),
    Pr(v_i=t)=2^(t-1-s_i),  1<=t<=s_i.

For two distinct components and h=min(s_1,s_2), independence yields

    Pr(v_1=v_2)
      = 2^(-s_1-s_2) (1 + sum_(t=1)^h 4^(t-1))
      = (4^h+2)/(3*2^(s_1+s_2)) <= 1/2.

The inequality follows from s_1+s_2>=2h and h>=1; equality is possible when both s_i=1. Let F mean “unit trial retries” and C mean ord_N(a^M)<=B. For the full chain just described,

    F = C intersect {all v_i equal}.

In particular F is contained in {v_1=v_2}, regardless of its correlation with C. Hence Pr(F | unit)<=1/2 and

    Pr(trial fails) <= phi(N)/(2(N-1)) <= 1/2.

Fresh independent trials give expected trial count at most two and Pr(more than k trials)<=2^(-k). There is no valid inference that Pr(F | C, unit)<=1/2. The exact certificate below actually contains a case where this conditional probability is one, and another where it is two thirds.

Do not sample only from the M-th-power image and attempt to apply the same valuation law to beta. The required uniform variable is the original a, and extraction uses a with its annihilator E. The map a to beta may destroy all its 2-part and need not preserve a useful distribution on the original unit group. Independence is used only for the original CRT components.

**Sampling, preprocessing, and bit/space accounting.** Use k=ceil(log2(N-1)) random bits to draw z in [0,2^k), reject z>=N-1, and set a=z+1. Acceptance probability exceeds one half. This gives exact uniformity at expected O(log N) bit work per accepted sample and does not condition away nonunits. Rejection draws and arithmetic retries are both charged. As usual for this Las Vegas theorem, unbiased independent random bits are the randomness model; a fixed pseudorandom generator is not a proof substitute.

The primitive’s promise needs no primality test. To cover arbitrary *composite* inputs in its base-acquisition role, first return 2 for even N. Test perfect powers by exact integer k-th roots for 2<=k<=bitlen(N). Whenever N=c^k with 1<c<N, c is already a proper factor, whether or not c is prime. After these tests, an odd promised composite that remains has at least two distinct prime factors. Repeated-squaring comparisons capped above N and integer bisection implement these tests in polynomial bit time and linear-sized arithmetic workspace. A conservative O(n^5) preprocessing allowance, n=bitlen(N), is more than sufficient with elementary arithmetic. No primality oracle is hidden here. If the input contract includes primes and demands termination for all B,M, a primality/prime-output branch is separate; the stated theorem does not promise that.

Here is a deliberately loose explicit realization of the primitive bound. Let ell=bitlen(M), h_B=bitlen(B), T=min(B,N-1), and H=ceil(sqrt(T)). Capping the search at T is a valid optional implementation completion since every unit order is at most N-1; it also keeps all search indices O(n) bits. If B>N-1 the large-order branch cannot occur. The finite certificate tests the parent’s uncapped search instead, including a B>N case.

After reading all inputs, the capped implementation has expected bit cost bounded by

    O(n^5 + h_B + (ell + n + H + 1) n^3),

where the n^5 term is omitted on the original promise if preprocessing is skipped. This is a conservative existence bound, not a claim of sharp logarithmic factors. Modular products have O(n)-bit residues. Each of a^M and a^u costs O((ell+n)n^2) using binary powering and schoolbook modular arithmetic. A found r<N has O(n) bits, E=M r has at most ell+n bits, and multiplying by r costs O(ell*n) with unbalanced schoolbook multiplication. A single scan finds its odd part; there are at most ell+n square-chain steps and gcds. Avoid copying an ell-bit exponent at each scanned bit. Sorting and merging O(H) O(n)-bit residue/index records costs O(H n log(H+1)), within the displayed envelope; gcds fit the conservative n^3 allowance. Exact square roots, sampling, control, reading, and output are covered. No operation has cost proportional to the numerical value M.

Reusing buffers across retries gives

    O(ell + h_B + H*n + n) bits of storage

up to ordinary sorting-workspace conventions; elementary multiplication, division, gcd and root comparisons can use O(n) bit buffers. Retaining every trial is unnecessary in the mathematical algorithm. Without capping, store the extra log B-bit indices explicitly; the parent’s soft space notation absorbs their logarithms. Since h_B=O(sqrt(B)+1), the explicit cost implies the stated soft bound. A uniform per-accepted-trial arithmetic bound together with the sampling expectation and expected at most two trials justifies the expected total; it is not an empirical timing estimate.

**Shared progression-base application.** Assume K>=1 supplied certificates with positive progression strides m_i, and let L_m=sum bitlen(m_i). A balanced product tree constructs M=product m_i with bitlen(M)<=L_m in O~(L_m) bit work using fast integer multiplication, including reading the input; an lcm or factorization of the strides is unnecessary. The tree’s space/construction costs are also paid. M=1 when all strides are one causes no exceptional case.

Apply the primitive once to this common M, reusing it across retries. For any covered prime p=1+m_i*t dividing N, a is a unit mod p and

    beta^t = a^(M*t) = a^((M/m_i)*(p-1)) = 1 mod p.

The quotient M/m_i occurs only in this proof; the consumer need not construct K such quotients or K powers of a. If e_i=A_i(t)-q_i*(N/p) and D_i=A_i(0)-q_i*N, then

    D_i-e_i = A_i(0)-A_i(t)-q_i*(N-N/p)

is divisible by t. Therefore beta^D_i=beta^e_i mod p for the same true integer error e_i. Neither the error radius nor the searched exponent is multiplied by M or M/m_i. A_i(t)-A_i(0) being divisible by t holds at every degree. The powered-base exponent is independent of the degree; certificate reading, coefficient arithmetic, recovery degree and root isolation are not thereby degree-independent costs.

Before removing global matches, retain W013’s component-order checks gcd(beta^j-1,N), 1<=j<B. The global guarantee ord_N(beta)>B ensures none is N. Thus any nonunit check returns a proper factor; if all are units, ord_p(beta)>=B for every prime divisor p of N. At B=1 there are no checks and the needed uniqueness for a one-element baby table is automatic. A covered progression with t<B will force a factor during these checks rather than supply an invalid collision table.

On the consumer branch use one baby table, one inverse of beta for signed exponents, and one common stride beta^(-B). Each certificate’s initial giant is computed as a power of beta with exponent D_i+E_i. Its cost is its actual exponent bit length; it has no mandatory extra factor bitlen(M). If D_i or coefficient encodings themselves have large widths, those widths must still be charged. “One huge-exponent setup” does not mean “one exponentiation total.”

For S=sum_i(2E_i+1), the number of tagged giants is

    G=sum_i ceil((2E_i+1)/B) <= K + S/B.

Thus the added input/acquisition/list envelope is expected

    O~(L_m + K + B + S/B),

with the poly(log N) arithmetic conversion, the input/exponent/coefficient widths, and **all** W013 consumer costs retained. More explicitly, add certificate acquisition/coverage, O~(L_m), the primitive’s expected bit cost, the B+G tagged list and polynomial-evaluation costs, each initial giant powering, each associated global-match recovery/root computation, and localization. The primitive’s sqrt(B) is absorbed by the consumer’s B. For fixed degree and the already stipulated polynomial bit widths, this is the advertised soft envelope; for growing degree it is not a degree-free full bit bound.

Use the W016 recovery polynomial (1+m_i*T)(A_i(T)-e')-q_i*N under its existing guards, and retain every tag before global-match deduplication. This review does not re-prove W016’s separate approximation/coverage or root-recovery audit. It checks the common-base substitution at that interface. W014 A/B can likewise use the primitive where a common supplied exponent M is already part of their accepted contracts; their normalization, carry-image, acquisition and usefulness obligations remain in force. Nothing here extends W014 C or settles W017.

**The stronger equal-information comparator is valid, and deterministic.** Suppose the same supplied data specify K ordinary integer progressions a_i+m_i*j with m_i>=1. First clip their integer index intervals to candidate values 1<x<N, paying the divisions, input widths and endpoint arithmetic. Empty progressions are discarded. Let ell_i be each remaining length, and L=sum ell_i, counting overlaps and repetitions as occurrences. This is the comparator’s L, not L_m or a deduplicated count supplied for free.

Check gcd(m_i,N). A value strictly between 1 and N is already a factor, for wide as well as small strides. If gcd(m_i,N)=1, compute m_i^(-1) mod N and z_i=a_i*m_i^(-1) mod N (with a_i the clipped initial term). Then

    product_(j=0)^(ell_i-1)(a_i+m_i*j)
      = m_i^ell_i * product_(j=0)^(ell_i-1)(z_i+j) mod N.

Normalization changes only the evaluation points. For width w the single polynomial F_w(Z)=product_(j=0)^(w-1)(Z+j) serves every unit stride. The unit multiplier m_i^ell_i may be omitted for factor detection; if actual product values are wanted, pay K binary exponentiations with their actual ell_i bit lengths. There is no division by a nonunit factorial or by differences of evaluation points.

To see the total bound, split each ell_i into consecutive power-of-two lengths. Since clipping and positive strides give ell_i<N, there are O(log N) length groups and O(K log N) piece records. For a group of v pieces of common length ell=2^j, take w=ell if v>ell; otherwise take the largest power of two at most sqrt(v*ell). Then w divides ell exactly. Build F_w and evaluate it at all Q=v*ell/w block starts by monic product/remainder trees over Z/NZ. The group costs

    O~(w+Q+v)=O~(v+sqrt(v*ell)).

The capped w=ell case costs O~(v), so no exceptional large-v term is lost. Repeated normalized starts are permitted. Summing groups and using Cauchy–Schwarz gives O~(K+sqrt(L)) modular work. These are the W015 monic ring operations, valid with zero divisors; no field interpolation is imported. Deterministic fast polynomial/integer arithmetic supplies the corresponding bit bound with the actual residue/index/input widths. Inversions via extended gcd are deterministic. Expected time is not needed for this comparator on supplied progressions.

Stride gcd=N needs an explicit branch, not a declaration that it is a proper factor. For positive m_i divisible by N, clipping leaves at most one term, since m_i>=N. Check that leaf directly. More generally a positive stride at least N leaves at most one clipped candidate whether or not it is invertible, so it may be handled before normalization. A gcd=N stride with an un-clipped arbitrary residue progression would not justify ordinary-leaf recovery; the interval-of-integers/clipping contract is essential.

Multiply the already evaluated progression products and take their gcd. A unit result excludes all listed candidates as factors; it is not a factoring success or a coverage proof. A proper gcd returns a factor. For gcd=N, scan/descent through the O(K) retained progression values to find a nonunit product, and bisect that progression’s index interval. Evaluate one half with the same single-progression block method, returning a proper gcd as soon as it appears. A unit left half directs the search right; a full left gcd directs it left. The total recomputation is O~(sqrt(ell_i)) along the geometrically shrinking path, bounded by O~(sqrt(L)). No inverse of a nonunit product is used. At a leaf the original integer lies in (1,N), so its nonunit gcd is necessarily proper, including for repeated prime factors. Only one such successful recovery path is needed.

Accordingly the cost is O~(K+sqrt(L)) modular work plus supplied-input processing and bit widths, gcds, clipping, output and recovery as specified. The family must cover a factor if the comparator is to find one. Both methods must pay for obtaining the same progression restrictions. A comparison to sum_i sqrt(ell_i) is too weak. W018 removes a base-acquisition obstruction, but it supplies neither S substantially smaller than L nor an acquisition/coverage theorem producing useful certificates at that cost.

**Primary prior art and novelty disposition.** The substantive external sources used are primary research papers; secondary search hits are not mathematical authorities for this review. Search queries and returned reading extracts are retained in the evidence directory, and source bytes/URLs/hashes are in [primary-sources/manifest.json](W018-powered-base-review-evidence/primary-sources/manifest.json).

Shor’s factoring-to-order reduction, section 5 (printed pp. 15–16 of the retained version), explicitly analyzes the local 2-valuations for arbitrary odd prime-power CRT components and gives constant success probability outside prime powers. W018 uses its classical extraction mechanism, replacing exact order of a with the accessible annihilator M*ord(a^M). The latter extension and its proof are supplied above; no quantum computation is involved. [Shor, primary paper](https://arxiv.org/pdf/quant-ph/9508027v2).

Ekerå discusses classical postprocessing with order multiples and its relation to Miller, as well as elementary perfect-power preprocessing, in sections 1 and 3.2. His complete-factorization algorithm and probability theorem are different and are not imported here. These passages provide context for the standard annihilator technique, not a verbatim reference for W018. [Ekerå, 2021](https://link.springer.com/article/10.1007/s11128-021-03069-1).

Harvey’s sections 2.2–2.4 and Algorithm 4.2 provide the existing polynomial-evaluation, large-order, and shared-collision consumer context already acknowledged by W013. The older Proposition 2.7 has a lower restriction on its order target and concerns an unrestricted base. It should not be restated as the newest available acquisition theorem or as a theorem about prescribed M-th powers. [Harvey, exponent-one-fifth algorithm](https://arxiv.org/html/2010.05450).

The current relevant update is Harvey–Hittmeir, version 2 dated 5 June 2026. Theorem 1.1 gives a **deterministic** factor-or-order>D algorithm for N>=3 and 1<=D<N-1, without the older lower threshold. Its time is O(sqrt(D)*log(D)*log(N)/sqrt(log log D)), with their small-D conventions. Lemma 2.1 explicitly provides an exact bounded-order decision. The theorem chooses an unrestricted unit; it does not demand an M-th power of a known preimage. Raising its output to M can reduce its order, so it does not directly discharge W018’s output requirement. Conversely W018’s expected bound does not improve that deterministic theorem. [Harvey–Hittmeir, 2026 v2](https://arxiv.org/html/2601.11131v2).

The bounded search and square-chain ingredients are established. Combining them with E=M r and the failure-set inclusion is a straightforward extension; product-exponent sharing and stride normalization are elementary algebraic consequences. No checked source was found stating the entire arbitrary-M primitive or this W016 application verbatim. This is a bounded literature check, not a claim that such a statement is absent from all literature. **Accept correctness; do not assign novelty, priority or a complete-improvement label.**

**Single preregistered exact certificate.** The [preregistration](W018-powered-base-review-evidence/preregistration.md), [fixed cases](W018-powered-base-review-evidence/cases.json) and [code](W018-powered-base-review-evidence/certificate.py) were hashed before execution in [preregistered-manifest.json](W018-powered-base-review-evidence/preregistered-manifest.json). A syntax-only AST parse preceded freezing; no candidate or fixture execution did. Exactly one run was made. [run-record.json](W018-powered-base-review-evidence/run-record.json) records its observed exit 0 and no timeout. [certificate-output.json](W018-powered-base-review-evidence/certificate-output.json) retains every per-base result and an empty failed-check list; stderr is retained separately.

The 21 fixed cases examined all 684 choices a in 1,...,N-1, including 394 unit records. They passed 3,287 checks with 16,370 charged events against a total 20,000-event limit. The wrapper elapsed time was below 60 seconds. There were 290 initial-gcd factors, 172 chain factors, 95 high-order outputs and 127 legitimate retries. The 127 retries are not deleted trials or failed assertions. The program uses known fixture components only in its separate naive-order reference checker; candidate trial(N,M,B,a) receives neither factors nor orders. The certificate is not registered as a solver.

Exact failed-unit fractions (all unit choices are the denominator):

- N=15, M=1: B=1 gives 1/8; B=2,3,4,5,9,16 each gives 1/4.
- N=21, M=1: B=5 gives 1/3; B=6,7 each gives 1/2.
- N=45, M=1: B=5 gives 1/6 and B=6 gives 1/4. M=12,B=1 and M=3,B=2 each give 1/4.
- N=63, M=6,B=1 gives 1/2; N=75, M=20,B=1 gives 1/4.
- N=65, M=1,B=12 gives 3/8; N=105, M=1,B=2 gives 1/24.
- N=15, M=2^64+4,B=1 gives 1/4, with the 65-bit exponent actually processed by the candidate powering routine.
- Excluded controls: N=9,M=6,B=1 and N=25,M=20,B=1 each give fraction 1. The probability theorem is explicitly not applied to them; their nonunit inputs still return initial gcd factors.

For N=15,M=1,B=1, every small-order unit fails but only one eighth of all units fail. For N=21,M=1,B=5, failure conditional on small order is 2/3 while the unconditional unit failure fraction is 1/3. These show concretely why the proof must use the failure-set inclusion. They were fixed before the run, not selected through a subsequent sweep.

Read-only aggregation of the retained run records finds 45 duplicate-baby branches, 35 records with multiple permitted annihilator matches, 25 with an out-of-radius match, 29 small-order cases with s=0, and 58 with surplus twos in E, including 18 successful extra-twos chain extractions. [coverage-from-retained-output.json](W018-powered-base-review-evidence/coverage-from-retained-output.json) records this bookkeeping; it is not a second candidate run.

The charged-event definition includes reference arithmetic and sampling-map visits but is not a bit-machine model. Comparisons, ordinary bookkeeping, fractions and logging have no calibrated event costs; all are within the wall budget. No timing, scaling, asymptotic, sampler-quality, end-to-end consumer, fast-polynomial implementation or performance claim follows from this certificate. The proof establishes the mathematical bound. The certificate only checks its fixed small instances and branch implementation. No shared-code test suite or Lean build was rerun for this isolated evidence script; neither shared implementation nor formal proof is added.

**Disposition and next mathematical obligation.** Accept the primitive as an expected factor-or-powered-order theorem on its stated domain. Accept the common-product exponent and true-error table sharing under the full existing consumer contract. Accept variable-stride normalization and the deterministic shared O~(K+sqrt(L)) comparator after clipping and nonunit handling. The required completions are explicit sampling and preprocessing costs, a full square chain, deterministic list matching when claiming bit bounds, actual exponent/degree widths, and the gcd=N stride branch. None changes the parent’s principal mathematical conclusion.

Reject deterministic reinterpretations of the primitive, applying the half-failure theorem to prime powers or conditional small-order samples, replacing the square chain by only the final half-exponent, ignoring K/ceiling/root/width costs, comparing against separate per-stride square roots, and inferring certificate supply or an end-to-end speedup. The remaining research target is a paid progression/certificate family with coverage and small total true error that beats the normalized shared product comparator including all acquisition and recovery costs. W018 resolves the powered-base acquisition obligation; it does not provide that family. **All new complete improvement labels remain NONE.**

Delivery file sizes and SHA-256 values are enumerated in [delivery-manifest.json](W018-powered-base-review-evidence/delivery-manifest.json); [delivery.sha256](W018-powered-base-review-evidence/delivery.sha256) additionally hashes that manifest. The manifest deliberately excludes itself and its checksum inventory to avoid self-reference. [verification.json](W018-powered-base-review-evidence/verification.json) records frozen-input/code integrity and any live-input drift at handoff. Frozen conclusions are not silently replaced by concurrent parent changes.

The handoff comparison found changes only in STATE and W014’s parent disposition among the frozen inputs. Their current copies and diffs are retained separately. The W014 addition says C round two completed, withdrew the N^(2/7) calculation, and still awaits full parent intake; it changes neither the accepted A/B interface used here nor this review’s refusal to certify C. W018 itself and the other load-bearing mathematical sources were unchanged at that comparison.
