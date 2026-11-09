# W033 ratio-sharing review

**Disposition: accept the symbolic identities, the exact unit-slope law, and the two representation-specific cost gates, with the sampling and localization qualifications below. Reject rational duplicate removal as an asymptotic improvement for these implementations. Verified complete factoring improvement: NONE.**

This review covers the full frozen [random-oblique-grid note](W033-ratio-sharing-review-evidence/inputs/research/findings/W033-random-oblique-grid.md) (R, lines 1–77) and [primitive-ratio-sharing note](W033-ratio-sharing-review-evidence/inputs/research/findings/W033-primitive-ratio-sharing.md) (P, lines 1–89). P's raw-versus-accepted correction supplies the missing accounting for R's ambiguous sampling sentence; §2 also refines P's word “only.” The two notes must be read together. Neither source was edited. The [brief](W033-ratio-sharing-review-evidence/brief.txt), [input manifest](W033-ratio-sharing-review-evidence/input-manifest.json), [claim audit](W033-ratio-sharing-review-evidence/claim-audit.json), and [read scope](W033-ratio-sharing-review-evidence/read-scope.json) identify the evidence and boundaries. This is a symbolic prose review, not a numerical experiment, parameter sweep, Lean proof, implementation, or novelty search.

The accepted [parent disposition](W033-ratio-sharing-review-evidence/inputs/research/findings/W032-W033-parent-disposition.md) remains background: axis CRT acquisition failed; the integer derivative-exclusion consumer is correct for arbitrary composites and repeats W006. This round audits the actual random-slope generator and sharing costs. The brief marks W032 label-period work as distinct and LIVE; no W032 review or task-state work was duplicated here. Concurrent context updates are recorded separately below. No delegation, installation, commit, code/Lean/STATE/task-registry edit, or unowned write occurred.

**Conventions and decision scope.** Let H be a positive integer and K a nonnegative integer. For probability claims assume N=pq with distinct primes p<q; write ell=bit_length(N), M=(p-1)(q-1), and d=d_H. The ordinary union bound assumes H<p. The exact tagged law additionally assumes H²<p. These are analytic hypotheses, not parameters revealed to the algorithm. K=0 gives no slope opportunity and cannot meet a positive-success gate. A fixed-H iid batch is the model being evaluated; arbitrary history-dependent selection needs its own conditional law. Costs include failures, raw retries, widths and acquisition. A lower bound for a representation is not a lower bound for factoring or arithmetic circuits.

**1. The generator is N-only; uniform units require a paid sampler.** Given public H and N, sample a raw uniform r in {0,…,N-1}, compute g=gcd(r,N), and record the outcome. Return a verified factor when 1<g<N. If g=N, record a full outcome and retry or exhaust the stated cap; for these canonical residues this is exactly r=0. If g=1, accept u=r. Thus R line 15 needs the wording “proper nonunits are factor exits; full nonunits are retries/exhaustion.” A full gcd is never a factor.

Exact raw uniform sampling can itself be implemented from ell random bits with rejection of integers at least N. Each accepted raw residue is exactly uniform, the acceptance probability is at least 1/2, and the expected number of bit blocks is at most two. Those rejected bit blocks, random bits, comparisons, gcds and any cap failures are charged. An expected-cost rejection sampler is not automatically a worst-case bounded-time random-tape algorithm.

In a virtual sampler that continues after recording nonunit outcomes, the accepted unit sequence is iid uniform on (Z/NZ)*: every unit residue has the same raw probability, and fresh raw blocks are independent. CRT is used only in the proof. It identifies that unit group with F_p* × F_q*, so the two components of each accepted u are independent uniform units. No prime, totient, order, CRT coefficient, or local inverse is computed by the algorithm. Form S_u by repeated addition of u modulo N and T by counting to H. On H<p, each is internally distinct modulo N, although cross-list full matches can occur. Every supplied point and its tag have a construction and storage cost.

Stopping on a discovered factor can censor the observed sequence. Reason about a virtual continued iid stream when proving success, and then couple early stopping to it. In particular, conditioning on previous *slope failures* generally destroys the product CRT law for those past slopes. Fresh draws remain fresh. Coincident slopes occurring naturally in iid sampling do not invalidate its law. Deliberate reuse, deduplication with resampling, sampling without replacement, or adaptive filtering changes the process. P line 69 should be read with this distinction, not as excluding accidental iid repetitions.

**2. Exact raw and accepted sampling ledger.** For one raw residue define

```text
alpha = Pr[unit]         = M/N,
beta  = Pr[proper gcd]   = (p+q-2)/N = 1/p+1/q-2/N,
zeta  = Pr[full gcd]     = 1/N.
alpha + beta + zeta = 1.
```

These counts are symbolic: the proper residues are the q-1 nonzero multiples of p and the p-1 nonzero multiples of q. For a budget of R raw draws, raw-gcd success alone has probability 1-(1-beta)^R ≤ R beta ≤ R(1/p+1/q). This particular union-bound proof counts RAW draws. Applying that proof with K accepted units requires a separate stopping-law or raw-work argument; accepted K cannot silently be declared the number of raw draws.

If S denotes the actual proper-edge probability for a uniform unit (computed exactly in §5 under its stronger hypotheses), a raw trial that also consumes each unit slope has success probability

```text
sigma = beta + alpha S.
Pr[success within R independent raw trials] = 1-(1-sigma)^R.
```

The outcomes are disjoint. Full outcomes are failures/retries, not omitted mass. This law presumes fixed H and complete paid consumption of every processed unit; a different capped or selectively processed transcript needs its own ledger.

For the prescription “continue until K units have been processed, or a proper raw/edge factor has been returned,” with only full raw outcomes retried, exact failure is

```text
Pr[no factor through the K accepted-unit slots]
    = [alpha(1-S)/(1-zeta)]^K
    = [M(1-S)/(N-1)]^K.
```

Delete the zero raw draws conceptually. Each remaining draw is uniform on the N-1 nonzero residues. To finish without success, all K such draws must be units with failed edge tests. In particular, the probability of an initial raw factor before K units, ignoring edge stopping, is

```text
1 - [M/(N-1)]^K
  ≤ K (p+q-2)/(N-1).
```

This is the correct accepted-K expression. There is a useful refinement to P lines 65–67: since (p+q-2)/(N-1) ≤ (p+q)/N = 1/p+1/q (equivalently 2N≥p+q), the same loose numerical upper bound K(1/p+1/q) also holds for the probability of a raw factor before K units, by this different stopping-process proof. P's “applies only” is valid as a warning about the original raw-draw derivation and cost ledger, not as a literal assertion that the numerical probability bound fails for accepted K. If the virtual sampler actually continues through all proper outcomes until K units, the expected number of proper raw outcomes is K beta/alpha=K(p+q-2)/M; that count is a different quantity and can exceed the loose probability bound. The virtual unit-only rejection process needs an expected K/alpha=KN/M raw draws. Actual early stopping can only decrease this cost. For distinct semiprimes alpha≥1/3, so the expectation is at most 3K, a uniform bound requiring no factor knowledge to run the sampler. Alternatively fix a raw cap R and retain exhaustion: in the virtual process the failure to acquire K units is exactly Pr[Binomial(R,alpha)<K]. A further random-bit cap has its own lost probability. These analytic formulae do not supply hidden factors to the program.

For a simultaneous raw cap R and at most K accepted slopes, a safe upper bound for any success is

```text
R beta + K H² (1/(p-1)+1/(q-1)), capped at 1.
```

It suffices to union-bound the corresponding virtual opportunities. Consequently a raw-only constant-success route costs order p raw draws, whereas constant collision success requires KH²=Omega(p). For an uncapped K-slot prescription, its exact law above gives per-slot success at most O(H²/p), since H≥1; the same necessary KH² gate survives after correctly accounting for initial exits. A lucky early factor is not a pathwise Omega(sqrt(p)) lower bound.

**3. Primitive tags give the claimed exact integer identity.** Every pair (i,j) with 1≤i,j≤H has a unique representation (i,j)=(ga,gb), where g=gcd(i,j) and (a,b) is primitive. For a fixed primitive pair, the allowed multipliers are exactly 1≤g≤floor(H/max(a,b))=:m(a,b). Therefore, in Z[U],

```text
Q_H(U) = product_(i,j) (iU-j)
       = C_H product_((a,b) in P_H) (aU-b)^m(a,b),
C_H    = product_(i,j) gcd(i,j).
```

There is no missing factorial: equivalently C_H=product_(P_H) m(a,b)!, because the multipliers attached to a primitive tag are 1,…,m(a,b). Also sum_(P_H) m(a,b)=H². The leading coefficient of Q_H is product_(i=1..H) i^H=(H!)^H, as claimed.

Under H<p≤q, every g and every a lies in [1,H] and is a unit modulo N. Hence C_H is a unit, and for every integer u,

```text
gcd(g(au-b),N) = gcd(au-b,N).
```

Deleting repeated copies preserves the existence of a proper edge in both directions, independently of the gcd of the total product. The algebraic identity holds for every H; the unit/gcd conclusion needs H below the least prime factor (or explicit unit tests). It is not licensed merely by H<N. The same edgewise unit argument works for other composites when that least-prime condition holds, but the semiprime probability formula does not thereby extend.

Define B_H(U)=product_(P_H)(aU-b), retaining (a,b) tags. It has distinct roots over Q: equal positive reduced fractions force the same primitive pair. Its leading coefficient product_(P_H) a is a unit on the promised branch, so its modular degree is exactly d_H. “Squarefree rational-root product” does not assert squarefreeness modulo unknown primes outside the no-alias range. Nor does squarefreeness eliminate cross-prime masking of the aggregate gcd.

For squarefree N, Q_H(u) and B_H(u) have the same prime-divisor support and indeed the same aggregate gcd with N. This alone is insufficient to detect every proper edge: both aggregate gcds can be N when some individual edges are proper. With prime powers, powers of a primitive edge can change aggregate valuations; edgewise existence remains the preserved quantity.

**4. The degree count and constant-factor obstruction are correct, including H=1.** Adopt phi(1)=1. The max-coordinate shell h=1 has the single pair (1,1). For h≥2, pairs with a=h contribute phi(h) possibilities for b, and pairs with b=h contribute phi(h) possibilities for a; the diagonal (h,h) is nonprimitive and introduces no overlap. Thus

```text
d_H = 1 + 2 sum_(h=2..H) phi(h)
    = 2 sum_(h=1..H) phi(h) - 1.
```

Every noncoprime pair has a common integer divisor r≥2. Overcounting such pairs gives

```text
H²-d_H ≤ sum_(r=2..H) floor(H/r)²
        ≤ H² sum_(r=2..infinity) 1/r²
        < (3/4)H².
```

The last strict bound follows without a totient asymptotic: the r=2 term is 1/4, and for r≥3 strict monotonicity gives 1/r² < integral_(r-1..r) x^-2 dx. Summing gives a tail strictly less than integral_(2..infinity) x^-2 dx=1/2. Hence H²/4<d_H≤H². At H=1, d_H=1, C_H=1, Q_H=B_H=U-1, and all assertions remain valid. H=0 is outside the stipulated range and should not be inserted into the totient formula.

The explicit enumeration in P is valid: test gcd(a,b) for the H² positive pairs using O(log(2H))-bit integers, keep the primitive tags, and multiply their modular linear factors. Its cost is O(H² poly(log(2H))) bit work before polynomial construction; using log(2H) makes the H=1 notation harmless. Totients and the hidden p are not needed to enumerate. Any explicitly emitted primitive-root list has d_H=Theta(H²) records; a Farey method may improve enumeration overhead but cannot erase that output. Rational roots b/a need not be constructed at all. If normalized to modular roots, each denominator a must be gcd-tested and inverted at its actual cost. Exact rational-root enumeration, root acquisition, tags, and inversion are not free oracles.

**5. Exact separation law in the no-alias range.** Assume H²<p<q. If distinct primitive tags t=(a,b) and t'=(a',b') have equal ratios in F_p, then p divides D=ba'-b'a. Rational uniqueness makes D nonzero. Since both products lie between 1 and H², |D|≤H²-1<H²<p, a contradiction. The same proof applies at q. Thus each component has exactly d distinct unit roots and each slope hits at most one tag there. In particular d≤p-1 and d≤q-1.

Let A_p and A_q denote a local hit. Uniform-unit CRT gives

```text
Pr[A_p]=d/(p-1),  Pr[A_q]=d/(q-1),  Pr[A_p and A_q]=d²/M.
```

The d² simultaneous possibilities are ordered pairs of primitive tags. Exactly d are the diagonal possibilities where both primes hit the same tag. A diagonal hit makes that primitive edge, and all its original multiples, zero modulo N; every other primitive edge is a unit. There is no proper edge. A nondiagonal hit gives one tag divisible by p but not q and a different tag divisible by q but not p, so it supplies proper edges. A hit at only one prime also supplies a proper edge. This proves

```text
S_H = Pr[a proper original or primitive edge exists]
    = Pr[A_p union A_q] - Pr[diagonal hit]
    = d/(p-1) + d/(q-1) - (d²+d)/M.
```

Equivalently, the three disjoint masses are

```text
only p:        d(q-1-d)/M,
only q:        d(p-1-d)/M,
distinct tags: d(d-1)/M.
```

This derivation explains both subtractions: inclusion-exclusion removes one copy of the both-hit mass d²/M, and then diagonal failure removes d/M. Removing the whole both-hit mass a second time would wrongly discard d(d-1)/M recoverable probability.

In contrast, the probability that the single aggregate gcd gcd(B_H(u),N) is already proper is

```text
T_H = d/(p-1) + d/(q-1) - 2d²/M.
S_H - T_H = d(d-1)/M.
```

The aggregate is full on all d²/M both-hit outcomes. The extra S_H mass therefore requires localization; it is not achieved by a single gcd call.

At H=1 the formula becomes 1/(p-1)+1/(q-1)-2/M, exactly the event that u=1 in just one prime component. There are no distinct-tag double hits. If p=2, the no-alias hypothesis forces H=1; the law is (q-2)/(q-1) and is still valid. Distinctness p≠q is essential. For the symbolic prime-square control N=p², H=1, there are p-1 unit residues congruent to 1 modulo p but not modulo p², among p(p-1) units, giving proper-edge probability 1/p; substituting q=p into the displayed CRT law is not justified.

The strict bound H²<p is sufficient. Equality H²=p cannot occur for positive integer H and prime p. This observation does not extend the formula to larger H: distinct rational tags may then alias in a prime component. The identity, degree bound, unit argument (while H<p), and union bound remain valid there, but the exact tagged count requires recomputation. At H=p a coefficient or denominator may cease to be a unit, so the preceding branch must not be reused.

As a useful symbolic order check, for distinct primes q≥3,

```text
S_H = [d/(p-1)] [1+(p-2-d)/(q-1)],
(1/2)d/(p-1) ≤ S_H ≤ 2d/(p-1).
```

The lower bound uses d≤p-1, so the bracket is at least 1-1/(q-1)≥1/2; the upper bound uses p≤q. Consequently S_H=Theta(H²/p) in this range. This is a probability statement, not a new factoring bound. For K independent accepted unit slopes at fixed H, complete consumption succeeds with probability 1-(1-S_H)^K. Thus K=Theta(p/d) is the analytic constant-success scale. Choosing H or a stopping schedule from unknown p remains an acquisition/scheduling obligation.

**6. Full gcds, coincidence, and paid localization.** The primitive tags preserve all proper edges, but a product tree by itself does not justify blindly following an arbitrary full child until a leaf and declaring failure. A globally zero leaf can mask useful siblings. There are three sound implementations relevant here:

- In the no-alias range, a full B_H(u) comes either from one globally full tag and no proper edge, or from two distinct proper tags and no globally full tag. A retained tagged tree can be descended, evaluating both child products and gcds and returning a proper child immediately. If both children are units it contradicts the parent being nonunit; if no child is proper, continue into a full child. A full leaf certifies the diagonal failure in this special range; otherwise a proper factor is found. With retained subtree polynomials, degrees along one path have O(d) total, so O(d) residue operations and O(log(2d)) gcds suffice for one ambiguous slope. This is a paid bound, not a logarithmic-time evaluation of arbitrary nodes.
- Outside the no-alias range, but still H<p, a simple complete method scans all d primitive linear values. It returns any proper leaf gcd, recording and skipping globally full leaves. Alternatively remove *all* globally zero leaves, paying to find them, and descend a nonunit product of the remaining leaves. An unqualified one-path descent with full leaves retained is not complete. At H≥p, even the edge-unit reduction needs new handling.
- Reconstruct the original H-point row problem for an ambiguous u and invoke the accepted integer consumer. T and S_u are internally distinct here. For each row x=iu, use F(x) if x is not globally in T and F'(x) otherwise. This excludes precisely its full edge, not every leaf value that has ever matched another row. A nonunit excluded row has a proper edge and permits the accepted single descent. With fast monic evaluation the extra cost is soft O(H poly(ell)); the F tree may be shared. This routine also detects that a global-only slope has no proper edge.

No hidden prime is used in these procedures. If A of the K aggregate values are full, a conservative complete bound charges up to A localizations, with A≤K, until success or exhaustion. The source's soft O(H²+K) or soft O(d+K) algebraic budget must not be advertised as the full splitter budget while omitting this work. Derivative exclusion on the row polynomial is already available W006/W033 machinery, not a new generator or novelty result.

**7. Representation and cost audit.** For H<p, each fixed edge iU-j has one root in F_p*, since i and j are nonzero there. Therefore

```text
Pr[any p-edge for a unit slope] ≤ min(1,H²/(p-1)),
Pr[any proper edge among K slopes]
    ≤ min(1,K H²(1/(p-1)+1/(q-1))).
```

The second bound only needs the appropriate uniform marginal for each considered slope; it does not assume independence of H² edge events. For iid slopes the exact law above is stronger in its domain. Since p≤q, the coefficient is O(1/p), and any fixed positive collision success probability forces KH²=Omega(p). This is necessary, not sufficient in ranges where aliases can reduce separation. Treat the raw-exit terms as in §2 rather than merging raw and accepted counts.

For the **explicit point representation**, building F once and supplying all KH indexed queries visits Omega(KH) records, even if equal values later get merged. For H≤sqrt(p), the success gate gives KH≥c p/H≥c sqrt(p). For H≥sqrt(p), even a single H-point trial costs Omega(sqrt(p)). Thus a full batch with constant collision success cannot have sub-sqrt(p) explicit point traffic. Streaming changes peak space, not the number of emitted/processed records. Deliberately computing only a compressed collection of distinct points would require its own generation program and success/cost proof; it is not the stated KH-list implementation.

For the **literal dense polynomial representation**, Q_H has H²+1 slots with nonzero unit leading coefficient; B_H has d+1 slots with the same degree guarantee. Vanishing interior coefficients do not shorten a stipulated dense array. A balanced product construction and monic multipoint evaluation at K supplied residues have soft O((H²+K) poly(ell+log(2+K))) bit envelopes for Q, with H² replaced by d for B after paid tag enumeration. The primitive enumeration is itself order H² up to bit/log factors. Polynomial/gcd/tag storage and localization are extra entries in the full ledger. A literal array and supplied evaluation list have work volume Omega(H²+K); after normalization this remains Omega(d+K)=Omega(H²+K). In either case

```text
H²+K ≥ 2 sqrt(KH²) = Omega(sqrt(p)).
```

Here soft bounds in residue arithmetic are shorthand for a fast polynomial-arithmetic implementation plus bit-width factors. For a concrete conservative bit envelope, let L=H²+K+2 (or d+K+2) and w=ell+ceil(log2 L)+O(1). Pack length-t reduced coefficient arrays in a radix exceeding t(N-1)². Multiplication then operates on O(tw)-bit integers, not constant-width unit-cost integers. With a regular fast integer multiplication bound M_Z, balanced product/remainder trees fit O((M_Z(Lw)+Lw²) log(2L)), plus scalar gcds, generation, reduction, indices, randomness and localization. Query divisors are monic (U-u); reversed-series inversion has constant term 1 and uses G←G(2-AG) without division by 2. No inverse of point differences, unknown-field FFT roots, or interpolation oracle is assumed. Repeated query points are legal. Stored coefficient trees can cost O(L ell log(2L)) bits plus records and multiplication workspace; widths of any explicit unreduced integers must be paid before reduction. R's “soft O(H²+K) arithmetic” is acceptable with this fast-arithmetic qualification, not as a statement about schoolbook polynomial multiplication.

Dense expansion can reduce repeated row evaluation, but rational duplicate removal changes its degree only by a constant factor. This establishes the claimed obstruction for these two fixed-batch representations and this uniform-slope generator. It supplies no circuit lower bound, no expected running-time lower bound for every adaptive/early-stopped implementation, no obstruction to a genuinely implicit aggregate evaluator, and no general all-input factoring comparison. For balanced semiprimes sqrt(p) has order N^(1/4), a familiar reference scale; this review claims no new best known factoring bound. An unknown-factor schedule, small-factor exits, prime powers, arbitrary composites, recursively acquired splits, and all bit costs remain necessary before any complete algorithm claim.

**8. Accepted conclusions and next decisive proof.** The target identities and probability formula pass. The older raw-count derivation is repaired by P and §2's explicit ledger; §2 also shows why P's categorical “only” must distinguish a derivation from the same numerical upper bound obtained by a valid stopping argument. The full-gcd claim is accepted with a paid localization routine as in §6; in the alias range a bare arbitrary descent is inadequate. The dense soft bound is construction/evaluation work, not automatically total factor-recovery work. Accidental iid repeated slopes are already included, while selected or forced repeats need a different law.

The failed assumption is that the H-by-H incidence support can supply order H² distinct chances per slope and be consumed across K slopes at only H+K work by deleting rational duplicates. The normalized support still has Theta(H²) tags. The actual implementations pay KH or H²+K, before any additional sampling and localization cost. No experiment is needed to decide this symbolic gate.

A materially changed computation would need an explicit N-only aggregate evaluator that avoids both record volumes while preserving distinct useful local support, with an actual paid full-gcd decoder and a success law for its generated/selected slopes. Alternatively it would need a different generator with a proved improved separation/cost tradeoff. Neither object is supplied here. The frozen [W007 brief](W033-ratio-sharing-review-evidence/inputs/research/hypotheses/W007.md), Candidate B, already asks for cheaply acquired nested split-polynomial circuits with many distinct roots; its [review](W033-ratio-sharing-review-evidence/inputs/research/findings/W007-split-circuit-review.md), §§8 and 10, leaves scalable root supply and localization paid. Renaming that obligation is not a new algorithm. No historical priority claim or fresh external-source theorem is being made.

The useful next proof would specify the proposed evaluator's operations, constants, widths, parameter acquisition, local distinct support and masking recovery, then compare its total cost and success with these exact ledgers. Degree alone cannot refute that different circuit. Until such a computation and its guarantees are supplied, the disposition is **revised/accepted at symbolic scope; rational-duplicate speedup rejected; verified complete improvement NONE**.

**Later source drift.** The final input check found that R had acquired the explicit raw-versus-accepted sampling correction while this review was in progress. Its other content was unchanged in the captured later version. The initially frozen 77-line R remains the line-reference authority above; the [later snapshots and hashes](W033-ratio-sharing-review-evidence/source-drift.json) and [textual diff](W033-ratio-sharing-review-evidence/source-drift.txt) preserve the changed paragraph separately. That edit is consistent with the paid accounting here; §2 additionally gives the accepted-K stopping law and explains why the same loose numerical probability bound can still hold. STATE and the parent disposition also changed concurrently; those context updates were preserved without auditing their added W032 claims or editing any source. The primitive-ratio target matched its original freeze at the recorded check. No silent refreeze occurred.

**Delivery integrity.** All frozen inputs and owned payloads are indexed in the [delivery manifest](W033-ratio-sharing-review-evidence/manifest.json). It excludes only itself and its detached checksum to avoid a self-hash cycle; the [checksum](W033-ratio-sharing-review-evidence/manifest.sha256) and final terminal output anchor that manifest externally. The [verification record](W033-ratio-sharing-review-evidence/verification.json) records frozen-input integrity, source drift, and scope checks. No project tests were run: only prose/evidence files changed, and no numerical or formal validation is claimed. Hashes establish byte integrity, not mathematical correctness.
