# Annular wavelet classification: unresolved after two routes

Target: Bownik–Rzeszotnik, https://arxiv.org/pdf/1905.08230v1, 20 May 2019, Problem 2.7. Determine frame status for EACH real b in (1/8,1/6], for the integer-translate dyadic system with Fourier transform 1_{(-1,-b) union (b,1)}. Bounds may depend on b but must hold for every L2 function. Neither an isolated parameter nor an assertion that some parameter works answers this classification.

## Source bodies and normalization

The 2019 source defines psi_jk=2^(j/2)psi(2^j x-k) and Fourier transform integral psi(x)exp(-2 pi i x xi)dx. With g=hat f, Fourier-series Parseval at fixed j gives 2^j integral_0^1 |sum_k g(2^j(t+k))1_E(t+k)|²dt. The coefficient phase sign is immaterial to Parseval. Summing gives exactly the inherited pair formula. Write a_j=2^j:

Q(g)=sum_j integral_{a_j(b,1-b)} |g(x)+g(x-a_j)|² dx + sum_j integral_{|x|/a_j in (1-b,1)} |g(x)|²dx.

There are at most three incident terms per frequency almost everywhere, so Q<=6||g||². Prove the identity first on compactly supported g away from zero and extend using this Bessel bound and density. The source problem is positivity of the infimum Q(g)/||g||².

Original actual proof retrieved at https://pages.uoregon.edu/mbownik/papers/16.pdf: Bownik–Weber, *Affine Frames, GMRA's, and the Canonical Dual*, Studia Math.159(2003)453–479, Example2 pp473–477. This uses the angular-frequency Fourier convention and Plancherel factor1/(2pi). Its cutoff beta is 2pi*b in the present convention. Case I proves beta<=pi/4; the paragraph on p474 explicitly leaves pi/4<beta<=pi/3 at heuristic evidence. Case II pp474–475 constructs positive-measure cancellation witnesses for pi/3<beta<2pi/3. Case III pp476–477 explicitly constructs and verifies a dual in the later Riesz range. Thus the original contains a real proof of adjacent ranges, not a proof of our gap. The 2019 question is consistent with the 2003 text.

Current author search retrieved 35 records; annulus/author query retrieved four noisy records. Actual 2025 follow-up https://arxiv.org/pdf/2507.09818v2 (v2 dated20November2025 in returned metadata), *Are MSF wavelets minimally supported?*, concerns a possibly nonmeasurable wavelet set inside orthonormal wavelet support. Its Theorem3.3 uses infinite doubly stochastic matrices; Section2/3 proof bodies do not classify these nonorthogonal annular framelets. This is a scope distinction, not a complete citation clearance. No current public proof-registry head was obtained; denied GitHub routes were not retried.

## Route A: measured anchoring, exact scale-invariant interval coding

Put x=sign(x)2^k u, 1<=u<2. Anchors have u>a=2-2b. On unanchored u in (1,a), the absolute normalized neighbors are

* 4-2u for 1<u<3/2;
* 8-4u for 3/2<u<a;
* 2-u/2 throughout (1,a);
* 2-u/4 when 8b<u<a.

The first two are the two branches of |2-u| renormalized into [1,2); the third comes from |4-u|; the fourth from |8-u|. All actual edges reverse sign and translate by a dyadic number, preserving Lebesgue measure. Normalization is only the coding, not the measure on which coercivity is claimed.

Let S0=(1,a), and remove from Sn every point having an active neighbor outside Sn. The remaining Sn+1 contains precisely the unanchored points with no anchor path of length<=n+1, modulo finitely many endpoints. coding.py uses rational interval endpoints and simultaneous preimages. If Sn became empty, finite degree and measure-preserving edges would give bounded congestion paths to anchors and hence coercivity. This is a universal mechanism, not a graph-ball sample.

The bounded computations did not terminate with empty Sn: at b=1/6 the last recorded stage n18 has10945 cells and positive length44417917/206158430208; analogous nonempty stages occur for13/100,1/7,3/20,4/25,33/200. The known-frame control b=1/8 also remains nonempty at n13. A computation stops when the NEXT stage exceeds12000 cells, so no claim about all subsequent stages is made. Therefore neither small residual length nor existence of remaining points settles coercivity. The needed improvement is an expansion estimate on the residual measured graph, not further anchor reachability enumeration. No parameter classification follows.

Initial implementation used quadratic interval intersections and in-place preimages. It was manually stopped before any result; the corrected run uses sorted linear intersections and simultaneous preimages. No cap was raised. See initial-coding-failure.json. The corrected computation is diagnostics only.

## Route B: positive-measure cancellation, and a decisive failure of the old chain

Conjugate by sign: h(x)=sign(x)g(x). Then each pair contributes |h(x)-h(y)|². Define B(S) for a measurable set S of finite positive Lebesgue measure as the measure of pair edges with exactly one endpoint in S plus the singleton-anchor integral on S; use the exact integral indexing above, counting each pair once. Put H=inf B(S)/|S| over ALL such S.

The exact criterion is H>0 iff there is a lower frame bound. Necessity: test h=1_S, giving Q(sign*1_S)=B(S). Sufficiency: by contraction replace h by |h|. Layer-cake applied to |h|² yields H||h||² <= sum_edges integral ||h(x)|²-|h(y)|²| + anchor integral |h|². Cauchy–Schwarz bounds this by Q(sign*|h|)^(1/2) times (sum_edges integral(|h(x)|+|h(y)|)²+anchor integral|h|²)^(1/2). The latter squared is <=6||h||² by incident-degree<=3. Thus Q(g)>=H²||g||²/6. Truncation justifies layer-cake for every L2 h. This classical measured Cheeger argument is an uncredited reduction; the missing step is proving H>0 or constructing measurable S_n with B(S_n)/|S_n|->0.

We checked the actual 2003 witness, rather than extrapolating point masses. In the present units its centers are ±c_k, c_k=2^(-k)/6, k=0,...,n. Choose any common nonzero L2 profile phi supported in (-epsilon,epsilon), and set g=sum_k[phi(x-c_k)-phi(x+c_k)]. Choose epsilon sufficiently small that all these intervals, and their translated third-edge intervals centered at ±5c_k, are disjoint from each other as needed and the latter avoid the support of g. Such a positive epsilon exists for every finite n because5 is not a power of2.

At b=1/6, the extra scale a_j=2^(-k)=6c_k contributes a pair from c_k+t to -5c_k+t whenever t>0, and from -c_k+t to5c_k+t whenever t<0. These partner intervals lie outside supp g. Therefore the third-scale leakage alone is (n+1)||phi||², whereas ||g||²=2(n+1)||phi||². Hence Q(g)/||g||²>=1/2 for this entire common-profile chain class, including one-sided profiles. Endpoint values at t=0 have zero measure and do not remove this energy. For each fixed b<1/6, choosing epsilon<(1-6b)min c_k makes BOTH sides of each chain site have the extra edge, giving leakage ratio>=1 instead. Boundary contributions can only increase Q.

This rules out the direct extension of the published adjacent-range construction, not all possible L2 witnesses. A new cancellation construction must include the ±5c_k branches with controlled measure and boundary, or use a genuinely different set geometry. Rational cycles without these edges cannot establish nonframe status.

## Stopping status

No full proof, counterexample or parameter theorem is claimed, so there is no PROOF.md. Full interval (1/8,1/6] remains unresolved here. Most useful next work: a weighted expansion estimate for the four-branch normalized coding, with its actual scale Jacobians, or a positive-measure low-boundary construction including every active third edge. Repeating finite graph balls or deleting cutoff endpoints does not supply either.
