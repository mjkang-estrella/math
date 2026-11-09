# Ordinary derivations and failed mechanisms (author only, not independently reviewed)

344875 is in FULLCANDIDATE.md. Everything below carries zero credit and no claim of acceptance.

## 330067 sigma clique covering: complete refutation, recommended ROUTINE, zero

Source: Davoodi-Javadi-Omoomi arXiv:1503.02380v1, Conjecture 5, read. scc = minimum total clique size over clique coverings of the edges.

(a) Trivial literal failure at d=1. K_t(1)=K_t has scc = t (one clique), which is below c t log t once log t > 1/c. The printed statement quantifies over all positive d, so it is literally false at d=1 for every c>0, f. This is a boundary correction and earns nothing.

(b) Substantive failure for large d. A row of a strength-2 covering array CA(N;2,t,d) is a function [t] -> [d], i.e. a clique of size t in K_t(d); the array condition says exactly that every edge is covered. So scc(K_t(d)) <= t * CAN(2,t,d). Francetic-Stevens arXiv:1503.08876v1 Theorem 2 prints d(2,v) = limsup CAN(2,k,v)/log_2 k = v/2, attributed to their reference [7]; a search result attributes this to Gargano-Korner-Vaccaro. So for fixed d and large t, scc(K_t(d)) <= (d/2 + 1) t log_2 t. If the conjecture held with constant c this would force c d^2 <= C(d/2+1) for all d, a contradiction for large d. It is consistent with the source's d=2 result: scc(K_t(2)) ~ t log t matches (2/2) t log_2 t.

The original GKV proof body is UNREAD; the limit is attributed through a printed statement in a later paper. Source Conjecture 8 (the set-system form) is refuted the same way only if its equivalence with Conjecture 5 is checked; I did not check that.

Assessment: complete one-step bridge from a classical covering-array limit. Recommend EXCLUDE AS ROUTINE, credit 0. Unpaid and not claimed: the true order of scc(K_t(d)) with partial cliques allowed, i.e. a lower bound of order d t log t. I attempted an elementary construction with N = o(d^2) log t and failed: block constructions with two symbols per block and random balanced partitions both fall back to d^2.

## 339249 random graph hyperenergy: clause (1) refuted under G(n,1/2), clause (2) unpaid

Source: Arizmendi et al. arXiv:1805.05483, Definition 4.1 and Conjecture 8.1, read. E_G(v) = (|A|)_{vv}; completely hyperenergetic means E_G(v) >= 2 for all v.

Clause (1) reading: "uniform random graph on n points" = G(n,1/2). The claim is false: a.a.s. every vertex has energy at least of order sqrt n.
Proof. A = (1/2)(J-I) + W with W symmetric, entries +-1/2 off the diagonal, and ||W|| <= C sqrt n a.a.s. (standard norm bound, attributed). By Weyl mu := max_{i>=2} |lambda_i| <= C' sqrt n. Then
E_G(v) >= sum_{i>=2} |lambda_i| u_i(v)^2 >= (1/mu) sum_{i>=2} lambda_i^2 u_i(v)^2 = (d_v - lambda_1^2 u_1(v)^2)/mu.
Write u_1 = s e + z with e the normalized all-ones vector; Davis-Kahan with spectral gap about n/2 gives ||z|| = O(1/sqrt n). Then lambda_1 u_1(v) = (Au_1)(v) <= sqrt n/2 + O(sqrt(log n)) uniformly in v, using Hoeffding for (We)(v) and ||W e_v|| ||z|| = O(1). With d_v = n/2 - o(n) uniformly, E_G(v) >= (n/4 - o(n))/(C' sqrt n) -> infinity.
So G(n,1/2) is a.a.s. completely hyperenergetic, the opposite of (1).

Assessment: routine spectral argument, and (1) looks like a slip or an unstated different model. Recommend zero (correction/routine). The conjunction (1)&(2) is refuted through (1) only under this reading.
Clause (2) gap: random d-regular, d>=7, ALL vertices. Kesten-McKay gives typical energy (d/pi)(2 sqrt(d-1) - (d-2) arctan(2 sqrt(d-1)/(d-2))), my hand values about 2.28 at d=7, 2.12 at d=6, 1.94 at d=5. The missing step is a uniform lower bound over every vertex, including those near short cycles: a polynomial approximation of |x| on the spectrum controlled by Friedman-type bounds plus a worst-case analysis of all tangle-free local neighbourhoods. Not done. The fact that d=6 is already above 2 typically but the conjecture starts at 7 suggests the cycle corrections matter.

## 364797 Katona-Xiao: source-own public, zero

Fang-Zhu-Chen arXiv:2409.10129v1 Theorem 1.8 with Remark 2 (read) states that Conjecture 1.5 holds by taking r=2, with both parities discussed there. Theorem proof body not audited. Exact public result, zero.

## 330915 Jarai maximizing configuration for paths: precise gap

Source arXiv:1507.04169v2 read at Section 1. For a path, with N_j the number of rolls in vertices 1..j and S_j = n_1+...+n_j, offline feasibility is EXACTLY S_{j-1} <= N_j <= S_j for all j, because the flow on edges is forced. I re-derived a_*(j;k) as the unique a in (j/k,(j+1)/k) with D(a||j/k) = D(a||(j+1)/k), which matches the printed formula and the source's own description. Also M_n := max p_G is nonincreasing in n by one-step averaging.
Gap: the conjecture needs exponential-order control of the ONLINE value. Inside R_G, p_G = c_G + o(1), and the maximiser is decided by exponentially small differences. Needed: p_G(n x) = c_G-level term minus exp(-n(min rate(x)+o(1))), uniformly, and in particular that the endgame convergence M_n - c_G does not decay more slowly than the balanced rate and swamp it. I could prove only the lower bound on loss from offline infeasibility. A steering lemma from the balanced point to the maximiser at smaller scale fails as attempted, because steering over s steps costs rates of order s rather than n.

## 328539 Stanley faithfulness: precise gap

Source arXiv:1408.1940v1 definitions and Conjecture 2.11 read. Mechanism: for omitted o of the core and large k, o + a_{2^k - sigma} must be covered in S(A); comparing with Lemma 2.13's proof, the covering must use t near the top of the previous block and an s in S(A) of the form lambda-1-o-2g, with g a top gap of the core. So S(A) must meet a specific finite set for each omitted element. That is a necessary condition only. It does not yield every core element below omega, and I found no counterexample by hand. Translation constructions (Theorem 1.5) keep the initial segment and cannot refute it.

## 373109 explicit tournaments: precise gap

Source arXiv:2602.11773 read: directed clique number is min over linear orders of the backedge clique number, so transitive tournaments have value 1 and the literal is not trivial. Idea tried: supermultiplicativity under lexicographic product, which would give n^c from a fixed seed. It fails as attempted: in a transitive subtournament each fibre occupies an interval, and an adversarial order interleaving fibres blocks the product bound; only additive growth (hence log n) follows. Gap: a lower bound on the backedge clique across interleaved fibres.

## 365985 planar spanning-tree growth limit: precise gap (literal only, source unread)

T(n) contains T(a)*T(b) for a+b-1 = n by vertex gluing, and pendant edges give T(n) subset T(n+1). The divisor bound gives |T(a)T(b)| >= |T(a)||T(b)| exp(-O((a+b)/log(a+b))). The de Bruijn-Erdos condition sum g(n)/n^2 < infinity just fails for g(n) = n/log n, and repeated gluing of a fixed T(m) loses order statistics (a q! factor), so Fekete does not close. Gap: an injective or low-collision gluing with o(n) overhead.

## 345483 planar cycles: half only (literal only, source unread)

Lower bound paid: take q = floor(k/(l+1)) segments of lengths p_i >= l+1 summing to k, joined in a ring, each replaced by order n parallel paths. The graph is planar; its cycles have length 2p_i >= 2l+2 or k, and k > 2l for large k; it contains order n^q copies of C_k. Upper bound unpaid: pigeonhole shows a heavily replicated segment has length >= l+1, but converting that into a global count requires a flap-type structure theorem for planar graphs that I did not establish.

## Parked after literal review only (source unread; recorded gaps are not open-status certifications)

345149, 324028, 371954, 354845, 347828, 334450, 328248, 328573, 380420, 368882, 348815. Specific notes in results.json.
