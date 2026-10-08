# H018 hybrid mechanisms: raw Grok report

Unverified initial report. In particular, collision duty-cycle rates, fibre
obstructions and factor-base recovery claims require independent review.
No conclusion below is an accepted lower bound or complete-work result.

No complete-work gain over negation-aware rho. Three exact gates close the natural versions of a second walk image, a rational fiber quotient, and a Weierstrass differential shortcut. One AP-Semaev lattice schedule stays on the wrong side of the square-root ledger.

Baseline used here: one full scalar on an ordinary prime-field curve of prime order q, with only the negation automorphism charged in the reference. Working single-target cost is about √(πq/4) group additions. Setup, memory, misses, verification, and extraction are extra. Verified improvement remains **NONE**.

## 1. Side images lose at every duty cycle

Closed. This is stored-key search, not a rho quotient.

Negation speeds rho because the step descends to x-classes. A second image σ does not do that. Inserting σ(P) into a table does not make the next step equal f(σ(P)), so the walks do not merge. The only detection policy that can see σ is: every step, hash the canonical class of P and of σ(P), and store both keys. Memory is then Θ(T) keys after T steps, the same regime as stored-point birthday search.

Under that policy, and under the same birthday heuristic the negation baseline already uses (this is not a proved hitting time, and pair counts are not a stopping law): each step emits r = 1+δ expected new classes and costs 1+δc baseline steps, where the extra image is computed with probability δ at incremental cost c. Sample count scales by 1/√(1+δ). The cost ratio is

(1+δc) / √(1+δ).

If c ≥ 1/2 this ratio is strictly greater than 1 for every δ > 0. Squaring gives the identity δ(2c−1) + c²δ² ≥ 0. Equality holds only at δ = 0.

So a rare doubling probe loses as well as an always-on one. H017's always-on x-only doubling (about 4M+2S against a 5M+S affine add, ratio ≥ 0.8) is the special case δ = 1. The reopen condition is an explicit second point, with a nonzero tracked coefficient of k, whose incremental multiplication count is strictly below half the matched step, together with the hash and label-update ledger.

The obvious reuse still misses that bar. After an affine add of a known jump J, δ⁻¹ and x(P+J) are already known. The differential identity then gives x(P−J) with 3M+1S plus one doubling. Against the Bernstein–Lange–Schwabe batched affine ledger of 5M+S per add (one inversion per batch), that increment is at least half a step for every squaring-to-multiplication ratio ≥ 0. Label recovery would be the subtraction relation on (a,b), but the arithmetic already loses, so recovery is not reached. A heavier baseline step can be resubmitted only with its own ledger.

Assumption used as a gate, not as a theorem about all coordinate methods: emitted classes behave like the usual rho samples. A detector that is not "hash these explicit keys" is outside this gate.

Cheapest falsifier: exhibit a formula with c < 1/2 on the 5M+S ledger, including canonicalization and the extra hash. No curve run is required to reject the maps above.

## 2. A rational fiber does not transport full-range labels

Closed for rational images. Not a generic-group bound, and degree is not being used as runtime.

Let f be a non-constant rational function on E and n an integer not divisible by the characteristic. Then deg(f∘[n]) = n² deg(f). The only way f([n]P+T) = f(P) identically is n = ±1. For n = 1 and T rational of order q, translation is transitive on E(F_p), so f is constant. For n = −1, f(−P) = f(P) is the negation quotient already in the baseline (the x-coordinate).

A partial coincidence does not escape this. If f∘[n]−f is not identically zero, it has at most deg(f∘[n])+deg(f) zeros. It cannot hold on a positive-density set without being the identity, which the degree forbids for |n| > 1.

Consequence for full-range walks: coefficients (a,b) diffuse, so a geometric coincidence is not a low-degree equation in k. The only recovery that stays O(1) field arithmetic in the tracked coefficients is an affine relation R = [n]P+T. The only such relation compatible with a rational fiber of small degree is negation. Hashing doubling slopes, chord slopes to a fixed jump, or any other rational image can increase collision frequency by at most the fiber size, and those extra collisions do not yield a linear equation for k.

This is narrower than the H017 branch-coverage count. It does not forbid bit tests that explicitly apply a known affine map, implicit detectors that are not functions of one point, short-coefficient interval search, or index calculus whose unknowns are factor-base logs rather than walk coefficients.

Cheapest falsifier: a rational f and an explicit (n,T) with |n| > 1 such that f([n]P+T)−f(P) is the zero function on one ordinary prime-order curve. One symbolic remainder is enough.

## 3. Differential x-arithmetic does not drop into this curve model

Closed as a solver reduction.

These curves have prime order, so E(F_p) has no point of order 2 or 4. There is no Montgomery model and no twisted Edwards model over F_p. Their x-only differential adds are not available. A Weierstrass x-only step still needs x(P−Q). A rho jump P ↦ P+J_{h(x)} does not carry that difference.

An order-2 recurrence P_n = P_{n−1}+P_{n−2} does carry it, and the labels follow an integer Fibonacci recurrence, which is nonzero modulo q for many seeds. The collision space is pairs of points, size Θ(q²), so the birthday sample count is Θ(q), not Θ(√q). No reduction of that recurrence to a function on the negation quotient was found. Until there is one, the cheaper multiply count is not a full-solver cost.

Storage of (x_n, x_{n−1}) does not coalesce anything with a one-point walk: equality of one x-coordinate is not equality of states.

Cheapest falsifier: a state of size O(q) on the negation quotient, updated by a Weierstrass differential add, with a label map whose coefficient of k is nonzero and whose per-step multiply count is strictly below the 5M+S ledger. Specifying the recurrence without the state-size reduction does not meet this.

## 4. AP factor base plus a (2,2) Semaev equation sits at √q before lattice cost

Not a predicted win. Kept because the polynomial is explicit and the ledger is a different object from the H017 padded box and from SP3.

Fix public u, δ ≠ 0 and an integer box 0 ≤ i,j < L, L = q^β. Factor-base x-coordinates are the arithmetic progression u+iδ. For a trial point R = Q−[a]G, Semaev's S_3(x_1,x_2,x(R)) = 0 with x_1 = u+iδ and x_2 = u+jδ expands to a bidegree-(2,2) polynomial. The monomial i²j² has coefficient δ⁴, from (x_1 x_2)², and does not cancel. A solution with a point on the curve and a consistent sign gives

±P_i ± P_j ± R = O,

and the tracked coefficient of k is the coefficient in R, hence nonzero. Verification is one scalar multiplication. That is the whole recovery path. There is no walk to coalesce.

Group-step count to manufacture the trials, taking consecutive a so each trial is one addition, is q/L² = q^{1−2β}, because a random R decomposes into the box with probability about L²/q. Beating √q in group steps needs β > 1/4. The classical univariate Coppersmith ceiling for a degree-4 equation is a root smaller than about p^{1/4}. At β = 1/4 the group-step count is already √q, and every surviving trial still pays a lattice whose dimension is at least the 9 monomials of bidegree (2,2). That lattice is not free, and at β = 1/4 there is no sparse trigger: the degree-4 equation is the test.

A bivariate bound that only reaches 2β ≤ 1/2 stays on the same side. This does not say every small-root lattice fails. It says this equation, with this box, does not enter a winning region under those ceilings. Degree 4 is the shape of the equation, not a claimed runtime.

Distinction: H017's padded box was an artificial module whose determinant missed a collector's root size. SP3 is a trilinear point relation with a missing sub-n^{3/2} detector. Semaev / McGuire–Mueller / Amadori–Pintore–Sala collect relations by Gröbner or summation systems and, on the analyses already in the project record, do not beat square root on prime fields. This card uses neither a Gröbner basis nor a claim of those exponents.

Cheapest falsifier: the Newton polygon of this explicit polynomial under a cited Jochemsz–May or Blömer–May bound. Kill it if every bound that actually applies has β ≤ 1/4, or if the LLL bit-complexity at the first admissible β already exceeds √(πq/4) field operations. Reopen only with a proved root bound β > 1/4 and a complete lattice ledger below that reference. No curve search is informative before that bound exists.

## Source limits

Repo records read: RESEARCH_LOOP.md, RESEARCH_TEAM.md, research/STATE.md, the H013 collision baseline, the H015 preprocessing baseline and ranked shortlist, the H016 ranked shortlist, the H017 briefs, and the H017 hybrid disposition. H001/H002 proposal raw reports were not read. No other H018 proposal was present in the tree. No run, edit, or child process was used.

Primary text newly inspected here is limited to search snippets and abstracts: Amadori–Pintore–Sala ePrint 2017/609 (one Gröbner basis, still a summation-polynomial method), McGuire–Mueller ePrint 2017/1262 (abstract only; the project record already says it does not beat square root), Delaplace–May ePrint 2019/800 (F_{p²} only). Jochemsz–May was seen as a Springer snippet, not a full proof read. The 2024/1330 small-root bound paper was not opened. The differential-addition multiply count is a direct expansion from δ⁻¹ and x(P+J), not a timed implementation. Bernstein–Lange–Schwabe's 5M+S figure is taken from the project's existing source note, not from a new PDF pass.
