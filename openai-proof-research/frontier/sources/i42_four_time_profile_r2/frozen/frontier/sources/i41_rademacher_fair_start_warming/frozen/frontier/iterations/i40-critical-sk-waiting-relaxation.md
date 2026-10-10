# I40 — Critical SK waiting-time relaxation

**Disposition: full two-disorder target W remains unproved and not refuted. No substantial finding is nominated.** There is a complete technical Gaussian deduction, stronger in its initial-law quantifier than Gaussian W. Its proof uses dual observable compactness already paid by QU's warming, static two-copy tail, and strong semigroup operations. Two constructive approaches to the Rademacher obligation are developed below: transferring the posterior dissipation profile, and replacing coordinate convergence by a positive four-time observable profile. Neither closes the Rademacher step. All new deductions await the parent's independent proof review; evidence verification is not that review.

The operative acceptance history is six accepted findings and four remaining. Nothing here changes that count. The parent handles review, integration, commits and project-only publication. The exact brief, I39 report and parent verification, prior reports and acceptance-gate reviews are frozen in `../sources/i40_critical_sk_waiting_relaxation/`. All upstream theorems **and proof operations** at `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are assumed true; this is an audit of the proposed deductions, not of upstream truth.

## 1. Exact target and the source boundary

Let the unscaled couplings J_ij, i<j, be independent standard normals or independent symmetric signs, J_ji=J_ij, J_ii=0. At beta=1 and zero external field,

π(σ)=Z⁻¹ exp(n^(-1/2) Σ_{i<j}J_ij σ_iσ_j),  ν(σ)=2⁻ⁿ.

Each site refreshes from its conditional Gibbs law at rate one. Put T_n=n^(2/3), Q_n(u)=P_{uT_n}, and

A_n(t)=n^(-2/3) Σ_i π[σ_i Q_n(t)σ_i],
B_n(s,t)=n^(-2/3) Σ_i E_ν[σ_i(sT_n)σ_i((s+t)T_n)].

Thermal randomness is averaged and probability below is only over disorder. **W** asks, for each of the two laws, every 0<a<b<∞ and η>0,

lim_{S→∞} limsup_{n→∞} P{sup_{s≥S, t∈[a,b]} |B_n(s,t)−A_n(t)|>η}=0.

There is no n-dependent replacement of S, no exchange of the limits, and no assertion at t=0. In fact A_n(0)=n^(1/3). In uniform-site-attempt units the corresponding clock scale is n^(5/3); no such change is made here.

Use QU for *Universality of critical quench autocorrelations in the Sherrington–Kirkpatrick model*, October 5, FU for *Functional universality of critical SK autocorrelations*, October 5, and CM for *Critical mixing in the Sherrington–Kirkpatrick model*, September 25. Full pinned paths, raw URLs, Git blobs and SHA-256 hashes are in `selected-pinned.json`; exact ranges/labels are in `read-passages.json` and `contracts.json`.

The decisive source contracts, including their operations, are:

1. QU `01-introduction.tex`, `thm:main`: joint convergence of A_n and B_n on compact positive-time sets for both laws, followed by relaxation of the limiting quench. This alone does not prove W.
2. QU `04-warming.tex`, `thm:warming`, **Gaussian only**: for any confidence loss χ>0, fixed auxiliary parameters, deterministic C_χ and ε_{n,χ}↓0, on events of limiting lower probability at least 1−χ,
   ||Q_n(u)||_{1→∞}≤K_χ(u):=C_χ exp(C_χ u^(-77/50)) for all u≥ε_{n,χ}.
   The same event serves all initial probability laws, including disorder-dependent ones. Its entropy bound holds for every positive u. I read the whole 1,623-line proof: the small-entropy two-observation argument; square-root-energy posterior-mean estimate; order-n stopped retention; moderate-range source transfer; level/support reductions; and integration to the kernel bound. The fixed entropy threshold and not just the exponent are essential here.
3. QU `05-gaussian-limits.tex`: common-cylinder strong L² approximation; bounded-source resolvent optimizers; recovery with fixed polynomial index before its outer limit; `glim:semigroup-strong` for all strongly converging inputs and varying positive times; `glim:static-tail` for the entire coordinate tail. I read the entire section, including the uniform-start escape proof, which is not needed for the result below.
4. FU `02-edge-law`, `prop:edge-conditioned-law`, and `03-observations`, `cor:observations-static`: all fixed-coordinate polynomial moments, with cube convergence obtained by the actual Haar replica comparison and truncation. FU `05-gradient`, `prop:gradient-domain`: the closed form has exactly constant kernel. FU `06-microscopic`, `lem:micro-recovery` and `thm:micro-relaxation`: bounded-polynomial-test liminf and strong cylinder recovery. The proof is not a theorem that arbitrary low-energy sequences retain their norms. QU's bounded resolvent argument is the authorized route to strong semigroup convergence.
5. CM's full functional constants allow every fixed positive exponent slack. The internal `cap-entropy.tex`, `cap:first-entropy-scale`, starts at k_min of order sqrt(log n); the product bound charges sqrt(log n+L), and the final layer argument absorbs logarithms into n^ρ. These operations do not turn R_J/T_n or C_LS/T_n into bounded constants. QU's newer fixed-threshold warming is the stronger usable Gaussian interface. The critical-slowing companion's linear Rayleigh-quotient theorem also does not bound the full gap.
6. QU `09-replacement.tex`, `repl:test-class`, `repl:comparison`, `repl:both-cutoffs`: polynomially many queries on **fixed** positive rectangles, smooth test derivative sums bounded by powers of log n, and histories with fixed terminal-time ratios. The retained cutoff includes kernel-log caps of order n^β, not a transferred O(1) kernel constant. Its universal output is trace-law convergence and survival of those cutoffs.

The whole 749-manuscript inventory and the entire read-only 9,340-file corpus were searched again. The source tree has 13,223 entries; CONTENTS' 719 entries are not the coverage denominator. The project search covers all snapshotted Markdown reports outside caches; the 15 matched documents include I17's different-temperature free-energy screen and I39. Neither is a duplicate of the Gaussian argument below. I39's statement that W was unresolved was correct as a status report; its proposed density compactness obligation was sufficient, not necessary. R012 and the archived block-spin consequences are outside this task. I30/I36's operation-level technical gate, and R011/I38's genuinely unpaid uniform mechanisms, are retained as the significance standard.

## 2. Complete technical deduction: Gaussian observable relaxation

For any probability ρ on the cube, define B_n^ρ by replacing ν with ρ. The following is a deduction under the pinned inputs, submitted for independent checking.

**G.** For Gaussian disorder, every 0<a<b<∞ and η>0,

lim_{S→∞} limsup_n P{sup_ρ sup_{s≥S,t∈[a,b]} |B_n^ρ(s,t)−A_n(t)|>η}=0.

The supremum includes every disorder-dependent initial law. It concerns this autocorrelation family, not total variation, a whole spectral-gap bound, LSI, or convergence of all bounded observables. No deterministic relaxation rate in S is claimed.

### 2.1 Strong compactness of the correlation observable

Complete the Gaussian matrix by the independent GOE diagonal and choose signed orthonormal eigenvectors u_a as in QU. This leaves the physical spin measure and dynamics unchanged. Set x_{a,n}=n^(-1/3)〈u_a,σ〉, and define

F_{n,t}=Σ_{a=1}^n x_{a,n} Q_n(t)x_{a,n},  G_{n,t}=F_{n,t}−π[F_{n,t}].

Orthogonality makes F independent of the auxiliary diagonal/eigenframe choices: it equals n^(-2/3) Σ_i σ_iQ_n(t)σ_i. In particular πF=A_n. Let

Qtail_{n,m}(x,y)=Σ_{a>m}x_{a,n}(x)x_{a,n}(y),
V_{n,m}=(π⊗π)[Qtail_{n,m}²].

On QU's represented Gaussian subsequences,

lim_{m→∞} limsup_n V_{n,m}=0 almost surely.                                      (1)

This is the actual `glim:static-tail`, not a sum of absolute coordinate second moments (that sum diverges). Its proof inserts the whole squared overlap tail into the uncapped two-replica comparison, uses spherical coordinate sign symmetry, then the summable squared resolvent tail. Keeping all cross terms before the Haar estimate matters.

There is a useful direct strengthening of QU's scalar tail estimate. Writing p_{n,t} for the relative transition kernel, Markov Jensen followed by the kernel bound gives, simultaneously for t≥a and all sufficiently large n on that representation,

||Σ_{a>m}x_{a,n}Q_n(t)x_{a,n}||₂²
=∫[∫p_{n,t}(x,y)Qtail_{n,m}(x,y)dπ(y)]²dπ(x)
≤∫p_{n,t}(x,y)Qtail_{n,m}(x,y)²dπ(x)dπ(y)
≤K(a)V_{n,m}.                                                               (2)

Every integral is finite for finite n. The same calculation applies to finite tail intervals in the limiting space using QU's limiting kernel and `glim:limit-static-tail`. Thus

F_t=Σ_{a≥1}x_a S_t^g x_a

exists in L²(Π_g), uniformly for t∈[a,b]. Its integral is A_g(t). This is stronger than mere convergence of its pairing against h_s, but follows from the very same source estimate by one conditional Jensen inequality.

For completeness, products in a finite head really converge strongly. Static second moments and cylinder pairings make x_{a,n}→x_a strongly. Hence u_{n,t_n}:=Q_n(t_n)x_{a,n}→S_t x_a strongly whenever t_n→t>0. For t_n≥a,

||u_{n,t_n}||∞≤K(a)π|x_{a,n}|,

uniformly bounded on the represented sequence. The limit has the corresponding bound. Use a smooth clipped coordinate c_R(x_a), equal to x_a on |x_a|≤R, bounded by a constant times R, with |x_a−c_R(x_a)|≤C|x_a|1_{|x_a|>R}. The omitted product has L² norm bounded by

C K(a)π|x_{a,n}| · (π[x_{a,n}²1_{|x_{a,n}|>R}])^(1/2) ≤ C_a/R,              (3)

using convergence/boundedness of the fixed fourth moment. The limiting bound is identical. Multiplication by the common bounded cylinder c_R preserves strong convergence: approximate the other factor by common bounded cylinders, use the multiplier's sup norm, and then static convergence of cylinder products. Compact-support cutoffs, if required by the chosen core, are removed by the same fixed-coordinate moments. Passing n first, then R, proves strong convergence of x_{a,n}u_{n,t_n}.

Finite sums, (1)–(3), and the analogous limiting tail prove

F_{n,t_n}→F_t strongly, and G_{n,t_n}→G_t:=F_t−A_g(t) strongly,
for every t_n→t∈[a,b].                                                       (4)

This also proves continuity of t↦F_t in L² and compactness of its image. For the finite head, truncate x_a as above and use strong continuity of S_t x_a; tails are uniformly small. Uniformity over [a,b] follows by the subsequence criterion on this compact parameter interval. A countable core and rational times are fixed before the representation; arbitrary time sequences follow from QU's varying-time convergence and these deterministic estimates. There is no assertion that every bounded finite-model function or density has a strongly convergent subsequence.

### 2.2 Duality pays the whole late-time supremum

Fix a burn time s₀>0, say s₀=1. Let w_{n,s₀}^ρ=d(ρQ_n(s₀))/dπ. The one common warming event gives

0≤w_{n,s₀}^ρ≤K(s₀),  πw=1,  ||w_{n,s₀}^ρ−1||₂≤sqrt(K(s₀)−1)

simultaneously for every ρ. For S>s₀, s≥S, reversibility and semigroup contraction give

|B_n^ρ(s,t)−A_n(t)|
=|〈w_{n,s₀}^ρ−1,Q_n(s−s₀)G_{n,t}〉|
≤sqrt(K(s₀)−1) ||Q_n(S−s₀)G_{n,t}||₂.                                      (5)

The step from s to S is L² contraction. It is valid for arbitrarily large finite s and so pays the supremum on the unbounded waiting-time interval at once. No long-time entry replacement or norm convergence of w was used.

For each fixed S>s₀, (4) and QU's strong semigroup operation imply

r_n(S):=sup_{t∈[a,b]}||Q_n(S−s₀)G_{n,t}||₂
→r_g(S):=sup_{t∈[a,b]}||S^g_{S−s₀}G_t||₂                                  (6)

on the represented subsequence. To justify the supremum, a maximizing sequence of times has a convergent subsequence; (4) and the fixed-time strong operator convergence apply to it. Conversely evaluate at a maximizer of the continuous limiting norm. The same sequential argument yields uniform convergence of the norm functions if desired.

Each G_t is centered. Since the source form kernel is exactly the constants, spectral calculus gives ||S_u^g G_t||₂→0 for each t. A finite L² net in the compact family {G_t:t∈[a,b]}, together with contraction, makes this uniform:

r_g(S)→0 as S→∞.                                                           (7)

No positive lower bound on the entire finite or limiting spectrum is needed.

Here is the disorder/limit bookkeeping. Apply the source represented-subsequence convention to any offending subsequence, retaining the kernel constants, all fixed head moments, tail errors, and the countably many integer S in (6). The bound K(s₀) is finite almost surely there. Equations (5)–(7) show

limsup_n P{sup_ρ sup_{s≥S,t∈[a,b]}|B_n^ρ−A_n|>η}
≤P{sqrt(K(s₀)−1) r_g(S)≥η}

along this further subsequence. The right side tends to zero. Equivalently localize all tight constants at confidence 1−χ, carry out the finite-head/core approximation on that common event, then let χ↓0. An assumed failure of G would give a subsequence with positive probability for arbitrarily large integer S; the above further representation contradicts it. Monotonicity in S extends the integer conclusion to real S. All finite-model quantities in G are independent of the auxiliary GOE diagonal, so marginalization gives the stated off-diagonal disorder law.

This completes the deduction of G, including Gaussian W. Its reduction certificate is explicit: QU tail plus Jensen → (2); QU strong semigroup plus ordinary cutoff → (4); warming plus reversibility/contraction → (5); the existing limiting constant kernel plus a finite net → (7). These are technical extensions of available operations. A stronger initial-law quantifier does not manufacture a substantial finding.

## 3. Independent audit of I39's delayed-bump obstruction

On the uniform eight-state space (x,y,z)∈{−1,1}³, take independent flips of rates 1/(2N), 1/N, 1/2. The coordinate decay rates are 1/N, 2/N, 1. The symmetric generator is irreducible for finite N. Its relative kernel is at most 8, uniformly over all times and N. With α=1/4, the initial density h₀=1+α(x−y) lies in [1/2,3/2], has mass one, and evolves as

h_s=1+α exp(-s/N) x−α exp(-2s/N) y.

For f=z(1+x+y)/3, |f|≤1. Put u=exp(-t/N), v=exp(-t). Direct multiplication gives

fP_t f=(v/9)[1+u+u²+(1+u)x+(1+u²)y+(u+u²)xy].                             (8)

Therefore A_N(t)=v(1+u+u²)/9 and

B_N(s,t)−A_N(t)=(αv/9)[(1+u)exp(-s/N)−(1+u²)exp(-2s/N)].                        (9)

The compact limit is A(t)=B(s,t)=exp(-t)/3, but at s=N log 2 the difference tends to exp(-t)/72. Every finite chain eventually equilibrates. This verifies I39's formula, normalization, positivity, reversibility and actual moving-time bump independently. The rational diagnostic builds the full transition matrices and also checks duality and the four-time identity below; it does not merely evaluate the claimed formula.

There is no contradiction with G. If the common visible cylinder space keeps only z, its limiting two-state semigroup is ergodic, but F_{N,t}=fP_t f does **not** converge strongly to its visible conditional mean. Its centered squared L² norm is

(v²/81)[(1+u)²+(1+u²)²+(u+u²)²]→4exp(-2t)/27>0.                              (10)

If instead all three coordinates are retained, the limiting semigroup freezes x,y and is not ergodic. Thus one cannot simultaneously invoke G's common strong observable limit and its ergodicity in this model. Uniform kernels alone supply neither. This is an admissible reversible-model counterexample to the stated shortcut, not an SK counterexample and not a new finding.

I39's stationary large-lag deduction is also sound: positive spectral measures make A_n nonnegative/decreasing, so the late-lag supremum is A_n(T). Fixed-T convergence and limiting decay prove its probability bound. That statement concerns t, not s, and is not substituted for W.

## 4. Rademacher attempt I: transfer a fixed-threshold dissipation profile

Gaussian observation identities remain exact for any fixed symmetric interaction matrix. For B_p=U diag((p²−d_a)_+)Uᵀ, the channel h_p=B_pX+β_p has posterior interaction W−B_p and external field h_p. Its posterior-variance derivative, conditional energy contraction, likelihood entropy identity, and product-endpoint tensorization are deterministic. Thus a Rademacher proof need not replace the heat-bath path out to s→∞; it could establish the probabilistic posterior bounds once and run QU's deterministic warming assembly.

The needed small-scale interface is concrete. At each desired disorder confidence it would have to hold on one event for every allowed p with **K_χ≤np³**, every posterior field in the specified fixed balls/annuli, and every 0≤f≤1:

V_p(f)≤C_χ p⁻² E_π(f)+C_χ exp(−c_χ(np³)^α),
p² Q_π|∇F_p|²≤C_χ V_p(f)+C_χ exp(−c_χ(np³)^α),                              (11)

together with the sharp annular covariance margin, projection tails and transition-potential extension used in QU's small-entropy proof. The terminal moderate/order-n posterior stability and word-diagnostic events would also need their Rademacher versions. This is a list of actual estimates at defined scales, not a claim that (11) alone implies warming.

Why the existing route stops: QU obtains these bounds by an exact **conditional Haar eigenframe** identity after GOE diagonal completion. The biased law L_circ dHaar turns spectral spin coordinates into spherical Gibbs coordinates and then controls posterior partition ratios at all admissible fields. Adding a Gaussian diagonal to a Rademacher off-diagonal matrix does not produce GOE or a conditionally Haar frame. Edge eigenvalue universality, or even finitely many eigenvector-entry limits, does not assert these Gibbs-tilted, field-uniform posterior comparisons. The extended covariance proof and warming cannot simply be relabelled as two-disorder theorems.

CM's minimum dimension sqrt(log n) also cannot be substituted for K_χ here. In QU's small-entropy proof one takes np₁³=c₀L and nR³=L^M with fixed L. A minimum dimension diverging with n excludes every such fixed L. A dissipation ODE known only above a diverging threshold can warm to that threshold but does not prove bounded L² density at a fixed multiple of T_n. This is precisely where the newer Gaussian source operation matters.

A direct measure comparison does not fix this. If two Hamiltonians differ by V with ||V||∞≤D, then their Gibbs density ratio lies in [exp(-2D),exp(2D)]. Comparisons of norms and reversible forms consequently pay exponential factors in D. Replacing one unscaled entry by ΔJ gives D≤|ΔJ|/sqrt n. Multiplying such bounds over order n² entries pays the sum of absolute changes (typically order n^(3/2)); comparing the completed matrices directly gives at best D≤(n/2)||ΔW||, still extensive for a bounded nonvanishing norm difference. These bounds fail to yield the required tight constants. They do not prove that Rademacher warming is false.

Nor is a hypothetical tight entropy bound enough to complete our L² argument. Here is a precise two-atom obstruction. For m≥2 let π(E)=m⁻³ and ρ(E)=m⁻¹, with the complementary masses at the other atom, and let F=m1_E. Then

ρF=1, πF=m⁻², ||F||²_{L²(π)}=m⁻¹→0,
D(ρ||π)≤2 log(m)/m→0,  ||dρ/dπ||²_{L²(π)}=m+(1−1/m)²/(1−m⁻³).

The entropy upper bound follows because the complementary density is below one, so its entropy contribution is nonpositive. Even vanishing entropy/TV does not compensate this growing observable without a rate or stronger integrability. Take m=n^(1/3) on n=m³ to match the crude SK observable bound. This is only a measure-theoretic obstruction, not a model of the SK Gibbs law or its dynamics. It identifies why transferring entropy alone, then applying Pinsker to ||F||∞≤n^(1/3), leaves an unpaid quantitative step.

**Status of attempt I:** no Rademacher version of the fixed-threshold posterior comparison or of positive-time L² warming has been proved. The deterministic observations and reduction are valid partial deductions; the Haar-based probabilistic input remains unpaid.

## 5. Rademacher attempt II: a positive four-time observable profile

This route avoids identifying any Rademacher edge coordinates, recovering a whole spectral gap, or comparing at an unbounded terminal time. Define, for either disorder law,

R_n(u,t)=||Q_n(u)G_{n,t}||²₂=〈G_{n,t},Q_n(2u)G_{n,t}〉, u>0.                (12)

It is nonnegative and nonincreasing in u. There is a physical fixed-time representation. Put q_n(x,y)=n^(-2/3) x·y. For a stationary spin trajectory in normalized time,

R_n(u,t)=E_π[q_n(X₀,X_t) q_n(X_{t+2u},X_{2t+2u})]−A_n(t)².                (13)

To prove (13), condition on X_t; by reversibility the conditional expectation of the first overlap is F_{n,t}(X_t). Given X_{t+2u}, the last overlap has conditional expectation F_{n,t}(X_{t+2u}). The Markov property across the middle interval gives 〈F,Q_n(2u)F〉. Subtracting A² centers it. This is a sequential four-endpoint history with three legs t,2u,t, not a product of independent copies of the ordinary two-point trace. The subtraction is exact and R_n≥0 despite signed individual path overlaps.

Here is a complete sufficient criterion, useful because it separates two distinct finite-time obligations:

**C.** Suppose for Rademacher disorder, at some fixed s₀>0,

(i) L_n:=||d(νQ_n(s₀))/dπ−1||₂ is tight;
(ii) for every fixed u>0 and 0<a<b, R_n(u,·) converges in law in C([a,b]) to the Gaussian R_g(u,t):=||S_u^g G_t||²₂.

Then Rademacher W holds. Indeed duality/contraction, exactly as in (5), gives

sup_{s≥s₀+u,t∈[a,b]}|B_n(s,t)−A_n(t)|≤L_n sqrt(sup_{t∈[a,b]}R_n(u,t)).

For a deterministic M, its failure probability is at most

P(L_n>M)+P(sup_t R_n(u,t)>η²/M²).

Take limsup_n, then u→∞ using (ii), compact-family decay (7) and Portmanteau, then M→∞. Dependence between L_n and R_n is irrelevant; no joint independence is assumed. This proves the conditional assertion C.

Gaussian sources pay both clauses. For Rademacher, (13) makes clause (ii) a plausible **fixed-horizon** extension of QU's comparison. The new endpoint product has absolute bound n^(2/3), so its crude size is polynomial. Repeating the score/conditional-copy estimates for three legs could therefore be technically feasible. However the printed final query class consists of the stationary one-leg and uniform-start two-leg traces, and its cutoff removal/base-mass argument uses those query laws. I have not proved the needed derivative, three-leg survival, and uniform-lag modulus assertions as a complete theorem. I do not import (ii) from two-point convergence or describe this extension as done.

More seriously, clause (i) is not one of those endpoint-polynomial queries. Its exact expression is

L_n²+1=〈w₀,Q_n(2s₀)w₀〉_π
=Σ_{x,y}ν(x)P_{2s₀T_n}(x,y) ν(y)/π(y),  w₀=ν/π.                           (14)

The endpoint weight ν(y)/π(y) can be exponential in n. QU's history derivative lemma assumes a fixed polynomial bound on the endpoint test; using (14) violates that contract. Transferred n^β kernel-log cutoffs permit an exp(C n^β) density cap, not tight L_n. For any fixed u, (ii) would at most give o(1) observable norm as u→∞ after n; it cannot absorb a growing factor in n without a new quantitative estimate.

A spectral version makes the missing information still more explicit. With E_n the spectral resolution of T_nH_n, (12) controls the positive measure 〈G_{n,t},E_n(dλ)G_{n,t}〉. The waiting-time difference instead integrates e^{−sλ} against the **signed** cross measure 〈w₀−1,E_n(dλ)G_{n,t}〉. Two-point stationary A_n controls a different positive measure built from the linear spins. At zero field the latter spins are odd under global spin reversal, whereas F and w₀−1 are even. An odd-sector linear bound does not provide the even-sector cross control. I39's two slow modes in (9) explicitly permit cancellation on every fixed time range and later uncancellation. Tight L_n plus the positive profile in C would prevent that; positivity of A_n alone does not.

**Status of attempt II:** the exact positive-profile representation and sufficient criterion are proved as technical deductions. A complete three-leg comparison and a uniform fair-start L² estimate remain unpaid. This is narrower than requiring a universal LSI or worst-start mixing theorem, but is not a proof of full W.

## 6. Current primary comparison, diagnostics and disposition

The early web searches and full responses are retained in `web01.json` and `web02.json`; direct response bodies, request URLs/timestamps/status, current-version pages and versioned PDFs are in `literature/`. Search results were not treated as premises. The important comparisons were checked in the papers:

- [Billoire–Campbell, 1105.1902v3](https://arxiv.org/abs/1105.1902v3) studies equilibrium SK relaxation numerically, in updates per spin, including the n^(2/3) scale and sample averaging. This supports the physical relevance and normalization of the finite-size relaxation question. It is not a uniform waiting-time proof or a fair-start density estimate.
- [Dembo–Lubetzky–Zeitouni, 1911.08001v2](https://arxiv.org/abs/1911.08001v2), Theorem 1.1 and the piecewise-frozen-interaction proof, concerns asymmetric soft-spin Langevin dynamics on fixed [0,T]. Its approximation mesh is chosen after T. Neither the dynamics nor the time quantifiers yield W.
- [Dembo–Gheissari, 2006.13167v2](https://arxiv.org/abs/2006.13167v2), Theorem 1 and the stochastic-Taylor proof of Proposition 3.1, permits symmetric interactions and polynomial multi-time statistics. Its constants depend on a fixed T; the proof chooses a positive series parameter proportional to 1/T and a dimension threshold depending on that parameter. Its linear random-matrix diffusion class is not critical Ising heat bath. It does not supply an all-time Rademacher comparison here.
- [Chatterjee, math/0508519v3](https://arxiv.org/abs/math/0508519v3), Theorem 1.1 and replacement proof, pays comparison by derivative sums; it does not remove time dependence from derivative bounds. The first fetched identifier math/0508213v1 was the distinct *A Simple Invariance Theorem*. That successful but misidentified response is retained and excluded as the cited 2006 article; the correct version was then fetched.
- [Wang, 2608.22159v2](https://arxiv.org/abs/2608.22159v2), Theorem 4.1, Lemma 4.2, Theorem 4.3 and the localization argument, requires all-field covariance control and covers a subcritical range. It cannot replace a critical fixed-threshold posterior estimate. The pinned QU/CM proof operations are stronger and closer inputs for the present task.

The named problem is the finite-size critical quench's relaxation to equilibrium uniformly after arbitrarily long waits. Its importance is observed in QU's explicit separation of thermodynamic-first dynamics and the critical window, and the numerical equilibrium program above; no invented importance score or worldwide-priority assertion is made. The only closed SK result here, G, is technical under the project's operation-level gate.

The new exact diagnostic has 3,285 assertions and uses rational arithmetic to reconstruct product-chain transition kernels, stationarity/reversibility, density evolution, (8)–(10), duality, Jensen's tail bound, and (12)–(13). It also checks the density-spike example, clock normalization on exact cubes n=m³, and the fixed-exponent replacement powers. These checks target admissibility, centering and normalization errors; they do not numerically prove G, C, W or novelty. No floating experiment is used. The I39 diagnostic is replayed independently without writing to I39; its 389 exact checks retain their scoped meaning.

The verifier checks the complete corpus inventory, SHA-256 and Git blobs, reproduces both corpus-search patterns and the frozen project search, checks fresh pinned responses, retained primary bytes/versions, read ranges and labels, all frozen inputs, and the one-time I40 seal. It reports live shared-ledger drift separately. It also checks I39's existing artifact seal without refreshing it. The entire corpus was searched, not semantically read. Selected-file acquisition is not a claim that every selected proof was read in full; `read-passages.json` records the actual coverage.

Run from `/home/mj-kang/Documents/Dev/math/openai-proof-research`:

```bash
python -B frontier/experiments/i40_critical_sk_waiting_relaxation/check.py
python -B frontier/experiments/i40_critical_sk_waiting_relaxation/verify.py
```

**Final mathematical verdict:** Gaussian W, even uniformly over initial laws, follows by the complete technical argument in §2, pending independent proof review. Full W for both disorder laws remains unproved and not refuted. The Rademacher posterior/positive-time density input and the alternative four-time transfer obligations are exposed explicitly. No substantial nomination, acceptance/count action, commit or publication was performed.
