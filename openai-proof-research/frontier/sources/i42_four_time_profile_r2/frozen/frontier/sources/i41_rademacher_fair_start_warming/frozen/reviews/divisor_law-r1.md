# Referee report: prime-predecessor divisor overlap law, round 1

Date: 2026-10-08. Scope: `proposals/number_theory.md`, section 1 only. Read `AGENTS.md`, the pinned source metadata, and the relevant catalogue/source statements. All upstream OpenAI theorems at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are accepted as true by instruction; their proofs are not being refereed.

**Verdict: ACCEPT the downstream mathematical result; CORRECTIONS to attribution and novelty framing before promotion as a research finding.** I found no fatal gap in the repeated-prime estimate, marked-mass limit, Gamma argument, divisor coupling, moments, or nonconcentration deduction. The main missing literature is substantially closer than the present novelty paragraph suggests. The result is a sound specialization of classical divisor/PD machinery to the assumed prime-predecessor theorem. Priority for this specialization has not been established.

## 1. Actual upstream contract

I fetched the [pinned introduction](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026/build/sections/01-introduction.tex) and verified byte equality with the local cached TeX (SHA-256 `ae0c15651b162958c193f0ad32078146e17fb1f566d47c14be9df9cb6accb1ca`). Its `thm:main`, `eq:main-law`, says exactly that, for every fixed k and bounded continuous F on [0,1]^k,

\[
 \frac1{\pi(x)-1}\sum_{3\le p\le x}F(V_1(p),\ldots,V_k(p))
 \longrightarrow \mathbb EF(L_1,\ldots,L_k).
\]

Here the sum is over primes, factors are ranked **with multiplicity**, zero padded, and normalized by **log(p−1)**. The statement explicitly uses equal prime weights and all real x tending to infinity. Its PD(1) definition is ranked independent uniform stick breaking. Thus there is no normalization, weighting, multiplicity, or subsequence mismatch in the proposal.

I also read the cached [section 8](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Poisson-Dirichlet-Law-for-Prime-Predecessors-September-24-2026/build/sections/08-poisson-dirichlet.tex), checked the companion introductions (smooth predecessors/totient fibers and even prime-factor parity), and searched the family-011 cached TeX for divisor-law terminology. No duplicate statement of the proposed overlap law was located. This is a bounded companion check, not a claim to have excluded every possible duplicate in the entire repository.

## 2. Repeated-prime mass: correct

For every e≥2, floor(e/2)≥e/3, including the extremal e=3. Therefore the constructed d satisfies d²|n and log d≥R(n)/3. On n≥√x, the event R(n)>η log n gives d>x^(η/6). Union bounding over **all integers d**, rather than primes, is valid:

\[
 \#\{n\le x:\exists d>x^{\eta/6},\ d^2\mid n\}
 \le x\sum_{d>x^{\eta/6}}d^{-2}
 =O_\eta(x^{1-\eta/6}).
\]

The map p↦p−1 is injective, so restricting this exceptional set to prime predecessors only reduces its size. Dividing by π(x)−1 yields Oη(x^(−η/6) log x)=o(1). The omitted small predecessors contribute at most (√x+1)/(π(x)−1)=o(1). This establishes (3) without any estimate for primes in growing progressions. The stronger quantity R(n), counting **all** occurrences of a repeated prime, is exactly what the subsequent coupling needs.

## 3. From finitely many factors to all colored mass: correct

For fixed K, averaging a bounded continuous test over the 4^K possible colors makes it a bounded continuous test of the first K masses. The source theorem applies. Moreover,

\[
 \mathbb ET_{x,K}=1-\sum_{j\le K}\mathbb EV_j(p)
 \longrightarrow 1-\sum_{j\le K}\mathbb EL_j
 =\mathbb E\sum_{j>K}L_j.
\]

The final expression decreases to zero because the PD mass sums to one. For example, the original stick remainder has expectation 2^(−K), which also establishes that the stick fragments exhaust the unit mass almost surely.

The colored tail has l¹ norm T_{x,K}. Bounded Lipschitz tests immediately give the required iterated approximation, and uniform continuity handles general continuous tests. A minor presentational improvement: truncated vectors lie in the compact **subprobability** simplex {z≥0:Σz≤1}, not the mass-one simplex. Work there or extend tests continuously to [0,1]^4. This is an easily supplied formal clarification, not a substantive gap.

## 4. Dirichlet identification: correct

Independent marking is invariant under the random permutation that ranks the stick fragments: conditional on the fragments, any such permutation still leaves the colors independent with the prescribed probabilities. The unsorted recursion is therefore justified.

Take independent G_i∼Gamma(α_i,1), Σα_i=1, set S=ΣG_i and Z=G/S, and take independent T∼Gamma(1,1). Then S∼Gamma(1,1), independent of Z, and U=T/(S+T) is uniform and independent of Z. For a fixed i,

\[
 Ue_i+(1-U)Z=(G+Te_i)/(S+T)\sim\mathrm{Dir}(\alpha+e_i).
\]

The density ratio against Dir(α) is z_i/α_i because the original total shape is one. Mixing over an independent J with probability α_i recovers the original density. Independence of U from the **original** normalized vector is what is required; the proof does not mistakenly require independence from the updated vector. The same-noise coupling contracts expected l¹ distance by E(1−U)=1/2. Boundedness of the simplex proves uniqueness among probability laws. Four equal colors consequently give Dir(1/4,1/4,1/4,1/4).

## 5. Coupling actual uniform divisors: correct, with a wording precaution

Uniform sampling from the set of divisors means independent exponent choices a_q,b_q∼Unif{0,…,e_q}. At q^e the four exponents in (A,B,C,H) are

\[
 (\min(a,b),\ (a-b)_+,\ (b-a)_+,\ e-\max(a,b)),
\]

all nonnegative and summing to e. For e=1 these are precisely four equiprobable unit vectors. For e≥2, the true contribution and independently marked occurrence contribution both have total mass e log q/log M, so their l¹ distance is at most twice this mass. Summation proves the claimed deterministic bound 2R(M)/log M. One can construct the coupling independently prime by prime, preserving all required conditional independence.

The phrase “distinct positive divisors” correctly means that each divisor is counted once in the sampling set. It must **not** be paraphrased as requiring D₁≠D₂: the stated model samples with replacement and permits equality. For clarity, explicitly say “with replacement.” If a separate without-replacement result is wanted, τ(p−1)→∞ in probability follows from finite-dimensional PD convergence (every fixed L_K is positive almost surely), so the collision probability E[1/τ(p−1)] tends to zero. That extension is unnecessary for the current theorem.

## 6. Moments and conditional nonconcentration: verified

Exact rational expansion of the displayed Dirichlet moment formula independently gives

\[
 \mathbb E(U-1/2)^2=1/8,\quad
 \mathbb E[(U-1/2)(V-1/2)]=0,\quad
 \mathbb E[(U-1/2)^2(V-1/2)^2]=7/384.
\]

In particular, 7/384−(1/8)²=1/384. The symbolic check was performed with Python integer/fraction arithmetic; no simulation is being substituted for proof.

A useful independent hand check also explains the phenomenon. For PD masses L, conditionally independent Bernoulli marks give conditional variance Q∞=(1/4)ΣL_j². Let S₂=ΣL_j². Uniform stick breaking yields

\[
 S_2\overset d=U^2+(1-U)^2S_2',\quad
 \mathbb ES_2=1/2,
\]
\[
 \mathbb ES_2^2
 =1/5+2(1/30)(1/2)+(1/5)\mathbb ES_2^2
 =7/24.
\]

Thus EQ∞=1/8 and EQ∞²=7/384 again. In the finite divisor model the exact identity

\[
 Q_p=\frac1{12\log^2 M}\sum_{q^e\parallel M}e(e+2)(\log q)^2
\]

follows from Var(Unif{0,…,e})=e(e+2)/12. It is consistent with the repeated-prime approximation.

Complementing divisors gives conditional mean 1/2 exactly for every p. Conditional independence then makes EQ_p² equal to the mixed centered fourth moment. All tests involved are bounded continuous, so moment convergence follows from the proved weak convergence. Since 0≤Q_p≤1/4, convergence in probability to 1/8 would force convergence in L² and zero limiting variance. The positive limit 1/384 rules this out. The claimed failure of convergence in probability of the random conditional measures to deterministic arcsine, in the weak topology, is therefore valid. This does not assert that no random limiting measure exists.

## 7. Literature and necessary novelty corrections

1. **The direct classical PD-to-Dirichlet reference is missing.** Hirth's *From GEM back to Dirichlet via Hoppe's Urn*, CPC 6 (1997), 185–195, explicitly generalizes the GEM/PD beta construction to a Dirichlet law. The [publisher abstract](https://doi.org/10.1017/S0963548396002842) verifies that scope. This belongs alongside the already cited arcsine paper. I accessed the publisher abstracts, not the full paywalled Hirth theorem statements; the present self-contained proof does not depend on them.

2. **Earlier multi-divisor laws are much closer than just a generic factorization theorem.** De la Bretèche–Tenenbaum, *Sur les processus arithmétiques liés aux diviseurs*, Adv. Appl. Probab. 48(A) (2016), 63–76, Theorem 1.1, treats the averages of products of the conditional divisor CDFs. I read the theorem and its sampling interpretation in the [author's corrected manuscript](https://tenenb.perso.math.cnrs.fr/PPP/proc-arith.pdf), also available as an author-uploaded text. For r independently uniform divisors of one uniform integer, its limit integrates a Dirichlet density with 2^r parameters all equal to 2^(−r), over binary-coordinate sum constraints. At r=2 this is exactly the proposed limiting joint law of (U,V). Thus the two arcsine marginals' dependence and its ordinary-integer moment consequences are classical consequences of an explicit prior theorem. Its introduction also records older random divisor-process limits. It does not give the prime-predecessor specialization.

3. Bareikis–Mačiulis, *Cesàro means related to the square of the divisor function*, Acta Arith. 156 (2012), 83–99, [Theorem 2.1](https://www.impan.pl/shop/en/publication/transaction/download/product/82360), already evaluates the averaged square of the conditional divisor CDF, with the quarter-parameter integral. I checked the theorem itself. This is an additional concrete precursor to the nonconcentration discussion.

4. Leung's [Theorem 7.1 and Example 7.5](https://arxiv.org/html/2206.14728v3) are more directly relevant than Theorem 1.1 alone. The general theorem allows multiplicative factorization weights and Example 7.5 allows prescribed pairwise coprimality constraints. For four factors (A,B,C,H), take the weight 1_{gcd(B,C)=1}: the map (D₁,D₂)↔(A,B,C,H) is a bijection between divisor pairs of n and such factorizations n=ABCH. Hence the full ordinary-integer overlap model is included in that classical weighted-factorization framework. Example 7.5 itself points to the 2016 and 2012 predecessors. The shifted-prime indicator is not multiplicative, so these results do not directly prove the proposal's arithmetic specialization.

5. [Haddad–Koukoulopoulos (2025)](https://jep.centre-mersenne.org/articles/10.5802/jep.317/), *On Arratia's coupling and the Dirichlet law for the factors of a random integer*, is also relevant: it gives a probabilistic PD-coupling proof of the ordinary-integer Dirichlet factorization law and improves the error term. Its scope is ordinary integers, not shifted primes.

6. The Bharadwaj–Rodgers comparison is substantively right. In the [arXiv v3 actually inspected](https://arxiv.org/html/2402.11884v3), the full PD statement is **Theorem 6**, requiring regularity and distribution level one; the shifted-prime level-one claim is Conjecture 4. Numbering differs from the version cited by the upstream manuscript. Their conditional route plus the present elementary transfer already supplies a conditional version of this specialization. Cite a version and its actual theorem number if adding a numbered reference.

Recommended framing: **“A prime-predecessor specialization of classical multi-divisor Dirichlet laws, deduced from the assumed upstream PD theorem, with explicit gcd/lcm marginals and a conditional-variance obstruction.”** Do not claim a new PD coloring law, new general divisor overlap distribution, or new general nonconcentration phenomenon. The proposal already disclaims established priority, which is appropriate; the closer references above should replace the suggestion that the relevant older literature merely remains to be checked.

## Disposition

Accept equations (1)–(3), both quoted moments, the variance 1/384, and the failure of deterministic conditional arcsine concentration. No new arithmetic hypothesis is needed beyond the assumed pinned theorem and elementary prime-counting growth. Add the direct classical references, clarify replacement sampling and the subprobability-simplex test domain, and retain an explicit “new-to-this-project; literature priority unverified” label. No proposal files were edited, and nothing was staged or committed.
