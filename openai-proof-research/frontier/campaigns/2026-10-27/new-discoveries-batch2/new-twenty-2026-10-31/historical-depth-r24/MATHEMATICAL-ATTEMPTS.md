# Second-pass attempts, zero endpoints

Priority after reading definitions: 405055 (finite combinatorial semantics and a conditional-moment approach), 383053 (explicit reversible coding), 324510 (local valuations). 405708 was initially selected but the actual source already contains the entire answer; stop that route. These rankings concern feasible mechanisms, not a claim of novelty or significance. All original objections remain in old-dispositions.json. No new record-coverage credit is sought.

## 405055: window versus variance

Read the OWR2026 report's Parameters section, Conjecture10 and surrounding Theorems7–11, printed pp38–39. Read Aires–Kahn2509.11549v1 §2 definitions (6)–(8), §3 order-polytope/simplex construction and derivations (15)–(26), Conjecture3.1, and concluding Conjecture12.8. These are actual source definitions/arguments; the full balance theorems and their dependencies were not audited. The source law is UNIFORM on order-preserving bijections to [n], not an arbitrary order-preserving random map. Empty predecessor/successor extrema have endpoints0 and n+1. The original source-scope objection is now resolved locally; the variance bound is not.

**Deletion/insertion reduction.** For each extension g of P−x let q be the last predecessor position (or0), r the first successor position (or n), W=r−q≥1, and M=(q+r+1)/2. There are exactly W extensions over g, with positions q+1,…,r. Thus the deletion marginal of a uniform extension of P is the W-size-biased uniform law on extensions of P−x. Writing E_* for that biased law,

win_P(x)=E_*[W+1],
Var_P(f(x))=E_*[(W²−1)/12]+Var_*(M).

This follows by counting each insertion once and the variance formula for a uniform integer interval. The first term is at most n E_*W/12, since W≤n. The unresolved term is Var_*(M). A uniform inequality Var_*(M)≤C n E_*(W+1), for absolute C, would finish the entire conjecture. No such bound was obtained. This identifies a real missing estimate rather than assuming an Efron–Stein inequality under dependent coordinates.

**Why support width does not suffice.** Let P be two unrelated chains of lengths m and k, and let x be rank r in the first chain; n=m+k. Interleavings give a uniform m-subset of [n], so

Var(f(x))=r(m−r+1)(n+1)(n−m)/((m+1)²(m+2)),
win(x)=2(n+1)/(m+1).

For m=k and r in the middle, the positional support has width k+1 of order n, while win is bounded. Hence the proposed support-width bridge cannot hold uniformly. Nevertheless the actual ratio Var/(n win) stays below1/8 in this family. This is a familiar order-statistic calculation, not a new significant solution. It shows why that failed bridge does not refute the conjecture.

**Second route: continuous geometry.** The source simplex coupling gives
Var(F(x))=Var(f(x))/((n+1)(n+2))+H(x)(1−H(x))/(n+2),
Win(x)=win(x)/(n+1).

A uniform Var(F(x))≤C Win(x) would imply Var(f(x))≤C(n+2)win(x). Conversely a discrete bound plus win≥2 controls the residual term and gives a continuous bound with another absolute constant. The conditional interval argument gives Var(F(x))≥Win(x)²/12, the reverse direction. Convexity/log-concavity of the marginal alone does not control its conditional fiber width. We did not silently reverse that inequality or substitute the stronger source Conjecture12.8 as a proved lemma. A coordinate-sensitive Poincare/fiber estimate is still missing.

**Diagnostics.** 120 deterministic-seed naturally ordered transitive posets with3≤n≤8 were evaluated by exact extension enumeration; deletion-weighted first/second/window identities agreed independently. Twelve two-chain cases matched the formulas. Maximum sampled Var/(n win) was7/96, at the eight-element antichain. This is a very small biased sample, not all posets, an asymptotic estimate or a certified counterexample search. No conclusion about the best universal constant follows.

Formal feasibility: if a finite counterexample family or a direct combinatorial midpoint estimate were found, finite posets, permutations, rational expectations and insertion bijections could be formalized. The missing universal midpoint estimate is the mathematics; it is not a semantic bridge we can omit. No Lean endpoint.

## 383053: reversible graph capacity

Read Meiburg2403.10985v1 §5 Definition5.1, Theorems7–11 and their complete displayed arguments, plus AppendixA Theorems14–15 and both short proofs. The current arXiv landing page lists v1. Definition: a partial deterministic automaton has a0–1 transition matrix for each symbol with row sums≤1; reversibility adds column sums≤1. Capacity is the supremum growth rate of graph-independent languages recognized by such automata. This is not ordinary deterministic regular-language capacity. The finite C7³ multirectangular separation in MathDB was not reconstructed or re-credited.

**Block-code rewind.** For an independent length-L code C of size M, the paper's construction reads the word, remembers its index, and consumes enough suffix symbols to reversibly reset that memory. Naming M possibilities costs ceil(log_d M) suffix positions over d symbols. For M approximately θ^L this overhead is proportional to L, yielding only θ^(log d/(log d+log θ)), strictly below θ for1<θ<d. Increasing L does not erase the proportional loss. A proof needs a genuinely different reversible recycling construction, or an independent code family whose required reset information is o(L). No such family for arbitrary graphs was constructed. The paper's assertion M≥c θ^L is stronger than follows just from the capacity limit; the displayed asymptotic lower bound can instead use rates θ−ε and then ε→0. This analytic observation is not an answer to MathDB.

**Clique padding.** For H_i=G join K_i, ordinary Shannon capacity stays Θ(G): map every added universal vertex to a fixed original vertex, preserving distinguishability and injecting each independent block code. The source's Theorem10 becomes arbitrarily tight on H_i as i grows. To deduce equality on G one would need, for example, Θ_REV(H_i)≤Θ_REV(G). That inequality was NOT proved. Relabeling a reversible automaton can combine two transition matrices and violate both determinism and injectivity.

Concrete failure of the direct operation: take G with two nonadjacent symbols0,1 and an added universal symbol z. A period-two partial automaton has R --z--> S --0--> R and R --0--> T --1--> R. Every symbol matrix is a subpermutation. With start/final state R its accepted language is concatenations of z0 and01. Distinct equal-length block sequences have a0-versus1 position, so this is a graph-independent language. Replacing z by0 creates two0 transitions out of R. This disproves only the proposed relabel-and-keep-states construction, not padding invariance or capacity equality. An alternative reversible automaton may exist (and for this simple graph the capacities are already equal).

**Third route: product regularization.** The paper proves only supermultiplicativity Θ_REV(G strong-product H)≥Θ_REV(G)Θ_REV(H). Combining this lower bound with its bound for powers cannot supply the reverse inequality Θ_REV(G^k)≤Θ_REV(G)^k. Exact multiplicativity would finish by α(G^k)≤Θ_REV(G^k) and taking kth roots. Neither this upper bound nor an amortized state-splitting version was obtained. Finite separation at one blocklength is insufficient for a strict asymptotic upper bound. No exponential search was launched to rediscover that fact.

Formal feasibility: automata and finite graph codes are feasible discrete objects, but supremum growth rates, strong powers, and the proposed amortized construction need full bridges. A theorem merely certifying the displayed three-state automaton would be an uncredited helper, not the endpoint. Park with the reversible recycling/padding/product gaps explicit.

## 324510: half-power sums

Read Meštrović1211.4570v1 §2.2 Conjecture2.14 (NOT adjacent Conjecture2.13 or2.17), §2.4 Theorem2.18 and its von-Staudt explanation, and the complete §3 proof of Theorem1.1. The exact exponent is m=(n−1)/2 even for n≡1 mod4, and S_m(n) sums1 through n−1. The adjacent odd-exponent theorem is not the target. No claim of a published resolution follows from these bodies.

**Prime-local elimination.** If an odd prime p divides n, let a=v_p(n), u=n/p^a. If p−1 divides m, then
S_m(n) ≡ −u p^(a−1) (mod p^a),
so v_p(S_m(n))=a−1<3a. One direct derivation: summing residues modulo p gives−1 when p−1 divides m. For b≥2, writing residues modulo p^b as t+j p^(b−1), binomial expansion gives S_m(p^b)≡p S_m(p^(b−1)) modulo p^b. The linear correction has factor p^(b−1)sum_j j, divisible by p^b for odd p; higher corrections have at least p^b. Induction yields−p^(a−1); partition1,…,n into u complete residue blocks and use n^m≡0 mod p^a. Since p does not divide u the valuation is exact. This is the classical local power-sum obstruction, not a new theorem to credit. In particular all eligible multiples of3 are eliminated; many composites with no resonant prime remain.

**Prime case and Bernoulli obstruction.** For a prime p≡1 mod4 with p≥13, m=(p−1)/2 is even and≥6. Faulhaber expansion gives S_m(p)≡p B_m modulo p³: the p² coefficient involves B_(m−1)=0; denominators of later Bernoulli numbers in the finite expansion have no p factor because their indices are <p−1, so the remaining powers contribute p³. Thus a prime counterexample requires p² dividing the numerator of B_((p−1)/2). We have no universal nondivisibility theorem for these numerators. p=5 is handled directly (S2(5)=30). Composite nonresonant cases additionally require simultaneous higher p-adic control. Pairing j and n−j leaves an even-power sum rather than forcing a nonzero residue, so the source's odd-power cancellation does not close this gap.

The small modular check5≤n≤2001, n≡1 mod4, found no zero. It is strictly weaker than the inherited20000 computation and is retained only to validate exact exponent/endpoint arithmetic. No discovery or coverage gain comes from it. The actual mathematical effort was the local obstruction and prime Bernoulli reduction; neither resolves the universal nonexistence question. Park; no Lean surrogate.

## 405708: source already gives full scope

Read Xu–Dong–Xu2609.34616v1 Theorem1.4, Corollaries1.5–1.7, §2 definitions of shifted adjacency Q and matrix-tree expression, and the complete §5 proof of Theorem1.4 and Corollary1.5 through the converse equality argument. In that proof, convex spectral correction plus trace inequalities bounds log τ/n^((n−3)/2) by−2A_q h, where h=m_q−e(G); equality forces diagonal corrections0 or1 and Q²=qI+J, yielding a polarity incidence matrix. Corollary1.5 with h≥0 gives the bound; h=0 gives exactly q+1 absolute points and hence the orthogonal polarity condition. Disconnected graphs have τ=0, strictly below the positive bound. The reserved exact-edge class is a specialization, already covered for every integer q≥2; excluding7,9,11,13 only weakens that specialization. Therefore no new result is possible here. This exclusion is based on actual concluding proof bodies, not the abstract. Auxiliary analytic Lemmas4.2–4.3, external projective geometry facts and the full proof dependency tree were not audited. This is preprint-body confirmation, not a separately read publisher version.

## Additional recovered definitions

406147: OEIS A185150/internal defines a(n) as the number of odd primes p strictly between n² and(n+1)² with Legendre(n/p)=1, offset1. Positivity for every n>0 implies Legendre's prime-between-squares assertion by forgetting the symbol condition. This implication explains the difficulty; it is NOT a known-result exclusion. The linked Sun1211.1588v1 was fetched but predates the December2012 OEIS conjecture and its inspected text does not state this exact target. No proof-body claim for406147. Need a uniform prime-in-short-interval theorem with the additional residue condition or an exact counterexample; none obtained.

405048: read the actual OWR2026 Kwan/Hunter/Sauermann report pp20–22, permanent definition, Theorems1–2, and the paragraph distinguishing sign entries from general distributions. The zero-row exponential lower obstruction in their general distribution is unavailable for ±1 entries. Transplanting it would widen the scope and is invalid. This report contains no full super-exponential proof, and its theorem proof itself is not printed/read here. Retain the original park.
