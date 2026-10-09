# H042 shared relations — raw Claude report

Unaccepted proposer report; independent mathematical and cost review pending.
Task: `node:delegated-task:command%3Amcp%3A3485a768-6d4e-4fa2-9a1d-6d44c46c29fb%3Adelegate-task%3Aecdloop-h042-shared-relations-opus-20261009-r1`
Provider: claudeAgent / claude-opus-5-5. Completed.

I've finished the reads (the loop/team docs, STATE, the H041 dispositions, and fresh primary reads of PKM §2.2–5 and two recent ePrint abstracts). Here is the report.

# H042 report: shared relation collection, sparse elimination and factor-base geometry

**I found no new public operator in this lens with a credible exponent or complete-work gain.** Verified improvement remains NONE and the exponent is still 1/2. Below are the mechanisms I worked through, each scoped to the construction named; none of them is a general exclusion. One low-priority card is left open.

## Primary reads
- **PKM2016 paper (fresh read of §§2.2–5)** ([PDF](https://people.maths.ox.ac.uk/petit/files/16PKC_primeECDLP.pdf)):
  - Algorithm 1 (step 4b) builds one system per random R=aP+bQ.
  - The target X enters only through S_{m+1}(x_{11},…,x_{m1},X)=0. The L_j chain is the same for every target.
  - V is either a subgroup of F_p^* of smooth order (§3.3), or the x-coordinates of a coset of H ⊂ E'(F_p), where E' is an auxiliary curve of smooth order. In that case L comes from a Vélu isogeny chain (§3.4).
  - The cost is P(p,m) + m!·p/(deg L)^{m−1}·T + (deg L)^ω. The paper says nothing about reusing work across attempts, sieving, or large primes.
  - The §4 experiments are m=2 only. §5 reports that the plain Semaev system S(x_1,x_2,X)=0, L(x_1)=L(x_2)=0 with L=∏_{α<B}(x−α) solved faster than their structured systems at comparable sizes.
- **Joux–Vitse, F4 trace variant** ([ePrint 2010/158](https://eprint.iacr.org/2010/158)): this is the known prior art for reusing algebraic work across decomposition attempts. A trace is computed once and replayed for each system of the same shape. I read the abstract and search summary only, not the full text.
- **Hu 2024** ([ePrint 2024/1923](https://eprint.iacr.org/2024/1923)): abstract only. It analyses problems in the PKM/Momonari–Kudo line and proposes a "pseudo-index calculus". It states no complexity.
- **McGuire–Mueller** ([ePrint 2017/1262](https://eprint.iacr.org/2017/1262)): abstract only. It describes an index calculus with fast summation-polynomial evaluation and no Gröbner bases. The O(p) bound and the "(m−1)-multiset, check the sum" description come from a search snippet; I did not verify them in the PDF.
- Not freshly read: the Galbraith–Gebregiyorgis 2014/806 symmetry-breaking factor base, the Gaudry 2009/Diem Frobenius orbits, and the Gaudry–Thomé–Thériault–Diem double large prime method. Treat any attribution to them below as unverified.

## Mechanisms worked through

**1. Shared elimination or materialising the decomposable set. Rejected for this construction.**
- *Operations:* compute or represent the set W of decomposable x-values (the roots of the elimination polynomial E(X), or the m-fold sumset of V). Then test every attempt X_i together, by multipoint evaluation or hashing.
- *Gain source:* per-target work drops to polylog.
- *Invoice:* W has density σ, so the representation costs at least about σp. Collection needs B/σ attempts. The total is at least σp + B/σ ≥ 2√(Bp), which is above √p.
- *Splitting:* writing m=k+l to test R ∈ W_k + W_l just turns this into generic 3-list membership.
- *Limit of the claim:* this covers only constructions that build or evaluate a representation whose size grows with the number of decomposable values. It does not cover per-system solvers.

**2. Sieve over relations among factor-base points only. Rejected as enumeration.**
- *Operations:* a zero at a factor-base point is a linear condition on the coefficients of f ∈ L(nO). A relation is n factor-base points lying on one hyperplane of the elliptic normal curve in P^{n−1}.
- *Missing piece:* nothing makes the high-multiplicity points of this hyperplane arrangement cheap to find. Enumerating (n−1)-subsets costs B^{n−1}, which is about q.
- *Prior art:* the McGuire–Mueller enumeration variant appears to be close, per the unverified snippet.
- Large-prime pairing on these relations is a birthday search on about p values, so it is generic.

**3. Sumset closure through a structured factor base. Scoped obstruction, not a candidate.**
- PKM's V inherits structure from a group G' (F_p^* or E'). Sumsets of V would stay structured only if that structure were compatible with E's group law.
- Correspondence-induced relations, such as summing the factor-base points over cosets of a subgroup H_j, factor through Hom(G', E).
  - Hom(G_m, E) = 0.
  - Hom(E', E) = 0, because isogenous curves have the same number of F_p-points. E has prime order q and E' has smooth order, so they cannot be isogenous.
- So these sums give no free relations. This holds for any choice of auxiliary curve, including via the genus-2 quotient v²=fg of the fiber product, since any composite E'→J''→E is still in Hom(E',E)=0.
- Factor bases with structure on E itself, i.e. generalised arithmetic progressions {Σ j_i G_i}, reduce to generic multi-base BSGS.
- *Limit of the claim:* this does not exclude factor bases with non-homomorphic structure, or better per-system solving.

**4. Reusing target-independent work (F4 trace).**
- This is known (Joux–Vitse). The only target-independent block is the ideal of V^m defined by the L-chain. Per attempt, you still have to find the zeros of S_{m+1}(·,X) on V^m, which is the single-system problem assigned to another role.
- *Gain:* at most a constant or polylog factor in d. It needs the trace replay itself to cost less than p^{1/2−1/m}.

**5. Rank and sparse elimination.**
- For one ECDLP you only need a left-kernel vector involving Q. For random m-sparse rows, the number of relations needed falls only by a constant (2-core / XORSAT-type thresholds). I did not compute those constants.
- With m≥5 and a B² linear-algebra cost, linear algebra is not the bottleneck under the corrected gate (it needs d < 3/10 at m=5).

## The one remaining card (low priority, constant/polylog factor only)

**Known-log orbit closure or multiplier patterns.**
- *Operations:* take a factor base V = ∪_{i<t} [ℓ^{−i}]S_0, or allow decompositions R = Σ c_i P_i with c_i in a small public set C, using the x-coordinate map of [c] inside S_{m+1}.
- *Gain source:* the number of unknowns and relations drops by a factor t, linear algebra by t², or the decomposition probability rises by |C|^m against the same B.
- *Costs:* the x-map of [ℓ^t] has degree ℓ^{2t}, and only |S_0| of its roots are rational. So the extra roots over the algebraic closure grow by about ℓ^{2t} per variable. That inflates system size and spurious solutions, and t^m (or |C|^m) pattern systems have to be solved.
- *Expected outcome:* at most polylog t. It cannot change the exponent, and at m≥5 it only shrinks the term that is not dominant.
- *Prior-art distinction:* this is the prime-field analogue of Frobenius-orbit factor-base reduction (not freshly read). The new element is using [ℓ] on E, with known log ratios.
- *Cheapest decisive falsifier, on paper:* compare degree and rational-root count of the composed L for t=1,2 at m=2, against the PKM Table 4/5 Gröbner degrees. If the per-system degree grows faster than the factor-t saving, the card is closed.

## Answer to the root's question
I could not find an explicit form of reuse that changes the paid, amortised collection cost for one ECDLP once rank and target dependence are charged:
- Target-independent sharing is limited to the L-chain block (mechanism 4, known prior art).
- Materialising the decomposable set costs at least √(Bp) (mechanism 1).
- Algebraic-group closure contributes no free relations because Hom(G', E) = 0 (mechanism 3).
- Sparse rank savings are only constant factors (mechanism 5).

Whether the exponent can move still depends on the per-attempt solving cost d, which is assigned to the dedicated single-system role.

I did no runs, edits, imports, child agents or commits, and I did not touch H006, H038, H034 or H039.
