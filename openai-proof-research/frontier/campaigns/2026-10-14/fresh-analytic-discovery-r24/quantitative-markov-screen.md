# Family 327: quantitative renorming screen

Myeongjin Kang; no affiliation. Original prose CC BY 4.0. Third-party files in `private/` are evidence, not licensed by this note.

**Disposition: no substantial candidate and no full target frozen.** The uniform existence statement below is a technical direct-sum consequence. The explicit finite-to-renorming interface remains unpaid. This is a pre-freeze screen, not a proof of an explicit modulus or a replacement of an earlier frozen target. The campaign count is unchanged.

## 1. Exact source operation

Family 327, *Nontrivial Markov Type Forces Superreflexivity*, is read at commit `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`; all its statements and proof operations are stipulated. Its entire 1020-line `build/main.tex` was read. The complete preprint tree has only this manuscript in the exact title family, with one PDF, one main TeX body, bibliography and figure. This is not a claim that all differently titled Banach manuscripts were semantically exhausted.

For p>1 and finite K, let M_p(X)≤K mean that every finite stationary reversible chain and every map f from its states to X satisfies

    E ||f(Z_t)−f(Z_0)||^p ≤ K^p t E ||f(Z_1)−f(Z_0)||^p.

The source proves X superreflexive. Its ordered-norm lemma first obtains a spreading norm N on c00 with contractive adjacent merging, finitely representable in X. Its finite-walk proposition gives, for every integer n, unit odd edge labels with

    P(N(sum of n labels) ≥ n/24) ≥ 3/20.

The lattice lift in the odd-edge-label lemma transfers the original Markov inequality to these labels. Consequently

    (3/20)(n/24)^p ≤ K^p n.

Thus the contradiction time can be chosen as any integer

    n > [(20/3)24^p K^p]^(1/(p−1)).                       (1)

If the labels are transferred through an embedding of distortion D, replace K in (1) by DK. This is just the source's displayed contradiction, not a new estimate.

The finite chart argument is already constructive at the level of finite Ramsey numbers. It specifies L=8(n+1), transition failure probability 1/(10n), a finite landmark set formed from words of length at most n, and a chart dimension B supplied by finite order averaging. Its oscillation compression gives N(G)≥ell D_L/6 on a successful trajectory. None of this is a new operation here.

## 2. Uniform existence is already a routine consequence

For each p>1 and finite K there is an integer j≥2 such that **every real Banach space X with M_p(X)≤K**, with no separability or dimension restriction, has a norm |·| with

    ||x|| ≤ |x| ≤ j||x||,
    delta_|·|(epsilon) ≥ j^(−1)(epsilon/2)^j    (0<epsilon≤2).       (2)

No explicit value of j is asserted.

Proof. Write P_j for (2). These properties are increasing in j: both distortion and the allowed modulus weaken. Pisier's classical power-type renorming theorem, after rescaling a norm, says every superreflexive space has P_j for some j. More explicitly, a modulus c epsilon^q is at least j^(−1)(epsilon/2)^j whenever j≥q and j≥1/(c 2^q), and the norm equivalence is accommodated by increasing j.

If the claim fails, choose, for every integer j≥2, a real Banach space X_j with M_p(X_j)≤K that fails P_j. Form Y=(direct sum_j X_j)_p. For any finite-chain map f=(f_j), Tonelli gives

    E ||f(Z_t)−f(Z_0)||_Y^p
      = sum_j E ||f_j(Z_t)−f_j(Z_0)||^p
      ≤ K^p t sum_j E ||f_j(Z_1)−f_j(Z_0)||^p.

Hence M_p(Y)≤K. The stipulated theorem makes Y superreflexive; Pisier gives P_J for one integer J. Restrict this norm to each coordinate X_j. Its equivalence constants do not increase and its convexity modulus does not decrease. For j≥J, X_j therefore has P_J and hence P_j, contradicting its choice. This proves (2). The zero-space case is harmless (empty modulus tests can equivalently be written as the midpoint implication). The proof is valid for all p>1, including vacuous or trivial classes; no silent p≤2 restriction was used.

This deduction uses the source theorem, classical renorming, direct-sum stability and a diagonal contradiction. It does not isolate a new Banach construction or a quantitative rate. Its statement is more uniform than the headline, but the operation is routine. It is not nominated.

## 3. What the closest quantitative primary proof already pays

Joerg Wenzel, *Superreflexivity and J-convexity of Banach spaces*, arXiv:math/9710204v1, was read in full (14 extracted pages). Its J_n(X) measures the failure of a finite signed partial-sum test. Its S_n(X) is the least factorization norm of the summation operator from ell_1^n to ell_infinity^n through X.

Theorem 4 and its proof correct an approximately triangular pairing matrix to an exact summation factorization. Theorem 5 takes a bounded summation factorization at a sufficiently large N, chooses minimum-norm vectors with alternating plateau constraints, uses two Ramsey thinnings to align their norms, and forms overlapping interval systems yielding a small J_n. Its explicit N is a double Ramsey number, bounded by an iterated exponential tower whose height depends on the factorization norm and the desired defect. Corollary 6 combines this with the J-convexity comparison for L2(X).

These are actual finite constructions, not merely qualitative superreflexivity citations. They already pay the general operation 'turn long triangular arrays into finite convexity defects using Ramsey theory'. They do not estimate M_p(X) from a finite factorization or turn a specified M_p bound into the subdivision-invariant norm needed by the pinned walk. The direction of Theorem 5 must not be reversed to invent that estimate.

Pisier's author-hosted notes, Chapter 4, Theorem 4.1 and Corollary 4.7, supply the power-type renorming and martingale characterization used in §2. The inspected proof route uses uniformly convex basic-sequence estimates, passes to L2(X), and improves the moment inequality through Lemma 4.12 before renorming. This classical operation starts with convexity or martingale control; it does not supply the missing finite Markov-to-convexity modulus. Only the specified portions in the read record were inspected; the original 1975 article was not separately retrieved.

## 4. Exact unpaid interface

Appendix A of the stipulated source has two limiting stages. The first takes a diagonal Ramsey spreading limit of increasingly long triangular arrays. The second sets N(a)=lim_J N0(F_J a), where F_J splits each coefficient into J equal pieces. Monotonicity, uniform convergence on each fixed coefficient cube and the prefix lower bound allow finite representability and exact subdivision invariance. Convexity of t↦N(...,t,s−t,...) then gives exact contractive merging.

An explicit version of (2) would need bounds, in terms of p and K alone, that replace those limits by finite arrays while keeping enough accuracy for **every** label and block compression used by the finite chart walk. The chart dimension B depends on n and the Ramsey construction. A merely pointwise subdivision approximation, or a bound only for a fixed coefficient vector, is not the needed uniform assertion. The signed merges and common one-step normalization also have to survive. Neither the source's qualitative compactness nor (1) provides this rate.

Monotone subdivision energies suggest finite telescoping or metastability as a possible proof-mining device. That suggestion has not been developed into a uniform simultaneous error estimate and is not a lemma of this packet. In particular, no absence-of-rate example is claimed: this report identifies a missing proof, not impossibility of an effective theorem.

Even if a very large explicit modulus were extracted by these existing Ramsey/subdivision operations, its substantiality would need a separate comparison. An explicit parameter extraction is not automatically a new contribution. There is no substantial mechanism currently established beyond the stipulated construction and the primary antecedents.

## 5. Eligibility and stopping decision

This is distinct from I12's sphere-isometry stability, I88's approximation/absorption/diamond targets and I90's anchored rank construction. Those records were checked at the stated ranges. I90/I93 already used family329's signed entropy compression as a comparison; that family was not selected here. Family085 strict-BV continuity, family095 hyperbolicity regularization, family076 compatible ultraflat prefixes and family154 mixing averages were rejected at the historical screen, not re-nominated.

A prior r11 inventory described 327 as unused; that statement is only a lead. The current bounded title/mechanism search and explicit older-chain comparison found no developed 327 quantitative-renorming chain. This does not establish exhaustive historical or worldwide novelty. Since §2 is technical and §4 unproved, no eligibility inference is used to nominate a result.

No full target was frozen, no result counted, and no formal/manuscript/publication work was begun. AB194, 375 and other earlier sealed scopes remain unchanged. Parent098 and B8C were not touched.
