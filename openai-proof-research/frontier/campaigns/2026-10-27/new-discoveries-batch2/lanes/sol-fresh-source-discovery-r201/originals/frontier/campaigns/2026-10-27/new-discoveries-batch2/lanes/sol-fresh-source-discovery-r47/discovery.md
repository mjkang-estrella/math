# r47 — Gaussian Radon target unresolved; credit 0

No qualifying source theorem or refutation, nomination, PROOF.md, Lean investment, paper, or acceptance is claimed. Root owns all gates. Observed counts: 6/30 additional, 36/60 total. Solo, assigned-lane writes only.

## Early primary-claim screen (three leads, at most four)

1. Jan Jekl, JMI19(1)(2025)65–80, DOI10.7153/jmi-2025-19-05, Conjecture1 p77. Literal inequality is sin_p(x)/x < (cos_p(x)+x/2+2)/3, 0<x<pi_p/2. EXCLUDE after reading actual successor Jekl, MIA28(4)(2025)725–738, DOI10.7153/mia-2025-28-42, Lemmas3–5 and Theorem1 p730. Theorem1 proves this exact inequality, including the upper bound1. The x/2 fraction was visually verified on original p77; PDF text extraction transposes it into misleading '2x'. The earlier progress message calling the successor 'stronger' refers to its additional upper bound; the target inequality itself is identical. No rediscovery or domain repair.
2. Ferreira–Simon, arXiv2212.07974v2, actual Introduction/TheoremsA–D and fractional-integration argument read. Wright-density log-concavity is distinct from the already-credited Mills-ratio result, but this source overlaps that campaign's special-function/entropy context. Not selected, not declared settled or novel. No numerical work or endpoint claim. Exact HTML cached for provenance. This was a conservatively abandoned lead, not an exclusion by a badge.
3. SELECT Chan–Kalai–Narayanan–Ter-Saakov–White, arXiv2507.01353v1, Conjecture7.2(2), p16, and actual published journal HTML Section7.2, DOI10.1007/s00454-026-00870-6 (publication7September2026). Read source Theorem1.3 proof, Lemma5.1 proof, Theorem1.1 deduction and concluding question. Published body still states the same question. The boundary n=d+2 is already proved by Theorem1.1 and earns no credit.

## Literal selected scope

For every pair of integers d>=1,n>=d+2, draw independent standard Gaussian X_1,...,X_n in R^d. For 1<=k<=n-1 define

q_k(n,d)=P(conv(X_1,...,X_k) intersects conv(X_{k+1},...,X_n)).

The question is q_k^2>=q_{k-1}q_{k+1} for every 2<=k<=n-2 (with the empty-group endpoint zero if used). This is the prescribed-label probability, not the distribution of the size of a randomly chosen unique Radon part. Symmetry would then imply source7.2(1). Both conclusions constitute one family. The surviving range n>=d+3 is targeted in full, not a fixed dimension. There is no new result for that range here.

## Closest primary bodies and chronology

* Source v1 submitted2July2025; current abs page lists v1 only. Journal published7September2026. Its actual Section7.2 retains Conjecture7.2. The line-kernel argument of Lemma5.1 handles the n=d+2 case; the conditional association proof for Youden's demon is a probability statement about one Gaussian vector with a prescribed sign event, not automatically an existence event in a multidimensional random kernel.
* Moshe White, arXiv2507.05449v1, 7July2025, actual Section3 pp7–13: Eq(3.2) already gives the exact Crofton representation for these same prescribed partitions. Proposition3.1 proves q_k(n,1)=1-2/binom(n,k); Propositions3.3/3.6 and Eqs(3.6)/(3.8) give intrinsic-volume formulas; Proposition3.7 gives the top-volume expression. Proofs and Conjecture3.9 (unimodality) read. Thus cone reduction and the d1 case are PUBLIC, not candidate discoveries. The 2023 thesis itself was not obtained; this explicit gap prevents any claim of a complete antecedent audit.
* Frick–Newman–Pegden, arXiv2407.02589v1, 2July2024, actual Theorem4 and Section2 Gale-duality argument read. This addresses the unique-partition boundary, not all n,d log-concavity. No validation of all printed ancillary formulas is claimed or needed.
* Kabluchko–Zaporozhets, arXiv1704.04968v3, 27December2019, actual Theorem2.1/Eq(2.3), Proposition1.4(f), Sections2.2–2.4 proof bodies read. These supply classical Crofton/face-angle machinery and Gaussian orthant formulas; no novelty is attributed to them.

## Concrete all-parameter route, with an exact failed sufficient step

Let H={z in R^n:sum z_i=0}, A={1,...,k}, B={k+1,...,n}, m=n-k, and
C_k={z in H:z_i>=0 for i in A,z_j<=0 for j in B}.
The d rows of the sample matrix, restricted to H, are independent isotropic Gaussian vectors. Their common kernel L is a uniform codimension-d subspace in H. A nonzero z in L intersect C_k has equal strictly positive positive/negative coordinate sums; dividing by that sum gives the two convex combinations. The converse follows by subtracting two convex combinations. Therefore the classical representation (already White Eq3.2) is

q_k(n,d)=2 sum_{r=d+1,d+3,...,n-1} v_r(C_k).   (1)

Here is a positive face-angle expansion useful for assessing an attempted proof. Define
alpha(a,b)=P(Y_1-Ybar>=0,...,Y_a-Ybar>=0,Y_{a+1}-Ybar<=0,...,Y_{a+b}-Ybar<=0),
for independent standard normal Y, with a,b>=1. This is the top internal angle of C_a in a+b coordinates. Put s=a+b and

beta(u,v;s)=integral_R phi(t) Phi(t/sqrt(s))^u Phi(-t/sqrt(s))^v dt,

where beta(0,0;s)=1. Then, for r>=1,

v_r(C_k)=sum_{a+b=r+1,a,b>=1} binom(k,a)binom(m,b) alpha(a,b) beta(k-a,m-b;a+b).   (2)

Derivation: a nonzero face retains a positive and b negative coordinates and has dimension a+b-1. Its internal angle is alpha(a,b). Unused signed normals in H have Gram matrix D(I-J/n)D, where D records the signs and J is the all-one matrix of size n-s. Their coefficient Gaussian has covariance D(I+J/s)D, since (I-J/n)^(-1)=I+J/s. Representing that Gaussian by independent standard coordinates plus one common N(0,1)/sqrt(s) gives beta. Summing internal times normal angles over all faces gives (2). These are classical angle computations specialized to White's public framework, not a substantive new theorem.

The source proves log-concavity of a -> alpha(a,s-a) for fixed s. However u -> beta(u,N-u;s) is log-CONVEX: write it as the u-th moment of Phi(t/sqrt(s))/Phi(-t/sqrt(s)) against the positive measure phi(t)Phi(-t/sqrt(s))^N dt, and apply Cauchy–Schwarz. No log-concave convolution conclusion follows from this combination.

More decisively, the tempting sufficient claim 'every positive-degree row k -> v_r(C_k) is log-concave' is FALSE, even at a degree that appears in (1) for a legitimate positive dimension. Take n=6,r=2. Every relevant face has (a,b)=(1,2) or (2,1), internal angle1/6. The three unused coordinates have common correlation1/4 before sign changes. Put y=arcsin(1/4)/pi. The trivariate orthant angle is 1/8+3y/4 for equal signs, and 1/8-y/4 for a mixed sign pattern (expand the three sign indicators, use central symmetry and the bivariate arcsine formula). Equation(2) gives exactly, in order k=1,...,5,

(5/24+5y/4, 1/3, 3/8-3y/4, 1/3, 5/24+5y/4).

Since arcsin(1/4)>1/4 and pi<4, y>1/16>1/18. Thus 0<v_2(C_3)<1/3=v_2(C_2)=v_2(C_4), contradicting log-concavity at the center. Positivity also follows directly from the positive-angle representation (or y<1/6).

This is NOT a source counterexample. For n6,d1, the actual probability uses 2(v2+v4), not 2v2. White's public q=(2/3,13/15,9/10,13/15,2/3) is log-concave. The higher face dimensions repair the failed row. No claim that numerical evidence resolves any source question is made.

## Strongest objection, falsifier and remaining gaps

Strongest objection: all completed reductions are within White's already public classical framework, and the needed global log-concavity mechanism is missing. Even proving the row claim would not suffice by itself without a shared-sum log-concavity theorem; the row claim is in fact exactly false. This lane has zero discovery credit.

A genuine source falsifier must give actual n,d,k with q_k(n,d)^2<q_{k-1}(n,d)q_{k+1}(n,d), using the WHOLE parity sum in (1), with rigorous probability or angle bounds. The displayed intrinsic-volume valley does not qualify. A proof must establish the full parity-sum inequality for all n,d,k, perhaps through cross-dimensional cancellations or a new conditional association for existence in the full random kernel. Neither bridge is established. Extending the line-kernel proof by just taking unions of sign events is unsupported; positive association under box conditioning does not automatically pass to such an existential event.

Novelty/eligibility also remain unqualified: full thesis, exhaustive citing literature, semantic registry coverage and specialist database audits are absent. No worldwide absence or novelty PASS is inferred from the source retaining its conjecture.

## Current public registries and access limits

Refresh at 2026-10-29 14:38UTC: Omega dev9fabd81524aa5bc037d66794c239ac6b9d2b4e86; compare from r45 dev13540e54dcb7e367c6799640ec15b707fcf2bb18 contains3commits/1changed file, docs/develop/theory/CYCLE_ANDERSON_DEFECT_BLOCK_NODAL_FAMILIES.md. Its full added patch was read: band-factor irreducibility/specialization of defect-cycle matrices, not Gaussian Radon probabilities. Fresh untruncated D5(12552) and Problems(1551) subtree lists obtained. These are named scopes, NOT a whole-dev absence assertion.

Other heads unchanged from r45: Omega main d7af67136d4478875778ac6e75eb5fbb8b3693a5; OpenAI7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a; AIM8729eab98bafe409b66c5e39253bf56569a62327; Countdbf673741a54c7dc9d88a6aec0e8148a538f4a3a. Complete cached scopes reused with exact hash/reuse paths in registry-screen.json; current heads independently fetched. Matching AIM598 and599 actual bodies read. 598 is the selected claim, not a proof. 599 concerns uniform convex samples and a unique-partition size distribution, not the selected Gaussian prescribed-split claim. clopenOP00268 imports598; no novelty inference from its label. Bounded public title/topic searches produced source, author and antecedent leads, not a claimed exhaustive literature screen.

All HTTP fetches in this lane returned200; no403/429/challenge bypass occurred. Springer redirected with cookies_not_supported in its URL but delivered the actual full article including the claim and proofs; exact final URL retained. The thesis is an unfilled literature gap, not asserted inaccessible after an exhaustive search. No browser/account/contact/post/upload actions.

## Reproduction

`bash run.sh python3 check.py` uses Python3, SymPy and mpmath. Passed54 exact inverse-Gram identities, exact symbolic n6/r2 row reconstruction and rational sign threshold,432 finite checks of the already public d1 formula, and4 independent Gaussian common-factor integral diagnostics (45digits, not proofs). About0.7s wall, sampled peak groupRSS54.3MB. Guard imposes AS512MiB per process, sampled aggregate groupRSS512MiB, CPU210s (per-process rlimit plus sampled group sum), wall230s, BLAS1. It kills the process group on failure; unsampled memory/CPU transients and already-reaped-child CPU are not covered by sampling. No blind enumeration.
