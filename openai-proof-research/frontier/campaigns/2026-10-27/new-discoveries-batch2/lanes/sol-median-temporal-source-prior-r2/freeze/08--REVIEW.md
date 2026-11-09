# Independent preliminary review: averaged temporal majority counterexample

No acceptance or count. Administrative snapshots say 9 additional, 39 total, next 40. Root alone decides and counts. Solo review; no child, git, public, browser, MathDB, Lean or manuscript operations.

Verdicts:

- SOURCE: PASS for the literal arXiv:1911.08613v2 Conjectures 3.1/3.2. Published-version equivalence remains HOLD.
- MATH: PASS, independently reconstructed exact certificate. The derivative at vertex 1, p=2/5, t=8 lies strictly between 18/1000000 and 19/1000000.
- SUBSTANTIVE: survives this preliminary screen. No complete routine source/classical adaptation yielding an ALL-order averaged finite counterexample was identified in the bodies inspected. This is not an acceptance recommendation based on graph size or computational effort.
- NOVELTY: HOLD, bounded no-duplicate finding only. Current public registry and full citing literature clearance are unavailable; journal body not read. No worldwide-priority assertion.
- FORMAL-FEASIBILITY: plausible, with a substantial explicit stochastic/source bridge required; no literal formal endpoint exists and no formal PASS is claimed.

## Literal source and chronology

Actual v2 PDF was frozen before scientific reading and independently converted with pdftotext. Section 2, PDF pp7–9, defines a locally finite possibly infinite graph (so finite graphs are included), independent rate-one clocks, and addition of the vertex itself to the median pool precisely when its degree is even. Introduction p2 explicitly identifies this with retaining the current Boolean spin on a neighbor tie. Initial spins are iid Bernoulli(p); clock randomness is also averaged. There is no transitivity hypothesis on Conjecture 3.1: it says any graph, vertex, alpha<=1/2. PDF p10 Conjectures 3.1/3.2 give the literal temporal assertions. Nothing in this witness resolves the distinct p-convexity/density assertions 3.7/3.8, PDF p13.

Proposition 2.2, p9, gives the exact threshold identity for [0,p]. Conjecture 3.1 uses [0,alpha). This discrepancy is null here: every opinion at every finite update time is one of the ten original continuous uniforms. The probability that any original equals fixed 2/5 is zero; thus neither endpoint convention changes any marginal, simultaneously over all times. At even-degree vertices majority of neighbors plus the old bit is exactly strict neighbor majority with ties retaining the old bit.

Current primary arXiv abstract/history retrieved 2026-10-30 09:09 UTC: v1 submitted 2019-11-19 22:21:23 UTC, latest v2 2023-01-02 16:49:15 UTC; PDF cover is dated January 3, 2023. Metadata lists SPA 155 (January 2023), 437–458, DOI 10.1016/j.spa.2022.10.015. Metadata is not verification of the journal proof body. No ScienceDirect retry was made. The complete candidate certificate predates this review (original files dated October 30 local session); no earlier public counterpart was established. Current queries and precise response hashes are in current-access.json; source hashes are in SOURCE-HASHES.md and freeze.json.

## Independent mathematics

independent_check.py transcribes the displayed 19 undirected edges into tuple states, constructs neighbor lists, includes the vertex in even-degree voting pools, and propagates integer masses forward. It imports neither candidate update arrays nor candidate coefficients. Candidate data is consulted only after all independent coefficients are generated. Vertex identities and the entire edge set agree. Degrees are 3,4,4,6,3,6,3,2,4,3, summing to 38. States are exactly the 1024 Boolean tuples; bit index 1 is the observed vertex.

For each state, summing all ten deterministic update destinations defines T on observables. Independent rate-one clocks have total rate ten and iid uniform vertex marks, so Q=T-10I. Updates that do nothing still occur as marks; multiplicities are retained in every mass step, including equal destinations. Thus T^k includes every one of the 10^k words, with its multiplicity, rather than just effective jumps or selected schedules. f(s)=s_1 and g=Qf have |g|<=1 because only mark 1 changes f. Starting mass w(s)=2^popcount(s)3^(10-popcount(s)) sums to W=5^10. The code checks mass W10^k and |c_k|<=W10^k for every k=0,...,240, where c_k=w T^k g. Forward c_k is computed as total mass of ones after one more T step minus ten times its current mass, and separately checked against the drift dot product. All 241 coefficients agree exactly with certificate-results.json; all A,B,C,D,W agree too.

The finite Poisson law gives m(t)=exp(-10t)/W sum t^k wT^kf/k!, an absolutely locally uniformly convergent analytic series. Equivalently use the finite matrix exp(tQ). Termwise differentiation gives m'(8)=exp(-80)/W sum 8^k c_k/k!. This is an ordinary finite-state theorem, with no sampled-clock approximation.

Put F=240!, A=sum_{k=0}^{240}8^k(F/k!)c_k and B=sum_{k=0}^{240}80^k(F/k!). For k>=241 each successive exponential term ratio is <=80/242, hence R=sum_{k>=241}80^k/k! <= (80^241/241!)/(1-80/242)=C/(DF), with C=121*80^241 and D=19521=241*81. The omitted signed numerator has absolute value <=WR. Thus S=sum 8^kc_k/k! lies in [(DA-WC)/(DF),(DA+WC)/(DF)], and exp(80) lies in [B/F,(DB+C)/(DF)].

The important sign check DA-WC>0 passes independently. Therefore dividing positive numerator bounds by positive exponential bounds yields lower (DA-WC)/(W(DB+C)) and upper (DA+WC)/(WDB). The checker verifies the exact strict integer comparisons

    1000000*(DA-WC) > 18*W*(DB+C)
    1000000*(DA+WC) < 19*W*DB.

No decimal eigenvalue or numerical exponential is evidence. A positive derivative at an interior time contradicts nonincreasing behavior directly by right difference quotients; analyticity also supplies a nearby interval of strictly increasing m. This proves the full universal temporal conjectures false, not a restricted-clock substitute.

## Strongest substantive objection and closest bodies

The strongest objection is that source Proposition 3.6 already constructs a counterexample and standard uniformization might merely package it. I read its complete proof, PDF pp11–12: K_(3,m), m odd and sufficiently large depending on p, updates one high-side vertex, every low-side vertex, then that same high-side vertex. The first marginal is the binomial-majority tail p1; the last is p^2+2p1 p(1-p)>p1. Its conclusion is for this prescribed sequence. Under iid rate-one marks that sequence has positive probability, but the derivative is a signed average over every word; its positive contribution gives no bound on the negative contributions. Conditioning on it, changing relative rates, or installing externally staged updates would change the conjectured law. No complete construction that forces this schedule with an iid-initial, simple, equal-rate graph and controls all other histories was supplied by this proof or found here. The source mechanism is relevant motivation, not already a complete averaged counterexample. Candidate finite bipartite sweeps are not a proof that such an adaptation is impossible.

Mossel–Neeman–Tamuz arXiv:1207.0893v1, July 4, 2012, Lemma 5.1 and its entire proof, PDF p13, use biased influences/Efron–Stein to compare a monotone balanced Boolean function with a dictator. Their P_p notation assigns probability p to zero; after spin complementation the statement gives the source bound m(t)<=p for p<=1/2. It supplies no comparison between the correlated laws at two different times: the later law is not a fresh iid product input. Thus it cannot remove a positive temporal derivative compatible with staying below p. Source Example 3.9, p13, has a nonconvex biased Boolean expectation; it supplies neither a temporal comparison nor an averaged graph realization.

Additional actual primary coverage: Amir–Baldasso 1902.03349v2 (January 30, 2020), PDF pp1–3 Theorems 1.1–1.3 and their accompanying proof outline, concern percolation criticality, strict lowering and continuity of the spatial threshold on Z^2. Alves–Baldasso 1912.06524v2 (June 10, 2022), PDF pp1–4 Theorems 1.1/1.3 and proof discussion, concern crossing windows and subcritical arm decay. Their statements do not imply a finite-graph temporal counterexample; I do not claim a line-by-line audit of all their proofs. The complete closest mathematical proof bodies actually read are source Proposition 2.2, Proposition 3.6, Example 3.9 and MNT Lemma 5.1. Damron–Sen 1904.11625v1 was identified by current primary metadata only, not read and not cleared.

Uniformization, matrix exponentiation and geometric tail bounds are classical methods. Standardness of the method alone is not a complete adaptation proving the signed-average endpoint. Conversely witness size is no novelty argument. This review finds a real additional signed-average fact in the displayed witness and no completed source shortcut, while leaving broader novelty on HOLD.

## Minimal formal interfaces, if root continues

1. A finite simple graph on Fin 10, exactly the listed edges; Boolean single-vertex updates; proof of the even-degree self-pool/tie-retain identity.
2. A source marginal interface justified by the actual independent rate-one Poisson law: total-ring Poisson(10t), independent uniform marks, and iid initial weights. Alternatively a fully proved finite CTMC law/generator uniqueness interface giving exp(tQ). Naming a finite sum “source marginal” without this bridge is insufficient.
3. The finite operator and mass identities, g bound, exact coefficients and rational integer inequalities, with kernel-checkable arithmetic and no native_decide/axiom shortcuts.
4. Absolute convergence/differentiation, the geometric exponential remainder, positive interval division, and positive derivative excluding nonincrease.
5. The median threshold coupling plus the fixed-endpoint null event to transfer the conclusion to literal 3.1; 3.2 also needs its law interface.

No Lean work or manuscript was performed. Feasibility does not certify that these interfaces are already in a library or cheap to prove.

## Integrity and bounded failures

Scientific inputs were copied and original/copy hashes compared before reading; exact bindings are in freeze.json. The initial freeze was broader than scientifically necessary (96 immediate files including unrelated scouting references), but did not recurse through historical trees. Those files have no implied actual-body coverage. Administrative files are snapshots only. Native bounded reads and apply_patch were used; all Python, extraction helpers, HTTP retrieval and hash operations ran through the specified immutable helper_guard.py, with OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 and fixed 512MiB AS/group RSS, CPU210, wall230. No candidate script was run in its original lane, and no candidate checker is independent evidence.

Own exact run passed at approximately 17MiB sampled group RSS and 0.24s guard wall. Source extraction/current access run passed at approximately 41MiB and 1.12s. No cap increase. Candidate manifest entries are separately checked against frozen files (administrative entries against snapshots), without running candidate verify.py. Final review manifest excludes itself and verification-receipt.json; verify.py is a separate guarded process after final writes and replays the independent implementation with before/after hashes.

Inherited failures remain in frozen/FAILURES.md and logs: unavailable networkx, fixed-cap allocation failure on the larger exploration, incomplete motifs coverage, and no counterexample in finite bipartite tests. No failures were discarded. Own live requests all returned HTTP200, but broad arXiv phrase matching returned irrelevant astronomy/plurality entries; those are not clearance evidence. No exact later resolution was identified in the relevant returned bodies/metadata; later resolution is not ruled out. Denied GitHub API/raw/codeload/diff/patch, ScienceDirect and Google challenge routes were not retried. No registry head claim, inaccessible historical-interval claim, HEAD loop, proxy, TLS-disable or browser bypass. Full current registry, published-body comparison, comprehensive citations and worldwide priority remain unresolved limits.
