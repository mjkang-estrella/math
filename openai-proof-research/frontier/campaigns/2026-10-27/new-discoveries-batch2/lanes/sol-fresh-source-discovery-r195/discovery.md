# r195 — higher convex-order separation: unresolved, zero nominations

## Exact source and status

Yuting Su, Meng Guan, Zhenfeng Zou and Taizhong Hu, *Separation Theorems for Increasing Convex and Weak 3-Convex Orders on Real-Valued Random Variables*, https://arxiv.org/pdf/2610.37025, Conjecture 5.1, p13. Latest obtained abstract history https://arxiv.org/abs/2610.37025 lists only v1, submitted 27 October 2026 11:01:33 UTC. The PDF title page says October 28, 2026; retain this distinction. PDF SHA256 d79e5cd0012d2ea0bc60934e4de1e5d44e64e351dc84b08894a818a31434316b. No journal version or DOI for this new source authenticated. Exact retrieval UTC, URLs, bytes and hashes are in http.jsonl. All fourteen extracted pages were read, including definitions, complete Theorems 3.3 and 4.1 constructions, Example 4.2 and discussion/references. PDF extraction issued font warnings; primary PDF bytes remain authoritative.

For every integer n>2 and real random variables X,Y with E|X|^(n−1),E|Y|^(n−1)<infinity on an atomless probability space, the conjecture is

    X ≤_(n-wcx) Y iff there is Z in L^(n−1)
    with X ≤_((n−1)-cx) Z ≤_(n-cx) Y.

Write C_j(W,t)=E[(W−t)_+^j]/j!. Weak n-convex order means equality of moments 1,...,n−2 and C_(n−1)(X,t)≤C_(n−1)(Y,t) for EVERY real t. Full n-convex order additionally requires equality of moment n−1. Thus Z must match X,Y through moment n−2 and match Y at moment n−1. No boundedness, nonnegative support, density, finite-support or n=3 restriction is permitted. The n=3 case is the source's public Theorem 4.1, not a fresh target. Conjecture 5.2 is recorded as a related stronger decomposition proposal but is not a second selected slot.

Qualification: the source explicitly says the 2014 higher-order proof is incomplete. That diagnosis is the authors' claim, NOT independently established here. The closest cited predecessor is Denuit–Liu–Meyer, *A separation theorem for the weak s-convex orders*, Insurance: Mathematics and Economics 59(2014)279–284, DOI 10.1016/j.insmatheco.2014.10.008 (RePEc metadata). Its actual body was not obtained. RePEc supplied a distinct legitimate UCLouvain discussion-paper link; its institutional hostname failed DNS resolution. No retry, ScienceDirect, challenge bypass or alternative denied endpoint was used. Consequently the all-order question is a fresh PROJECT investigation and explicitly conjectural in the read source; absence of an older proof is not certified. No substantive PASS or novelty clearance is claimed.

## Exact all-order obstacle formulation

Set p=n−2, D(t)=C_(p+1)(Y,t)−C_(p+1)(X,t) and Δ=(E[Y^(p+1)]−E[X^(p+1)])/(p+1)!. Equal lower moments and dominated tail estimates give D(−infinity)=Δ and D(+infinity)=0. Weak order gives D≥0, hence Δ≥0.

The missing construction is equivalent to finding an integrable h≥0 such that

    integral_R h = Δ;
    integral_t^infinity h ≤ D(t) for every t;
    C_p(X,.)+h = C_p(Z,.) for a probability law Z in L^(p+1)
    having the common moments through p.

Necessity: take h=C_p(Z)−C_p(X). The first order gives nonnegativity; Proposition 2.2's moment identity gives its integral Δ; Tonelli applied to each positive-part transform gives the tail identity C_(p+1)(Z)−C_(p+1)(X)=integral_t^infinity h. The terminal order is precisely the upper obstacle. Conversely these three requirements give the first order, the terminal transform inequality and, by the same moment identity, the last moment equality. This accounts for ALL n, t, moment and integrability conditions; it does not construct h. If Δ=0, h=0 and Z=X already work, so the substantive existence problem is Δ>0.

The last requirement is essential: for p≥2 a valid C_p is C^(p−1); distributionally (−1)^(p+1) times its (p+1)-st derivative is a positive probability measure, with the appropriate left polynomial and right vanishing boundary behavior. Finite moment p+1 is an additional tail condition. Merely finding a nonnegative mass allocation below D does not guarantee these derivative and boundary constraints. For instance the running infimum H(t)=inf_(s≤t)D(s) has the right monotonicity for a survival mass profile, but differentiating it may give atoms or a function that fails the transform conditions. No theorem repairing this uniformly is supplied.

## Exact source-admissible obstruction to max-gluing

Let X be equally likely ±1 and let Y take −2,0,2 with probabilities 1/8,3/4,1/8. Both laws have moments (mean,second,third)=(0,1,0). Define unnormalized Q_j(W,t)=E[(W−t)_+^j]. For a=|t|,

    Q_3(Y,t)−Q_3(X,t) = 0                          if a≥2,
                         (2−a)^3/8                 if 1≤a≤2,
                         (4−6a²+3a³)/8              if 0≤a≤1.

Direct expansion proves the formula on t≥0; symmetry and equal cubic polynomials extend it to negative t. The last polynomial decreases from 4 to 1 on [0,1], since its derivative is −12a+9a²≤0. Hence X≤_(4-cx)Y, in particular this pair satisfies the full weak-order hypotheses at n=4.

Nevertheless max(Q_2(X,.),Q_2(Y,.)) is not Q_2 of ANY probability distribution. At zero the two functions equal 1/2. Their derivative difference is 1/2; consequently X dominates immediately to the left, Y to the right. The maximum has left derivative −1 and right derivative −1/2. Every Q_2 transform of an L² law is continuously differentiable with derivative −2E[(W−t)_+], by dominated convergence. This corner is impossible. Translating both laws by 2 also gives a nonnegative-support example. It defeats direct max-gluing even on source-admissible data; it does NOT refute Conjecture 5.1. Here Δ=0 and Z=X is a valid separator. The source's order-three proof uses ordinary convex call transforms, where corners are allowed; the higher regularity obstruction is specific to extending that mechanism.

An additional exact method barrier concerns stationary excess inversion. For nonnegative W with 0<EW<infinity its stationary-excess density is P(W>t)/EW on t≥0, necessarily nonincreasing. Uniform[1,2] has density 0 then 1 then 0 and cannot be such an image. Distributional inversion would put negative mass at 1 and positive mass at 2. Thus an ordinary separation theorem applied to transformed variables cannot simply be inverted without proving the separator lies in the transform's image. This is a complete range obstruction, not a claim that the unread 2014 body uses precisely this invalid step.

## Classical adaptation challenge and unresolved universal step

The complete applicable classical implication is the easy direction. If X≤_((n−1)-cx)Z, integrate its nonnegative C_(n−2) difference from t to infinity to obtain C_(n−1)(X)≤C_(n−1)(Z). Combining with Z≤_(n-cx)Y and the common moments through n−2 gives X≤_(n-wcx)Y. Finite L^(n−1) moments justify the integrals. This proves sufficiency, not necessity. The source's entire n=3 necessity proof was read early; it uses convexity, maximum/chord construction, a continuous area parameter and a single-crossing endpoint argument. The explicit corner above prevents treating those same operations as valid higher transforms without a new construction.

Translation is a full bridge from a nonnegative separation theorem to any COMMON bounded-below pair: expand (W+a)^k binomially to preserve all required moment equalities, and use C_j(W+a,t)=C_j(W,t−a); translate the resulting Z back. It does not cover arbitrary left-unbounded laws. An approximation extension needs order-preserving approximants with exact lower moments and enough tail control to retain moment n−1 of the separators. Plain clipping need not preserve these conditions. A bounded highest moment alone does not supply that control: μ_R=(1−R^(−q))δ_0+R^(−q)δ_R converges weakly to δ_0 but has q-th absolute moment 1 for every R, while each lower positive moment is R^(j−q)→0. These laws are a precise compactness-method warning, NOT feasible separators for a claimed counterexample. No complete all-order classical bridge is obtained, so there is no shortness-based exclusion.

Outstanding requirement: prove the obstacle lemma with its full probability-transform and tail constraints for ALL source-admissible X,Y and n≥4, or give an exact pair for which no probability-law separator exists. A finite support grid's infeasibility would not rule out arbitrary real-supported Z. No source proof or refutation was obtained.

## Bounded reconnaissance, history and limits

Current math.CA, math.PR and math.MG recent lists were read. Four actual PDFs were obtained before choosing: the separation source; Jia Li's equidistant affine-subspace paper2610.37421 (intro and final questions inspected; unnumbered stabilization direction not selected); Ikeda–Murahara2610.36409 (intro and question search; public moment statements not nominated); Bogosel2610.36382 (intro and question passages, public shape-optimization resolutions not nominated). No abstract-only exclusion or fresh-target padding. Only Conjecture5.1 is sustained. No historical clustering, cosine, Brownian or parked merge-tree investigation is reopened.

r192 original-path history was refreshed with direct records across campaigns, and r189/r191 dispositions and changed Guo/root records read. Raw inventory: 5,119 paths; 3,495 aliases bound by equal bytes AND enclosing original directory/name provenance; 1,624 copied representatives. Of these,125 generated representatives without adequate direct-original qualification are retained as inherited evidence ONLY, not fresh original records. qualified-history.json contains1,497 qualified records. No inference of original provenance from equal content alone. The initial broader corpus remains preserved; screening found zero source aliases even in that superset, hence zero in the qualified subset. Seven r111–113 original documents retained. Seven changed/new representative records identified; these include r193 summary/discovery and root dispositions. This is bounded project coverage, not 5,119 distinct investigations or exhaustive history.

Early exact arXiv/title/author/statement screens had no prior target match. Current lean.up.railway.app/api/data bytes were fetched and screened for exact aliases with zero hits; this is not a fresh OpenAI repository tree/head or proof-body sweep. Denied GitHub routes, ScienceDirect, Google challenges, Crossref/export429 and historical capped intervals remain parked. Bing RSS gave irrelevant Windows-update results and supplies no negative evidence. Missing2014 body materially limits priority/subsumption assessment. No worldwide, all-history, MathSciNet/zbMATH or complete citation-body clearance.

checks.py passes801 exact rational transform controls and32 highest-moment escape controls. Ordinary formulas above establish the method witnesses for all thresholds/parameters; numerical checks do not prove the conjecture. No PROOF.md because there is no complete ordinary candidate. Zero nominations; no Lean, manuscript, count, credit, git, browser, child, MathDB or shared edit. Counts9additional/39total,next40 unchanged; root alone accepts/counts/stages.
