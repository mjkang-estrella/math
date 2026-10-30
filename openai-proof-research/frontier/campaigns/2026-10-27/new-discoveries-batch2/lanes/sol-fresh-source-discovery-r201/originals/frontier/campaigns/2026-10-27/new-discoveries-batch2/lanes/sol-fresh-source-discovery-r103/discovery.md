# r103 — Gaussian scale-mixture Fisher minimizers: unresolved

29 October 2026. Solo, no children, no git, only assigned lane written. Credit **0**. Counts remain **8 additional / 38 total**. No PROOF.md, Lean, or paper.

## Early exact duplicate screen

Ancestor and batch AGENTS, ledger, NEXT, prior-campaign-context and pinned upstream/catalogue were read. `audit.py` scanned ALL dates under openai-proof-research, every selected text file whose filename contains SUMMARY/discovery/FINDINGS/PROOF/review/ledger (case insensitive), plus all text files in review paths, with no date/file cap. The frozen inventory contains **120305 files**; identical byte bodies are deduplicated for matching, not removed from the inventory. Exact regexes and all hits are in duplicate-audit.json. Initial buffering failed with MemoryError under the mandated guard; the streaming replacement passed with sampled group RSS499879936 bytes and wall62.43s. Failure retained in failures.md. This is a project screen, never a worldwide priority certificate.

BNT entropy-concavity/norm search:48 distinct matching bodies; Feige/Marsiglietti/Pandey:29; covariogram/Matheron/Godbersen:5. These broad counts include inventory JSON, unrelated references and copied reports. Relevant actual earlier selection is **r94 discovery.md**, which already screened both BNT conjectures and selected Luo Problem10.1. Thus neither BNT conjecture is fresh. Feige and covariogram were search leads only, not read/selected primary candidates; a failed Feige URL is retained and gives no mathematical evidence.

Before Fisher investment, `screen-fisher.py` searched all-date report filenames for exact author names/id and Fisher/mixture/minimizer/Schur terms. Its literal hits include r94's entropy proof comparison, r81's separate lattice-entropy extension problem, and unrelated Cordero-Erausquin–Eskenazis reviews. None is the exact Fisher Question3. `audit-fisher-full.py` repeats this against every file in the frozen 120305-file corpus, including review-directory bodies; its full path hits and failures are retained. No prior-art clearance is inferred merely from a missing word.

## Three actual primary statements screened

1. **BNT Conjecture1**, latest arXiv1509.05926 PDF, §2: for every symmetric log-concave vector X in R^n, v↦exp h(<v,X>) (zero at v=0) is a norm. Allows dependent planar marginals. EXCLUDE AS PREVIOUSLY SCREENED, r94. Read original Proposition1 proof: Ball/Busemann reciprocal-section norm plus maximum-density/entropy comparison loses factor e; it does not give the sharp conjecture.
2. **BNT Conjecture2**, same latest PDF, §2: for every iid pair of real log-concave variables, t↦h(sqrt(t)X+sqrt(1-t)Y) is concave on [0,1]. EXCLUDE DUPLICATE/PUBLIC REFUTATION. Actual Luo arXiv2609.11418v2 HTML was obtained: asymmetric examples at every signal fraction, symmetric examples above4/7, with exact finite Gaussian moment matching. Search snippets showing only the asymmetric v1 are stale. The low-signal symmetric remainder is r94's object, not a fresh nomination.
3. **SELECTED: Eskenazis–Gavalakis Question3**, *On the entropy and information of Gaussian mixtures*, Mathematika70(2024)e12246, published PDF p4, and latest arXiv2308.15997v3 (16 February2024), §1.2. Given any n and iid centered Gaussian scale mixtures X_i=Y_i Z_i, Y_i>0 a.s., characterize ALL unit coefficient vectors minimizing I(sum a_i X_i). This is a different functional and optimization object from entropy concavity or Luo smoothing. The full question includes arbitrary mixing laws, coefficient boundary points, signs and degeneracy; the paper does not impose finite-support mixing here. The natural tentative answer is equal absolute coefficients for a nonconstant mixing law, but that is NOT supplied as a theorem; for a Gaussian every unit vector minimizes. Extended/infinite Fisher cases must also be treated before a full answer.

## Closest actual proof bodies and public scope

Published EG §2 Theorem2 proof (20)–(28) and v3 counterpart were read: entropy's variational formula, Gaussian variance conditioning, concavity of -log g(sqrt(s)), then Hölder for Rényi orders. This is already public and earns no credit. Differentiating an entropy inequality in a Gaussian-noise parameter does not preserve its sign and cannot yield a Fisher comparison without another argument.

EG §3.2 Proposition10 proof (35)–(38), Proposition4's Jensen extension and Corollary6 were read. Fisher information is convex in the DENSITY. The weighted convolution density is not affine in squared coefficients. EG Theorem7 compares to the Gaussian covariance lower bound and controls CLT rates, not which coefficient vector is optimal for fixed n.

Bobkov, *Upper Bounds for Fisher information*, EJP27(2022)paper115, actual published §15 pp37–38, equation15.1 and Proposition15.1 proof, was read. It proves I(integral q dπ)<=integral I(q)dπ using the perspective u²/v and compactness/lower semicontinuity. EG's reference to draft Proposition15.2 should not be confused with the published Corollary15.2. This gives an upper bound by E[1/V], not ordering between two mixtures; ordering upper bounds is insufficient.

Bounded live exact author/question searches located the source and conference restatement, no full Fisher optimizer proof. This is not exhaustive citation coverage and does not certify priority.

## Full-scope mechanism investigated (not finite sampling)

For iid V_i=Y_i²>0 and w_i=a_i², let V_w=sum w_i V_i. Conditioning gives f_w(x)=E φ_(V_w)(x), with φ_v the centered normal density of variance v. Signs of a_i are immaterial. Work first with any finite mixing law bounded away from zero; then all differentiations below are justified by Gaussian domination. No claim extends these differential manipulations to every arbitrary mixing law without an approximation argument.

For any smooth positive reference g with score ρ=g'/g define L_g(x)=-2ρ'(x)-ρ(x)² and K_g(v)=E L_g(sqrt(v)Z). Completing the square and integrating by parts gives

    I(f) >= integral L_g f, with equality at f=g.

Indeed I(f)-integral L_g f = integral f[(f'/f)-ρ]². In particular the exact first variation is dI(f)[h]=integral L_f h for mass-zero variations. At a coefficient vector w,

    ∂i I(f_w)-∂j I(f_w)=E[(V_i-V_j) K'_(f_w)(V_w)].

Freeze f_w on the right. Swapping iid V_i,V_j, with C=sum_(k≠i,j)w_k V_k, makes the right side

    (1/2) E[(V_i-V_j){K'(C+w_i V_i+w_j V_j)
                              -K'(C+w_i V_j+w_j V_i)}].

If this has the sign of w_i-w_j for every n, every iid law and every w, then pair balancing proves diagonal minimization. Strictness and all minimizers would still need separate treatment. At the equal point the first variation vanishes by exchangeability; this alone says nothing about optimality. For n=2 at w=(1/2,1/2), the exact second directional variation is

    E[(V_1-V_2)² K''_(f_equal)((V_1+V_2)/2)].

The usual nonnegative Hessian term in the density vanishes here because the first density variation itself is zero. A negative value of this expression for an admissible iid law is a direct falsifier of the tentative equal-coefficient answer. Conversely, local nonnegativity is insufficient for global optimization.

## Exact obstruction to an overstrong sufficient lemma

One might hope that K_g is convex on all v>0 for every Gaussian scale mixture g. This is FALSE, even when g is itself an equal sum of two iid scale mixtures. This is a ROUTE obstruction, not a refutation of Question3.

Take P(V=1)=9/10, P(V=49)=1/10. Then the equal two-copy sum has variance-mixture values1,25,49 with weights81/100,18/100,1/100. At x=0, the posterior precision P=1/V has probabilities

    2835/2966, 63/1483, 5/2966

at precisions1,1/25,1/49. Let μ,σ²,κ3 be its first moment, variance, third cumulant. For s=x², m(s)=E[P|x=sqrt(s)] satisfies m'(0)=-σ²/2, m''(0)=κ3/4, while ρ(x)=-x m(x²). Hence

    L_g(sqrt(s))=2m(s)+4s m'(s)-s m(s)²,
    K_g''(0)=3[(5/2)κ3+2μσ²]
             = -5500011742996608/171302489627215625 < 0.

Bounded precision ensures smooth right extension at v=0 and dominated differentiation; therefore K_g'' is negative on some positive interval. A formal rational Taylor-series computation independently reproduces this coefficient in check.py. This is not numerical quadrature or finite-grid sign evidence.

**Strongest objection:** the negative-curvature interval is near0, whereas the conditional variance arguments of this very iid model lie in [1,49], and its unequal-pair midpoint is25. Thus this certificate cannot be inserted into the pair-balancing formula as a source counterexample. It invalidates only the unrestricted K-convexity shortcut. Even convex order of V_equal versus V_w cannot be pushed through this particular arbitrary test function without proving its needed restricted averaged inequality.

## Precise remaining gap and falsifier

No sign proof or counterexample is known here for the universal paired expectation above at attainable conditional variances. A complete answer would prove the actual global comparison I(f_w)>=I(f_uniform), characterize equality including Gaussian mixing degeneracy, and extend to arbitrary positive mixing laws/infinite Fisher values; or supply an actual admissible law and coefficients violating the tentative comparison (which alone would still not characterize all minimizers asked by Question3). The source question is not resolved by the sufficient route's failure. No PROOF.md is warranted.

## Live registries and chronology limits

At fetch receipt20:02–20:04UTC, Omega HEAD was73a5033dd654a16a14fcd1b13277f1a03d81d826, authored/committed19:55:36UTC. Supplied c9cea079... to this head is2commits/1file, not API-capped. The changed actual CDSO incidence-moment/capacity-phase body concerns joint subset arrays and graph costs, not Fisher optimization. This merge time is NOT treated as intellectual priority. OpenAI HEAD remains7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a,26October21:18:03UTC.

Inherited full path inventories were screened and relevant actual current bodies downloaded: Omega GaussianQuadraticMixedDefect is joint Gaussian characteristic-function control; TraceClass/EntropyConcavity is quantum trace-class entropy under affine mixtures. OpenAI HardSphere/GaussianMixture is a pinned Brownian-bridge kernel construction; GaussianInformation/Kernel/Mixtures gives xlog perspective bounds, not iid Fisher optimizers. Other retrieved current mixture bodies concern inference kernels, posterior replicas and FreeIsing response mixtures. Blueprint bodies are not equated with Lean claims; both forms were read where returned.

Material HOLD: the18:13baseline-to-c9cea path/claim changes have not been exhaustively semantically audited in this lane. Short2commit latest delta and baseline name matches do not repair that gap. No global absence/priority or novelty PASS is asserted. User-specified ThetaTailRobinWitness/AURICv18/FIB§33 scope differences are retained as supplied context, not newly re-proven. Chatterjee remains EXCLUDED and MMPP PARKED; neither was retrieved. Matveeva and r102 untouched.

Final screen correction: the initial exact-id raw regex accidentally doubled a backslash. Author/Fisher matching already worked; the corrected supplemental full-corpus audit and filename audit now match literal arXiv ids. Initial scripts/results are preserved under initial-* and the failure is described in failures.md. The all-date corpus itself was not capped or replaced. This correction does not change target selection or zero-credit status.
