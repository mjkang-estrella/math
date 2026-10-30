# Independent preliminary review: pendulum complementary time map

UTC 2026-10-30; America/Los_Angeles 2026-10-29. Candidate: sol-fresh-source-discovery-r166. Disposition: **ordinary mathematics PASS with the explicit closed-endpoint supplement below; source scope PASS for arXiv v1; publication history and substantive novelty HOLD. Recommend HOLD on Lean/manuscript investment, and only bounded source-history/subsumption research next.** No acceptance credit; root decides. Counts remain 9 additional / 39 total, next 40.

## Scope and integrity

All 57 originals in root-r166-preliminary-freeze-r1/review-freeze.json were SHA-256/length verified before candidate inspection or copying. Work uses byte-identical frozen-copy files in this review lane. before-hashes.json and after-hashes.json give each original and copy's exact hash and length; finalmanifest.json covers the review payload. The freeze itself is separately hashed. No candidate proof, shared file, ledger, count, git state, Lean file or manuscript was changed. No children, browser tabs, external messages, uploads or posts were used.

The actual primary body is da Costa–Grinfeld–Pinto–Xayxanadasy, *Bifurcating solutions in a non-homogeneous boundary value problem for a nonlinear pendulum equation*, [arXiv:1907.13009v1](https://arxiv.org/html/1907.13009v1), equations (12), (14), section 4.4 Conjecture 1. Equation (14) explicitly gives z in [0,2] and 0<phi<pi/2. Here z=y(-L)^2, not the unsquared initial ordinate. The formal numbered conjecture says convexity of this z-map for each such phi. Its preceding discussion sometimes uses the unsquared ordinate in prose; that does not change the numbered z statement. No restriction to z<1+cos(2phi), to stationary points, or to a neighborhood of z=0 is permitted.

Source section 5 adds unproved expectations for I_k, B_k and D_k. Equations (31), (34)–(38) involve additional period terms or different maps/domains. These are additional claims, not an enlargement of the literal numbered Conjecture 1. They are not certified here. In particular, the homoclinic divergence of a period term cannot be silently inserted into the finite T_B endpoint analysis.

## Independent proof audit

Fix a=1-cos(2phi) in (0,2), b(z)=acos(1-z)/2. From the original two integrals,

    T(a,z) = (1/2)(integral_0^a + integral_0^z)
                    [t(2-t)(a+z-t)]^(-1/2) dt.

Indeed t=1-cos(2x)=2 sin^2(x) has dx=dt/(2 sqrt(t(2-t))); its endpoints are exactly a and z. On the first interval a+z-t>=z and on the second >=a. Both intervals lie below 2 for interior z. Thus the integrals are finite and positive; the t=0 singularity is integrable.

Define M_n=(integral_0^a+integral_0^z)t^(n-1/2)(a+z-t)^(-1/2)dt. The binomial expansion of (2-t)^(-1/2) has coefficient 2^(-1/2) binom(2n,n)/8^n, all positive. MCT separately on the two nonnegative integrals gives the finite equality

    T(a,z)=1/(2 sqrt(2)) sum_(n>=0) binom(2n,n)/8^n M_n(a,z).

No differentiated series is involved. MCT is sufficient even as the ratio approaches 1; uniform convergence in the entire parameter rectangle is unnecessary.

Put s=a+z and t=s sin^2(theta). Then M_n=2s^n times the sum of integrals of sin^(2n)(theta) up to theta_a=asin sqrt(a/s) and theta_z=asin sqrt(z/s). Since theta_a+theta_z=pi/2,

    M_0=pi,
    M_1=pi(a+z)/2-2 sqrt(az),
    M_1''=sqrt(a)/(2 z^(3/2))>0.

For n>=2 put p=n-1/2>1. The fixed endpoint part A_n=integral_0^a t^p(a+z-t)^(-1/2)dt is convex by pointwise convexity and integration. In the other part substitute y=z-t:

    B_n=integral_0^infinity (z-y)_+^p(a+y)^(-1/2)dy.

For each y the integrand is convex in z because u->u_+^p is convex for p>=1. For any two z and their interpolant, all three integrands vanish beyond their finite maximum. Their integrals are finite, so integrating the pointwise convexity inequality is legitimate despite the infinite written interval. This proves M_n convex for every n>=2. It requires neither differentiating at the moving boundary nor claiming a globally integrable weight on [0,infinity).

Positive partial sums are convex. Passing the convexity inequality to their finite pointwise limit proves convexity of T. To obtain strictness correctly, remove the M_1 term first: the remaining nonnegative series is again a finite convex pointwise limit. The coefficient of M_1 is binom(2,1)/(8*2 sqrt(2))=1/(8 sqrt(2))>0. Its strict Jensen inequality plus the remainder's weak inequality proves strict convexity for every interior pair. There is no unjustified claim that a strict inequality survives a limit by itself.

For C^2 regularity, the first original integral has locally positive denominator uniformly on [0,phi]. For the moving integral write x=b(z)u on u in [0,1]. On every compact z-subinterval of (0,2), b and its first two derivatives are bounded and smooth, and a+z-2sin^2(b(z)u)>=a. Its first two differentiated integrands are bounded on the compact product. Ordinary differentiation under a fixed integral is therefore valid. The C^2 convex remainder T-M_1/(8 sqrt(2)) has nonnegative second derivative. Consequently

    T_zz >= sqrt(a)/(16 sqrt(2) z^(3/2)) > 0.

All constants in the candidate check. This strengthens the source statement but earns no separate credit.

## Closed endpoints: verified supplement, not a frozen-proof edit

At z=0, the first original integrand is bounded by (cos(2x)-cos(2phi))^(-1/2). This is integrable: near x=phi, cos(2x)-cos(2phi) is asymptotic to 2sin(2phi)(phi-x), with positive coefficient for every fixed allowed phi. The second integral is at most b(z)/sqrt(a), which tends to zero. DCT gives the literal endpoint value T(a,0).

At z approaching 2, choose z>=2-a/2. On the first interval and on the whole fixed interval [0,pi/2], the squared denominator a+z-2sin^2(x) is at least a/2. Extend the second integrand by the indicator of [0,b(z)] on this fixed interval. It is dominated by sqrt(2/a) and converges almost everywhere to the integrand with z=2 and b(2)=pi/2. The first integral has the same bound. DCT proves the finite literal endpoint value T(a,2). This verifies root's proposed bridge, including the moving interval qualification.

For any endpoints x,y in [0,2], approximate by interior points and pass the weak convexity inequality to the continuous limits. This proves convexity on [0,2]. In fact the remainder above extends continuously too, hence is convex on [0,2]; M_1 remains strictly convex there, so strict convexity also extends. No endpoint derivative is claimed. The candidate PROOF.md only spells out the interior result; it should not be described as already containing this endpoint proof. This review supplies it separately without altering the freeze.

## Adversarial findings and strongest falsifier

The strongest concrete falsifier of the tempting routine shortcut is the n=0 moving piece B_0(z)=2asin sqrt(z/(a+z)). Its derivative is sqrt(a)/(sqrt(z)(a+z)), and its second derivative is strictly negative; at a=z=1 it equals -1/2. Thus the two pieces are not separately convex for all orders. The fixed n=0 piece is convex, and cancellation gives a constant only after complementarity is used. A blanket application of convex convolution to every moment is false. The candidate avoids it using the exact M_0 and M_1 identities.

The source's equation (21) also cannot be reduced by discarding its last term: g=z^2-2(1-a)z-2a is negative at a=z=1. Source Lemma 3 is local, not global. Equations (26)–(30) and the actual text explicitly report failure to prove global Phi positivity. Positivity only at stationary points would yield the single-minimum conclusion, not general convexity. Neither the failed Smoller route nor its numerical graph supplies this candidate's theorem. No counterexample to the candidate's literal theorem emerged; the analytically proved inequality, rather than samples, is the reason for mathematics PASS.

## Primary history and bounded classical comparison

The live arXiv abstract retrieved on 2026-10-30 lists only v1, submitted 2019-07-30 15:20:35 UTC. The stored primary body says v1 and still contains Conjecture 1. This establishes the latest **observed arXiv** version. Neither it nor unrelated Crossref results establish that there is no published revision or subsequent solution. The candidate's Crossref mismatch remains a failure; three additional bounded bibliographic queries also did not identify an exact published version. Published-version status remains unresolved.

Two actual publisher bodies were obtained, extracted and read in their relevant sections, rather than inferred from titles:

* da Costa–Gartland–Grinfeld–Pinto (2009), [EJAM 20, 269–287](https://doi.org/10.1017/S0956792509007827), section 3.3.3, pp.280–281. Here S_A=4kT+2T_1. In q=sin^2(alpha), T=K(q)/sqrt(2), T_1=(1/sqrt(2))integral_0^phi_p(q-sin^2 x)^(-1/2)dx. The displayed second derivative is a sum of positive fixed-interval integrals. Domain q in (sin^2(phi_p),1), and its boundary conditions are Dirichlet. This is a genuine earlier pendulum convexity proof, not just a monotonicity badge.
* da Costa–Mendez–Pinto (2017), [EJAM 28, 243–260](https://doi.org/10.1017/S0956792516000243), section 3.1.5, equation (3.3), p.252. The C_l time map is sqrt(2) integral_0^(pi/2)(1-q sin^2 theta)^(-1/2)dtheta plus (1/sqrt(2))integral_phi0^phi1(q-sin^2 x)^(-1/2)dx. Its second derivative is explicitly positive for q in (sin^2(phi1),1). Section 3.1.6 reuses this for higher turns. These formulas and complete relevant pages were checked visually after extraction.

On bounded source orbits q=(a+z)/2 is affine in z. That does not identify either old map with T_B: their spatial endpoints phi_p or phi0,phi1 are fixed; T_B's second endpoint b(z) varies with z. Substituting a moving endpoint into a convexity theorem for fixed endpoints introduces additional derivative terms of uncontrolled sign. Moreover the old elliptic-period representation ends at q=1 (z=2-a); T_B stays finite across this homoclinic value and exists until z=2. Therefore these actual bodies do not supply a complete literal full-domain subsumption bridge. This is a concrete obstruction to the proposed application, not a claim that no other classical adaptation exists.

The source also cites Korman (2012), Schaaf (1990), and Smoller (1994). A bounded attempt to inspect Korman's institutional site returned HTTP200 with an actual scheduled-maintenance body, not a book or theorem; no theorem clearance follows. Full book bodies were not obtained. The positive binomial expansion and integration of convex functions are classical; the complete exceptional-moment bridge must still be located in an earlier body, or independently judged substantive. Shortness alone is insufficient to exclude, and failure to find such a body is insufficient to certify novelty. Recommendation is HOLD, not automatic EXCLUDE or INVEST.

## Public registries and exact coverage

Candidate snapshots observe Omega d36a58e865e46580f127ef7a09d64ccbc2370296 and OpenAI 4eaee87548250b2682affda7d05d947c05554bae. This review independently read the retained IncompleteBeta Result/Moment and IncompleteBetaShape Result explanatory bodies and both Result Lean source texts without running Lean. They compare finite gamma-coefficient convolutions at fixed sums of beta shape parameters and prove Turanian coefficient signs. They neither state this moving-cutoff time-map convexity nor provide the exceptional M_0/M_1 bridge. No full dependency/build audit is claimed.

The live review observes Omega **2b143c68ca72fcaccfe71d6233cb2c6db4c8c059**, OpenAI unchanged. The saved GitHub comparison d36a58e...2b143c68 has 22 commits and 11 returned file paths, below the 300-file cap. Those paths concern Fibonacci incidence, resistance, words and other unrelated theories; no target path hit. This is exact path coverage of this delta, not semantic clearance of every new body. The inherited aa026->a19a and a19a->490f 300-path gaps remain untouched. No global registry novelty PASS is claimed. Candidate history-receipt.json is preserved, but its 1681-path history investigation was not independently rerun here; unrelated coupling and Orthomin candidates were not reviewed mathematically.

Integrity coverage is all 57 frozen files. Substantive coverage is the complete candidate PROOF.md, discovery.md, SUMMARY.md, numerical-check implementation, source equations (5)–(6), (12)–(14), (21)–(30), Conjecture 1 and later branch discussion, the five named beta proof bodies, root DECISION.md/replay-receipt, current registry heads/delta, and the two classical sections identified above. Remaining frozen files are preserved evidence, not silently represented as independently audited primary theorems. Campaign ledger/context/NEXT and ancestor rules were consulted; no old or related outcome is awarded another count.

## Independent runnable checks, failures and resource qualifications

independent_checks.py is written independently and runs via run-independent-checks.sh. It passes six curvature comparisons (direct source equation versus differentiation of a fixed-u integral), six 16-term positive-series/tail diagnostics, twelve M_0/M_1 identities, eighteen n=2,3,7 convolution identities, nine Jensen tests involving closed endpoints, and the negative B_0 curvature control. Endpoint a values include .001 and 1.999; interior parameters include .0001/.0002 and 1.999/1.999. The tail bound uses binom(2n,n)<=4^n and M_n<=pi max(a,z)^n. Numerical assertions allow absolute roundoff; the first displayed series gap exceeds its tiny mathematical tail because it is below working precision. This is explicitly not a validated tail interval. Root's separate 63-curvature/24-convolution replay remains supporting diagnostics, not an interval or universal proof.

All Python/retrieval/extraction/rendering/hashing/check processes used the unchanged designated helper_guard.py, with OPENBLAS_NUM_THREADS=1, OMP_NUM_THREADS=1, PYTHONDONTWRITEBYTECODE=1. AS and sampled group RSS512MiB, CPU210s, wall230s, nominal40ms were never raised. Main independent checks: guard exit0, sampled peak20,492,288 bytes, wall1.483s. Sampling is not a continuous peak guarantee. Native bounded text reads and apply_patch were used.

Review process defect retained: the initial native pwd/rg --files inventory was broader than necessary and not guard-wrapped; its displayed output was truncated (896 lines, original 33,644 tokens). It did not mutate inputs and was not treated as source or coverage evidence. One guarded extraction attempt failed with ModuleNotFoundError: No module named 'bs4', guard exit1, sampled peak10,059,776 bytes; the replacement used the standard library, without installing packages or raising caps. Exact failure qualifications are recorded in failures.json. The candidate's earlier export.arxiv.org429, ignored MathDB query parameters, unguarded inventory and ordering defect remain preserved in frozen-copy/discovery.md/http.jsonl. The already blocked export API was not retried; no TLS disabling, challenge bypass or browser was used.

The strongest outstanding acceptance falsifier is an earlier actual theorem/proof that, with all parameter and endpoint adaptations written out, supplies these complementary moments and the full z in [0,2] conclusion. No such bridge was established in the bounded bodies inspected. Root should resolve that question and publication history before authorizing formal or manuscript work. No acceptance is recommended at this preliminary stage.

Final packaging qualification: an initial guarded finalization failed its supplementary-copy assertion because two AGENTS.md inputs shared a local basename. No original or frozen candidate mismatch occurred. The campaign rules copy was restored under a unique name after checking its original hash; this failure and correction are retained in failures.json.
