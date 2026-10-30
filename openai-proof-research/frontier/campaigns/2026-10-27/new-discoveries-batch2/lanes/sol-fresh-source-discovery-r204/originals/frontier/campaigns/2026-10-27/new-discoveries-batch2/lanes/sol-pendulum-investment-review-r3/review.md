# Pendulum investment adjudication r3

UTC 2026-10-30; America/Los_Angeles 2026-10-29. **Decision: scoped INVEST.** Root should fund a finite formal-feasibility stage for the literal published Conjecture 1. This is a substantive investment recommendation, not acceptance, priority certification, permission to count, or a claim of worldwide novelty. No Lean or manuscript was produced. Counts remain 9 additional / 39 total, next 40; credit 0.

| Gate | Decision | Exact scope / remaining condition |
|---|---|---|
| Published source | PASS | da Costa–Grinfeld–Mottram–Pinto–Xayxanadasy, Afrika Matematika32(2021)645–672, DOI10.1007/s13370-020-00851-9, eq24/26 and Conjecture1 p660 |
| Ordinary mathematics | PASS | Complete complementary-moment proof plus independently supplied closed-endpoint DCT supplement, rechecked here; every fixed 0<phi<pi/2, z in[0,2] |
| Substantive threshold | INVEST | The complete exceptional-moment/cancellation construction is a specific missing bridge beyond the inspected published map theorems. Routine EXCLUDE is not supported by those theorems |
| Bounded priority | Scoped no-match; conditional | Changed title/DOI/Mottram/arXiv aliases screened in selected actual current registry bodies and known patches; refreshed indexed citer set still one relevant 2024 work. Two historical capped intervals remain separately assigned; fixed OpenAI full-tree request403 creates an additional explicitly unclosed coverage limit |

## What is being invested in

The [published body](https://link.springer.com/article/10.1007/s13370-020-00851-9) retains b(z)=acos(1-z)/2 and the sum of two inverse-square-root integrals in eq26, explicitly z in[0,2]. Its changed title and additional Mottram coauthorship do not change the mathematical object in arXiv1907.13009v1 eq14. Printed p660 still conjectures convexity for each fixed phi; Appendix47–50 still reports the unsuccessful approach. This journal body was published online28 October2020, after the identified2019 Lorvanhxay thesis, and received inJuly2020. It is stronger evidence about survival of the question than the2019 arXiv label alone. It is not evidence that no later proof exists.

Only this map is in scope. No I_k/B_k/D_k expectations, extra turns, full physical bifurcation diagram, or separate quantitative-curvature credit is proposed.

Fix a=1-cos(2phi) in(0,2). The substitution t=1-cos(2x) gives

    T(a,z) = 1/2 (integral_0^a + integral_0^z)
                  [t(2-t)(a+z-t)]^(-1/2) dt.

For interior z define M_n by replacing the integrand with t^(n-1/2)(a+z-t)^(-1/2). The positive binomial expansion gives

    T(a,z) = 1/(2sqrt2) sum_n binom(2n,n) M_n(a,z)/8^n.

MCT applies to both nonnegative integrals. Their finite values imply a finite pointwise limit. There is no derivative of this series. Complementary angles under t=(a+z)sin²theta give exactly

    M_0 = pi,
    M_1 = pi(a+z)/2 - 2sqrt(az),
    M_1'' = sqrt(a)/(2 z^(3/2)) > 0.

For n>=2, p=n-1/2>1. The fixed integral A_n=integral_0^a t^p(a+z-t)^(-1/2)dt is convex by pointwise convexity. The other piece is

    B_n = integral_0^infinity (z-y)_+^p(a+y)^(-1/2)dy.

The positive-part power is convex; integration preserves its Jensen inequality. For any three arguments in that inequality all supports lie in one bounded interval, and a>0 bounds the weight there. Thus integrability is adequate without an integrable weight on the entire half-line. Positive finite partial sums and their finite pointwise limit are convex. Removing the M_1 term before taking the limit leaves a convex remainder; its coefficient1/(8sqrt2) yields strict convexity. These steps prove the bridge, rather than invoking an unidentified incomplete-integral theorem.

The n=0 moving piece is **concave**, not convex:

    B_0 = 2 asin sqrt(z/(a+z)),
    B_0'' = -sqrt(a)(a+3z)/(2 z^(3/2)(a+z)^2) < 0.

At a=z=1 this is -1/2. A blanket convex-convolution proof is therefore false; complementarity of the two low moments is essential. The n=1 identity also resolves the exponent1/2 case that the positive-part-convexity argument cannot cover. Classical beta integrals individually explain these identities, but neither their existence nor the general convexity-preservation rule already states the paired-moment theorem for this stopping condition. Selecting the expansion and splitting off exactly the exceptional moments is the substantive construction being judged here.

The endpoint supplement is sound. At z down to0, the first original integral is dominated by (cos2x-cos2phi)^(-1/2), integrable by its simple zero at x=phi, and the moving integral is at most b(z)/sqrt(a), tending to0. At z up to2, for z>=2-a/2 the squared denominator is at least a/2 on[0,pi/2]. Extend the moving integral by its interval indicator and apply DCT on that fixed interval. Both literal endpoint values are finite and continuous limits. Passing Jensen inequalities through interior approximations gives convexity on[0,2]; the continuous convex remainder and strictly convex M_1 give strictness too. No endpoint derivative is asserted.

## Why the actual classical bodies do not justify routine EXCLUDE

Schaaf1990, DOI10.1007/BFb0098346, chapter1 definitions and Theorem1.4.2 with its complete proof were re-read in the cached actual publisher extraction. Its Dirichlet return maps start at u=0 with velocity p and stop on returning to u=0; the A-B-function test proves T_i''(p)>0. The trigonometric example makes this a serious comparison. But our orbit stops on a prescribed nonzero velocity condition, generating b(z); no equality with that return map has been established. Even an equality with a convex p-map would require an additional inequality after squaring: for H(z)=T(sqrt(z)), H''=(pT''-T')/(4p³). T''>0 does not supply its sign. The proof of1.4.2 supplies g''' positivity for the return-map representation, not the complementary moving cutoffs. Other Schaaf chapter results remain r2 evidence, not newly claimed whole-book coverage.

Smoller1994, chapter13 sectionD, DOI10.1007/978-1-4612-0873-0_13, actually fixes f(u)=-u(u-a)(u-1), 0<a<1/2, homogeneous Dirichlet boundaries. Theorem13.11 asserts exactly one critical point. Equations13.28–37 prove S''>0 **at stationary points** by adding kS'. That gives uniqueness, not global convexity in our squared initial ordinate. Journal Appendix47–50 has the same stationary-point limitation even before its unresolved sign is considered.

The actual2009 EJAM section3.3.3, DOI10.1017/S0956792509007827, and2017 section3.1.5 eq3.3, DOI10.1017/S0956792516000243, use fixed spatial endpoints and a complete elliptic-period term for q<1. In our variables q=(a+z)/2 crosses1 at z=2-a, whereas T_B remains finite. Substitution of b(z) into a fixed-endpoint convexity theorem needs boundary derivative terms and does not cross that period singularity. The exact fixed-endpoint formulas, not merely their titles, underlie this objection.

The refreshed primary-followup selection remains Grinfeld–Pritchard2024, DOI10.1093/imamat/hxae028. The cached actual AppendixA.1–A.4 fixes moving intervals by substitutions and proves width monotonicity, together with area and local bifurcation facts. It provides neither our second-derivative inequality nor the exceptional paired moments. Similar elementary substitutions in a different first-derivative theorem do not form a complete subsumption bridge.

Accordingly INVEST is justified by a complete construction solving the exact surviving published question beyond those maps, not by proof length, an open label, or inability to obtain all books. EXCLUDE would require an earlier body yielding this complementary sum (including n=0,1), or an equivalent mixed-stopping/squared-variable theorem, with its full-domain and endpoint adaptation supplied. None of the inspected bodies does so. This judgment does not assert that the construction is unprecedented worldwide.

## Bounded prior clearance and its precise limits

Fixed heads: Omega2b143c68ca72fcaccfe71d6233cb2c6db4c8c059; OpenAI4eaee87548250b2682affda7d05d947c05554bae. No HEAD chase. The r2Steiner complete Problems tree(1567 blobs) and Blueprint tree(22274 blobs) were reused and saved. The Problems subtree identity at the fixed root agrees with the inherited complete-tree identity; no historical interval enumeration was repeated. Topic selection adds the elliptic-tail family to the previously relevant incomplete-beta families. Three actual Problem bodies and twelve current Blueprint explanatory bodies were retrieved by immutable raw URLs. All fifteen were screened literally for the journal title, DOI, Mottram, Grinfeld, Xayxanadasy, arXiv identifier/title and mathematical topic aliases. The saved screen lists every URL, hash and match; matches were generic incomplete-beta/complementary language, not target identifiers or a matching theorem.

In particular, IncompleteBeta/Moment's complementary indices concern finite Gamma-coefficient convolutions and fixed-sum beta-shape imbalance. IncompleteBetaShape's sliding affine windows compare expectations under a different shape parameter. Neither supplies M_n(a,z) or its moving-cutoff convexity. EllipticTailExponent concerns the supremum2 of a normalized remainder parameter exponent, not this map. The beta moment/comparison/mixture/kernel/result explanations were compared as mathematical bodies; their formal correctness is accepted as instructed, not re-audited by Lean.

The known d36a58e..2b143 delta has11 actual patches, all screened for the expanded aliases, with no matches. The saved current OpenAI commit has281 paths;105 contain actual patches, screened without target hits;176 absent patches receive no content clearance. A requested complete fixed OpenAI recursive tree returned403 rate-limit exceeded, so that route stopped. The copied complete older preprints tree is explicitly only a baseline. It cannot establish current whole-repository absence. This additional access limitation is retained for root's coverage reconciliation; no substituted partial result is called complete.

The independent refreshed OpenAlex exact-DOI citer request on2026-10-30 again returned only the2024 rivulet work. The r2 publisher/citation/history evidence remains body-verified evidence, with exact inherited retrieval URLs and dates preserved. A single index is not a worldwide citation census. Korman DOI10.1142/8308 and Lorvanhxay2019 NUOL thesis remain unread. No blocked host was retried. Neither is an automatic investment blocker: no specific located theorem presently satisfies the mixed-stopping/squared-variable hypotheses, and the2020 successor explicitly cites the2019 thesis while retaining this conjecture. This chronology reduces the thesis-resolution concern without proving the thesis contains no relevant lemma. A future exact theorem that supplies the bridge is material; a broad unread title alone is not.

**Residual historical coverage condition:** root must reconcile the separately assigned aa026->a19a and a19a->490f capped-interval closure before claiming completed historical prior clearance. This review neither polls that worker nor adopts an unfinished closure result. The bounded finding here is no matching prior proof located in the enumerated bodies and patches, sufficient for finite feasibility investment under the stated residual conditions, not acceptance-level completed registry clearance.

## Root interface plan and stopping rule

Root can test feasibility with a small analytic interface before substantial formal investment: (1) literal eq26 definition with b and phi, and an exact change-of-variables equality to the t-integral; (2) finite/integrable M_n and the two exact complementary low moments; (3) positive-part change of variable and convexity for n>=2; (4) positive coefficient expansion via MCT, and convex finite pointwise limits; (5) a separately stated continuous-extension theorem to both literal endpoints. Keep a in(0,2), z in(0,2) for the moment lemmas and phi in(0,pi/2) at the source interface. The final interface must conclude ConvexOn[0,2] for the literal source integrals with no residual assumed identities or endpoint hypotheses. Strictness is optional and uncredited separately.

Highest feasibility risks are singular-integral substitution/MCT infrastructure and exact low-moment evaluations; they are formal-engineering risks, not a missing ordinary proof. Root should stop and reconsider if any becomes an assumed bridge, if a concrete classical theorem supplies the whole construction, or if the bounded registry reconciliation identifies an earlier matching proof. No new numerical run is necessary to decide these analytic steps; inherited checks are diagnostics only. I wrote no Lean and performed no manuscript work.

The strongest scientific/substantive falsifier is an earlier actual complementary-incomplete-integral theorem or mixed-stopping-map proof covering the two exceptional orders and q=1 crossing, with the parameter conversion written out. The strongest acceptance blocker currently is incomplete historical/current-registry coverage, not a discovered mathematical defect. Root alone decides whether and when acceptance gates are met.

## Integrity and process

Before scientific reading, all57 candidate and251 source-review originals passed exact byte-length/SHA256 verification and were copied byte-identically. Both complete reviews, candidate proof, closed-endpoint supplement and root source-adoption decision were read. Context ledger/prior/NEXT were consulted for counts and prior objections; this is not a fresh audit of every historic candidate. before-freeze.json, after-freeze.json, body-coverage.json, provenance.json and final-verified-manifest.json provide the receipts. Supplemental copied registry inputs have their own original/copy checks.

Every helper/retrieval/hash/check used the unchanged designated helper_guard.py with OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1, AS/groupRSS512MiB, CPU210s, wall230s, nominal40ms; limits were never raised. Receipts are in the tool transcript; sampled RSS is not a continuous peak guarantee. Native bounded reads/apply_patch were used. failures.json records the initial unguarded native inventory, truncated displays, one import failure corrected before retrieval, the403, and the corrected hyphenated-topic selector. One filename inventory inadvertently included the separate gap-closure lane; no worker status/results or patch contents were read or adopted, and it was not polled. No git/shared/count edits, children, external messages/posts/uploads, browser, Lean or manuscript actions occurred. All writes stayed in this assigned lane.
