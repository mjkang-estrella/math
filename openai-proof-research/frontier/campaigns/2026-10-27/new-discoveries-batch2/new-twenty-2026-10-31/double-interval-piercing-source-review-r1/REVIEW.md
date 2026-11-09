# Review of MathDB 325944

Disposition: **HOLD for the intended source inequality; literal normalization correction/refutation only, credit 0. Campaign remains 52/60 beyond 39 prior. No acceptance or Pi dispatch.** This is an independent review of the displayed ordinary arguments and source passages, not a new proof or an independent verification of the parent's 20 raw bindings / 106 hashes.

## Exact statement and source fidelity

Frozen raw record hash is 33b4a91e5cfcf0322fc1e2c649d3e47bc4ac69cd021248bc5778eefda6671f0d. It expressly calls a(S) the approval RATIO, then asserts a(S)/n >= 1/3. In contrast, Klawe–Nyman–Scott–Su, arXiv:1307.5094v1 (18 July 2013), introduction lines89–96 in the frozen text, defines a(p) as the NUMBER of approving voters, a(S)=max_p a(p), and the approval ratio as a(S)/n. Its concluding conjecture is about this number divided once by n. These are different endpoints.

Literal failure is elementary: take four labeled voters, each approving [0,1] union [2,3]. The sets are nonempty, have two disjoint closed bounded nondegenerate components on one common real line, and are pairwise intersecting. Their approval ratio is 1. Dividing that ratio again by n gives 1/4 < 1/3. This is a transcription/normalization correction with zero campaign credit, not a substantive new refutation. If distinct approval sets were demanded (neither record nor read source demands this), one may instead use the four different sets [-i,1] union [2,3], i=1,2,3,4; all still share 0 and have ratio1. No silently repaired literal theorem is qualified for credit.

The intended source is a finite society with n voters, two disjoint closed approval intervals per voter, all on R. The vertical levels in Figure1 distinguish voters for display; they are not two fixed tracks. Pairwise intersection is of whole approval sets, and does not require either matched component pair to intersect. Source lines36–39,76–98 and concluding lines571–575 were actually read. The source works with finite positive n through counts and division by n; n=0 is outside a defined approval ratio. It does not explicitly add a separate nondegeneracy/boundedness/distinct-voter-set hypothesis in these passages. Do not manufacture one. Standard nonempty interval convention is needed; if empty approvals are admitted, singleton society with empty approval is an additional boundary failure, not mathematical credit. Singletons as closed intervals cause no problem for a genuine general theorem. The original-source result is not replaced by a separated-family statement.

## Independent assessment of r374

Theorem4.1 and its entire relevant endpoint proof (source lines322–423) were read. For 2n components, pairwise voter intersection gives n(n-1) <= sum(L+R+B+C). Counting containments gives sum B=sum C. A component endpoint is in at most a-1 other components, because its own voter's two components are disjoint. Summing left and right capacities gives 4n(a-1). The first a left endpoints save a(a-1)/2, as do the first a right endpoints counted from the right. Hence

    n(n-1) <= (4n-a)(a-1).

The source assumes distinct endpoints without loss. For finite bounded closed components this can be justified by replacing each tied endpoint block by distinct ordered endpoints with all left endpoints before all right endpoints. Preserve the order of unequal blocks. This preserves the component intersection graph, including touching and degenerate intervals. Interval Helly implies that maximum component depth equals its clique number, so depth is preserved; components of a voter remain disjoint. No statistical or computational validation is being substituted for the count. This only validates the known weaker source argument.

The bound permits n=19,a=6: 342 <=350, although 19>18. This manually checked pair is only feasible for the relaxed inequality, not an actual society or a counterexample. Thus the endpoint relaxation does not establish the conjecture. It is already source Theorem4.1; reproducing it has no novelty credit. The source Table1 itself displays the weaker bound at approval number6.

Let F be the finite indexed family of whole approval sets. Define nu(F) as the maximum size of a pairwise disjoint subfamily; define tau(F) as the minimum number of real points meeting every member. For nonempty pairwise intersecting F, nu(F)=1. This is an integral packing assertion; it is not a bound on fractional packing or on disjoint individual components.

For a bounded finite nonempty component family choose the smallest right endpoint p of component I, with sister component J belonging to its voter. Every component meeting I contains p: its right endpoint is >=p by minimality and its left endpoint <=p because it meets I. Therefore every set avoiding p is disjoint from I and, by whole-set pairwise intersection with I union J, must meet J. This part of r374 is valid. It does NOT say that the restrictions to J are intervals or remain pairwise intersecting.

The exact unpaid sufficient lemma is:

    For every such F and every earliest-right-endpoint choice p,
    tau({A in F : p not in A}) <= 2.

An empty residual requires zero extra points; otherwise arbitrary two-component restrictions to J must be addressed. Ordinary interval Helly cannot pay this lemma. It is stronger in its prescribed first point than the alternative sufficient conclusion tau(F)<=3; neither has been proved or authenticated here. They are sufficient routes, not assertions that the original density inequality logically requires a three-point transversal.

## Full conditional bridge, with dependency left explicit

If an authenticated theorem supplies an integral transversal P of size k<=3 for arbitrary finite nonempty two-interval families on one common line when nu=1, enumerate the voters with multiplicities. Then

    n = sum_v 1 <= sum_v sum_{p in P} 1[p in A_v]
      = sum_{p in P} depth(p) <= k*a <= 3*a.

Because n>0 and some approval is nonempty, k>=1. Thus a>=ceil(n/3); integrality automatically handles n not divisible by3. Duplicate voters are counted separately in this inequality even if a theorem first collapses equal sets; a hitting set for distinct sets still hits every labeled occurrence. Points repeated in a purported transversal can be removed. No pairwise intersection of components is used. A fractional transversal of total weight<=3 would also suffice via the same finite incidence sum, but that precise output must itself be authenticated; a fractional packing inequality alone is not this output, and no unproved LP or rounding bridge is presumed.

If the theorem requires bounded components, finitely many unbounded closed nonempty components can be clipped to a sufficiently large closed window: choose one witness from each component and from each intersecting voter pair, and contain all finitely many witnesses in the window. Component nonemptiness, disjointness and whole-family pairwise intersection survive. Any transversal of the clipped sets hits the originals, whose approval number is at least the clipped family's. Boundedness can thus be bridged without weakening the desired density bound. For finite compact intervals, closed touching intersections are retained; a theorem only for open intervals needs an additional incidence-preserving transformation, not a casual endpoint assertion. A theorem requiring two separated tracks has no supplied conversion: placing left and right components on different tracks can destroy cross intersections. Constants, weighted variants, and domain cannot be supplied from memory.

This is a complete conditional incidence/finite-domain bridge, NOT a complete proof: its integral or weighted piercing input remains unpaid. No classical theorem label or constant is asserted as established.

## Actual prior/source investigation and chronology

The original bibliography (read in full) contains Berg–Norine–Su–Thomas–Wollan2010, Hardin2010, Helly1923 and Scott's *Approval ratios of two-intersecting double-interval societies*, Harvey Mudd senior thesis2011. It does not itself cite a Tardos, Kaiser or Gyarfas–Lehel theorem. Scott's thesis is a specific unread potential dependency, not a cleared result. Bibliographic dates are not authenticated theorem applicability.

Current arxiv metadata GET on 2026-11-07 at03:00:16UTC reports a single v1 submission, 2013-07-18 22:13:46UTC; it supplies no successor theorem body. This is version chronology only, not evidence that no journal successor exists. The frozen paper header says Contemporary Mathematics with a placeholder copyright; no final journal theorem/correction body was authenticated. The cached source's open conjecture status does not establish present-day novelty.

The focused search budget was THREE batches and EIGHT distinct explicit public GET attempts (including the search GETs), below the12 cap. Google returned an interstitial/challenge script, Bing returned irrelevant dual-monitor results, DuckDuckGo returned a human challenge202. No challenge was answered. Tardos's public institutional home was read only for routing. Its linked HTTP publication index returned403 and was not retried by an HTTPS/alternate route. A guessed Kaiser homepage returned404. MathDB's exact current page returned403; current statement and proof status are therefore unread. No blocked AMS335255/ASU route was attempted. Full URLs, UTCs, successful status/finalURL/bytes/SHA256 and exact error strings are in access-inventory.json and contemporaneous receipts. For error responses, body bytes/hash/finalURL were not captured; those fields remain explicitly unavailable rather than fabricated.

No actual applicable current public proof-registry theorem body was acquired. Cached generic registry-directory observations in BRIEF are not relied on as clearance. No new investment/implementation follows this failed current check. Tardos/Kaiser/Gyarfas–Lehel general versus separated hypotheses, their exact bounds and proof dependencies, and Scott2011/successor bodies remain precise source HOLDs. There is no worldwide novelty conclusion, no exclusion merely from familiarity, and no claim that these theorems cannot apply. Their actual statement/proof is what is missing.

## Gates and objections

Literal fidelity: FAIL under ratio definition; correction0. Intended mathematics: HOLD for the exact residual/piercing dependency above. Final-source/successor: HOLD, unread body. Prior resolution: not established, not cleared. Novelty: not established, transcription and reproduced endpoint bound0. Significance: unqualified. Formal endpoint/axioms/replay: NOT RUN, no complete eligible ordinary endpoint. Pi: NO DISPATCH and no recommendation for campaign credit on the present record. Acceptance: root only, not authorized here. Credit0;52/60 unchanged.

Objection: pairwise intersection should permit Helly. Rebuttal: whole approval sets are not convex; restriction to J can have two components and need not preserve pairwise intersections. Objection: root's hash check independently validates the argument. Rebuttal: hashes validate bytes only. Objection: a classical named theorem settles it. Rebuttal: no exact statement/proof/domain was authenticated, so this review gives no such clearance. Objection: the source still calls it a conjecture, so a new proof would be novel. Rebuttal: source-era status is not current prior-art evidence. Objection: the literal counterexample qualifies. Rebuttal: it is precisely the excluded normalization correction.

## Integrity, access and resource accounting

Both mandated frozen checks returned count110, mismatches[], exit0. First bootstrap receipt is preserved. Only the review lane was written through its resolved write_lane.py, apart from the mandated bootstrap/verifier receipts. No git, installs, solvers, math enumeration, numerical program, CAS, Lean/formal API, Pi, children, paper, browser, private API, POST, account mutation, messaging or publication was performed.

There are material compliance limits, explicitly preserved. The initial target excerpt selector accidentally printed unrelated neighboring DERIVATIONS and BRIEF summaries; a later own-receipt inspection echoed some. Those are out-of-target semantic exposures, not authorized proof coverage, and no conclusion here uses them. The author BRIEF discloses older legacy-read deviations; this review does not cure them. This reviewer did not open those legacy files or protected lane bodies. Whole target-author JSON/Markdown containers were acquired in memory for entry/section selection. No recursive campaign scan occurred.

The mandated first two scripts report self-only caps, not descendant monitoring. The third infrastructure read has a contemporaneous terminal receipt but no durable guard receipt. Guard creation has actual writer RSS samples/true exit in its terminal output. Subsequent guard receipts save worker stdout/stderr, real exit, affinity and limits, observed descendant PIDs and sampled RSS; writer true exit and samples are printed after saving each receipt. Those writer events cannot be inside the receipt already written. Guard own exit is reported by the shell tool. Therefore universal every-reader/resource/access true-exit receipt compliance is NOT claimed. Short-lived processes may evade10ms samples. These are sampled process observations, not cgroup/group peak guarantees. No retrospective telemetry was invented. All launched subprocesses were waited/reaped. Error-response metadata gaps remain gaps.

read-inventory.json, access-inventory.json and resource-inventory.json distinguish semantic reading from byte acquisition, current reads from cached observations, and actual samples from missing telemetry. The actual lane hash manifest is produced and re-read verified after this report, excluding itself, its verification report and the final guard receipt to avoid self-reference. Those exclusions are explicit. The report is a HOLD handback, not acceptance evidence.
