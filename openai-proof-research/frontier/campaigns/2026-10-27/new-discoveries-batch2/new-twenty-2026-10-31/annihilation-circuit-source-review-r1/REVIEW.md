# Independent review: MathDB 354377

Review date: 7 November 2026. Independent ordinary mathematical/source review only. Credit 0; campaign remains 52/60. No children, mathematical computation, formal execution, Pi dispatch, acceptance, or publication.

## Verdict and separate gates

The proposed eight-point set is a correct ordinary counterexample to the supplied literal record and to arXiv:2204.11084v1 Conjecture 6.2. There is no mathematical repair needed. This is not an acceptance recommendation. Publication-version fidelity remains HOLD for the specific unavailable final journal body (DOI 10.1142/S0218216522500110). The bounded search found no exact earlier public refutation; that does not prove literature novelty. Significance needs root adjudication with the complete adaptation below, including a stronger comparison to Theorem 1.7 than the author's direct-normalization comparison. I do not recommend exclusion merely because the proof is short or uses familiar linear algebra. No dormant Pi implementation brief is issued while source/significance qualification remains unsettled.

| ID | Gate | Finding |
|---|---|---|
|354377|Ordinary correctness|PASS, full proof below|
|354377|Literal fidelity|PASS, exact record/raw agreement and all hypotheses paid|
|354377|arXiv source fidelity|PASS for v1, including visible formula and definitions|
|354377|Source/journal version|HOLD: final journal proof/conclusion/figures unavailable; no denial retry|
|354377|Prior/subsumption|BOUNDED REVIEW COMPLETE for specified 2014/2022 bodies; no printed identical refutation identified; general adaptation fully exposed below|
|354377|Novelty|NOT ESTABLISHED worldwide; no concrete matching public resolution surfaced|
|354377|Significance|ROOT DECISION: explicit close source adaptation, with strongest objections below|
|354377|Formal certificate|NOT RUN, no claim|
|354377|Independent review|Ordinary/source adversarial review delivered, with stated limits|
|354377|Acceptance|NOT ACCEPTED, root only, credit zero|

## Original quantifiers and obligation audit

The primary 2022 paper defines Basic using every real-valued function on the finite set and separate functions R -> R. Finite sets permit omission of continuity (pp1-2). A layer is x_i=j, i in [3], j in [n]. Minimality means EVERY proper subset is basic, not just deletion of one point, not only subsets meeting every layer. The integer annihilation definition is on p3; irreducibility is setwise coprimality on p3 and p11, hence gcd 1 and uniqueness only up to sign. Neither the original statement nor the literal record imposes two points per layer, graph connectedness, a special construction family, or a coefficient greater than one. Conjecture 6.2 is visibly exactly sum |f(X)|=2(|M|-n), p14. The preceding two-or-zero theorem has its own restricted hypothesis and cannot be imported as an extra conjecture hypothesis.

The supplied literal JSON and raw JSONL have the same ID, UUID, statement and source. Their open status/empty solutions are not novelty evidence. The n=3 witness uses the literal 1-based alphabet, not a finite-field model.

Write A=222, B=211, C=121, D=112, E=333, F=311, G=131, H=113, where digits denote ordered coordinates. They are eight distinct members of [3]^3. Set v=(1,-1,-1,-1,-1,1,1,1) in this order.

All nine layer obligations, including nonemptiness, are:

|layer|points|sum|
|---|---|---|
|x=1|C,D,G,H|-1-1+1+1=0|
|x=2|A,B|1-1=0|
|x=3|E,F|-1+1=0|
|y=1|B,D,F,H|-1-1+1+1=0|
|y=2|A,C|1-1=0|
|y=3|E,G|-1+1=0|
|z=1|B,C,F,G|-1-1+1+1=0|
|z=2|A,D|1-1=0|
|z=3|E,H|-1+1=0|

For arbitrary REAL annihilation weights, put a=w(A), e=w(E). Six two-point layers force w(B)=w(C)=w(D)=-a and w(F)=w(G)=w(H)=-e. The x=1 equation gives -2a-2e=0, hence e=-a over R. The two other remaining equations are then satisfied. Conversely the displayed weights and every real scalar multiple satisfy every layer equation. Thus the real annihilator space is EXACTLY Rv, full support for every nonzero member. This argument does not apply in characteristic 2, which is irrelevant here; it uses real arithmetic, not modular rank.

For any finite K subset M define T_K:R^9 -> R^K by (u_i,j) -> (P -> u_1,Px+u_2,Py+u_3,Pz). A functional on R^K is pairing with arbitrary real weights w(P). It kills im T_K iff every layer sum of w vanishes: this follows by testing each of the nine unit layer weights separately. T_K is onto iff there is no nonzero such functional. To prove the nontrivial direction without an unproved rank computation, a proper image has a basis that can be extended to a basis of R^K; assign zero to its basis and one to an added basis element. This constructs a nonzero annihilating functional.

T_M is not onto: v is nonzero, kills its image, and pairs to 1 with the indicator of A. Consequently that real indicator function has no coordinate decomposition and M is non-basic. For EVERY proper K subset M, extend any real annihilation weights on K by zero on M\K. The extension annihilates all layers of M. It is av and has a zero at any chosen missing point, so a=0. Thus T_K is onto and EVERY real function on K decomposes into three coordinate functions on [3]. Extend these to R by zero away from {1,2,3}. This supplies the ambient functions in the original definition. If K is empty the unique function has the zero decomposition; equivalently its codomain vector space has no nonzero functional. All proper subsets are covered, including those missing layers. No enumeration of subsets is needed or was run.

For integer annihilators the preceding classification still holds, and a=w(A) must be an integer. The gcd of the eight absolute values is |a|. The irreducible nonzero integer functions are precisely v and -v; the zero vector is not primitive. Either sign has norm 8. There are eight points and n=3, so 2(|M|-n)=2(8-3)=10. Thus the literal universal statement fails, regardless of any harmless choice of sign in 'the' irreducible function. No obligation has been deferred to a source axiom or a mathematical program.

## Primary figures and constructions

Read 2204.11084v1 text pp1-16, including definitions, Lemmas 1.5/1.6 and their proofs, Remark 2.3, Theorems 1.1/1.2/1.3/1.7/1.8, relevant graph bridge and construction proofs, and conclusion. Source pages 7-14 rendered at 1500 pixels and visually inspected using the PDF skill. Figures are source renderings, not an authored paper.

For coordinate transcriptions below take the front-left-bottom grid vertex to be 111 and the directions right/back/up to be x/y/z. Uncolored grid circles are not members of the depicted set. Coordinate reversals/permutations do not affect the comparisons. Color convention on p13: red -1, blue +1, green -2, black +2 (black in earlier unweighted illustrations merely marks membership).

Figure 2, p7, is the three-axis basic star on four levels: {(k,1,1),(1,k,1),(1,1,k):1<=k<=4}, ten points; not this candidate. Figure 3, p8, is the 2n-cycle of Remark 3.3 with n=4, eight points 111,211,222,322,333,433,444,144. Each layer forces alternating coefficients; its primitive norm is 8 and RHS is 8, so its having eight points does not make it a refutation. The analogous n=3 cycle has six points and norm/RHS 6. Pages 9-10 have no additional point figure. Figure 4, p11, is {211,121,112,222}, the basic K4 example. Figure 5 adds 111 with coefficient 2, giving Example 5.1; see below. Figure 6, p12, is an abstract three-cycle incidence diagram for the explicit coordinate construction; its groups of points are specified by the printed formula, not a [3]^3 point plot.

Figure 7 (p13), left to right, transcribes as follows:

* Six points: blue {133,212,321}; red {123,232,311}. Norm 6 =2(6-3).
* Seven points: black {133}; blue {222,311}; red {123,233,332,111}. Norm 8 =2(7-3).
* Eight points: black {133}; green {311}; blue {312,321,211}; red {123,233,132}. Norm 10 =2(8-3).

In particular the printed eight-point n=3 illustration is NOT the proposed all-unit-weight witness. Sign multiplicities already distinguish primitive vectors, and the above transcription checks every layer sum. This is a concrete figure comparison, not an inference from resemblance.

For completeness Figure 8 (p14) consists of:

* Left: blue {144,211,322,433}; red {444,111,222,333}. Eight points on four levels, norm 8.
* Right: black {144}; blue {423,212,331}; red {134,244,143,322,411}. Nine points, norm 10.

Figure 9 consists of:

* Left: black {144,411}; blue {233,322}; red {214,424,443,112,131,341}. Ten points, norm 12.
* Right: black {144,411}; green {234}; blue {233,222,332}; red {112,121,341,413,442}. Eleven points, norm 14.

These transcriptions have balanced layer weights and reproduce the norms 2(|M|-4); they provide explicit comparisons rather than a blanket claim that every pictured set was proved minimal again here. Four used levels distinguish them from the candidate. No matching correction is printed in the copied v1 text. This does not clear the unavailable final journal figures.

Theorem 1.7 uses globally distinct a_k,b_k,c_k,d,e, with 6m+2 points and weights 1,-1,-m,m. Each axis uses 2m+2 levels (the groups appearing differ by axis); independent BIJECTIVE normalization gives n=2m+2 and primitive norm 6m+2m=8m=2((6m+2)-(2m+2)). Thus the author's direct-normalization comparison is correct. Its original global alphabet of size 3m+2 has empty layers in each axis, so cannot directly be used for this conjecture.

But there is a stronger comparison: for m=1 map d to 2, e to 3, and each of a_1,b_1,c_1 to 1. This noninjective identification produces exactly B,C,D,F,G,H,A,E, with weights (1,1,1,-1,-1,-1,-1,1), the NEGATIVE of the candidate vector. No two of these eight points collide. Summing old zero layers preserves annihilation on the merged layers, and every level 1,2,3 occurs on every axis. However a noninjective layer identification can enlarge the annihilator space, so neither minimality nor primitive uniqueness follows just by citing Theorem 1.7. Here the independently supplied six pair equations plus -2a-2e=0 prove both, as above. Norm 8 and RHS 10 then finish the full adaptation. This supplies every bridge; it is stronger than saying only that the source construction satisfies equality before merging.

## 2014 companion and complete common-center adaptation

Read the entire seven-page Russian text of 1412.8078v1, including definitions, Lemma 1, Propositions 1-7, Examples 1-3 and the construction proofs. Example 1 is the 0-based version of 2022 Example 5.1. Example 2 explicitly lists {300,210,120,030,001,111,221,331}, projection sizes (4,4,2). Coordinate permutations and independent bijective coordinate relabelings cannot turn that into (3,3,3). This rules out ONLY direct isomorphism. It does not exclude transformations that identify, split or add levels. Example 3 is the basic four-point K4 set, not a counterexample.

Proposition 4 starts with a closed planar array and transfers disjoint balanced-color groups perpendicular to its plane. Its proof obtains non-basicness from Lemma 1 and supplies minimality in the stated two-point layer situation. Every planar projection of this candidate identifies some pair (for example B,F project to the same yz point); the resulting extra identification is not covered merely by calling it a simple projected closed array. Proposition 5 replaces B in a non-basic set by translated A',B', retaining A, for A,B sharing two coordinates. The printed conclusion is non-basicness, not preserved minimality or the conjectured norm discrepancy. The candidate DOES contain pairs sharing two coordinates: B,F; C,G; D,H. In fact Propositions 4 and 5 give a more direct complete construction, as follows. Begin in the plane x=1 with the closed array 122(+),121(-),131(+),133(-),113(+),112(-), returning to 122. Consecutive yz coordinates alternate equality and the six points are distinct. Partition it into the balanced pair {122(+),133(-)} and the balanced four-point complement. Proposition 4 permits translating just the pair by (2,0,0), giving T={322(+),121(-),131(+),333(-),113(+),112(-)}. Thus T is non-basic by the PRINTED construction and proof. Adjoin A=222 to form the non-basic seven-point M0=T union {222}. In M0 choose the pair A=222 and B0=322 sharing y=z=2. Apply Proposition 5 with perpendicular translation vector (0,-1,-1). It deletes B0, retains A, and adds A'=211 and B'=311. The output is EXACTLY the proposed eight-point M. There are no coincidences among its eight points, so every set-operation hypothesis is paid. Non-basicness follows from the printed 2014 propositions, but the input M0 is not minimal, and Proposition 5 makes no minimality assertion. For a full-target bridge attach the nine-layer table, real annihilator classification/zero-extension minimality proof, primitive normalization and 8 versus 10 calculation above. They apply to exactly this output; no further existential choice or unproved transformation is required. This is a complete earlier-construction-to-full-target adaptation and a stronger objection to significance than mere mismatched projection sizes. The printed proof assigns a formerly nondecomposable function to the new set; it supplies no all-layer or primitive norm statement.

Here is a COMPLETE ordinary bridge from Example 5.1 (already present as 2014 Example 1) to this target. Let O=111, and let S_t={O,(t,1,1),(1,t,1),(1,1,t),(t,t,t)} for t=2,3. Their integer relations are r_t=2[O]-[(t,1,1)]-[(1,t,1)]-[(1,1,t)]+[(t,t,t)]. For each t, its three t-layers force the three arm weights to be minus the diagonal weight a; a 1-layer then forces the center weight to be 2a. This also verifies minimality/full support and primitive normalization of the five-point ingredient without relying on a picture. Take r_2-r_3; the common center cancels, every other point is distinct, and the result is exactly v supported on M. This alone proves a nonzero annihilator, NOT minimality. The layer table and real-kernel proof above finish minimality for every proper subset, all-layer coverage, integer primitive classification and norm 8 versus 10. All required content is now supplied. Without canceling O, the union has the non-basic proper subsets S_2 and S_3 and is not minimal.

This is a full earlier-example-to-target adaptation, not a claim that the earlier paper printed the final counterexample. Generic circuit elimination only guarantees some circuit in the canceled support, not that all eight points survive as a minimal circuit; the equations are essential. Theorem 1.8 says integer annihilators decompose into rectangles and omits its routine proof; it does not assert support minimality or this discrepancy. No unprinted general matroid theorem was treated as a prior resolution.

## Significance, objections and chronology

Strongest argument for substantive exclusion: the entire full-target construction can be obtained by one subtraction of two explicitly printed five-point relations from 2014/2022, followed by the already printed full-support/uniqueness criterion (2022 Remark 2.3) and the elementary equations above. Alternatively, the exact six-cycle -> Proposition 4 -> adjoin one point -> Proposition 5 route above already uses the 2014 construction bodies and yields the entire witness, with every remaining bridge explicitly paid; or merge levels of the m=1 Theorem 1.7 construction as specified. No new machinery is needed. Root can judge whether these fully specified bridges make this a routine adaptation under campaign policy. If choosing exclusion, root should cite THIS full bridge, not point count, proof ease, standard tools, or the (4,4,2) mismatch alone.

Strongest objection to that exclusion: neither cited primary proves that the canceled support is minimal, and merging layers is not a minimality-preserving theorem. The main source still conjectures equality immediately after presenting these ingredients. The new step is selecting the gluing/identification that retains a single full-support annihilator while reducing the used level count; the explicit proof settles a stated universal claim rather than merely providing another instance of a known true theorem. A short correct counterexample can be mathematically substantive. The record being open does not establish significance, but the existence of elementary ingredients does not by itself negate it. I therefore give root the full adaptation and both objections, with no automatic significance PASS or smallness-based REJECT.

The companion's arXiv v1 is dated 27 December 2014. Main arXiv v1 submission is 23 April 2022, manuscript title page says 26 April 2022. The institutional author page acquired during this review lists the 2022 JKTR article and links only to the publisher and arXiv; no independent journal PDF is linked for it. Search preview dates are metadata only and not a replacement for the final body. Do not retry DOI/publisher, cached publisher previews, mirrors or alternate endpoints. A genuinely independent author/institutional final file, if later concretely identified, may settle the precise version HOLD lawfully.

Current registry sequential observations from the copied r392 dossier were minutes old at launch: OpenAI math 4eaee87548250b2682affda7d05d947c05554bae; LeanPool 364b613903fd76bc2b385eda32507a2650e84dcd; TauCeti 48a7d16da15db9f296480c476723877bd2972b1e; formal-conjectures 2055e5adadae0b2e392365938faa82ef6f1464f0. These are root observations, not matching proof bodies or atomic ancestry evidence. Pinned-routing file describes narrow catalogue routing only; no identified matching OpenAI theorem was relied on. No blind registry refresh or protected-lane search was performed. Registry root absence is not a mathematical or novelty verdict.

## Search, access and verification limits

Three actual native search calls / nine strings were precharged exclusively to 354377, with immutable exact plans saved before each and summaries after; author plans were read first to avoid blind repeats. Native search is an explicit external-tool exception to the local runner: its CPU, network status and complete ranking telemetry are unavailable, and no local resource receipt is fabricated for it. Search summaries route sources; mathematical conclusions rely on actual copied primary bodies. Motzkin/finite-field titles were screened as potentially related names, not assumed to be applicable unread theorems. The digital-plane source concerns two-dimensional arrays; any actual acquisition result is preserved in access records. A generic unknown worldwide theorem is not an invented HOLD. The concrete version HOLD is the unavailable final journal body.

Every local read, source render, acquisition and write after the mandated bootstrap/verifier has used run.py and its resolved write_lane.py, with contemporaneous true child exits. First two shell commands were exactly mandated. Two early run.py invocations with CLI code/--help instead of stdin executed empty code, exit 0, and their empty receipts remain; no sources were read by them. The incidental pwd command read no source and wrote nothing. A combined image-display output exceeded the host transport limit (JSON cut at 524288 bytes): the runner itself completed exit 0; six separately receipted page reads then allowed complete visual inspection. This is a display/transport failure, not a hidden mathematical or acquisition failure.

All ordinary reasoning above is manual; scripts only manage files, receipts, source conversion, hashes and bounded public GETs. No rank/subset enumeration, mathematical software, Lean, compiler, CAS, formal API, browser, git, installs, shared/parent/author writes, dependency writes or child delegates. Requests and converters are synchronous children of the capped runner and must be reaped before handback. No denial retry is authorized. Runner limits are 2 CPUs, child CPU 115s/supervisor120s, AS6GiB, sampled process-group RSS6GiB, arena2, deadline130s/outer140s. Samples can miss transient RSS; child CPU is cumulative rusage, not a universal cgroup attestation. Receipt-writer subprocesses have their own 10s/512MiB caps and their full resource use is not independently sampled. Frozen-before verified all 146 bindings unchanged. Frozen-after and terminal actual-byte manifest/verification are separate delivery evidence.

Remaining tasks are precise: root adjudicates significance using the complete source adaptation and its objections; obtain the final journal body only through a concretely identified independent lawful primary file or explicitly retain the source-version HOLD; only after qualification should root authorize a literal formal witness, dependency/axiom audit, independent formal statement review and extracted replay. No such implementation has been authorized or dispatched here. No change to acceptance or credit follows from this review.

## Final acquisition and operational addendum

Five new direct GET attempts in this review (cap 12), all precharged in access-budget.json and individually recorded in access-1.json through access-5.json. The author page, both arXiv abstract histories and the SOFSEM slides succeeded. Both latest arXiv pages are byte-identical to the copied pages and still show only v1. The SOFSEM primary slides were converted with exit 0; their actual forward proof uses alternating sums on arrays, and their converse recursively assigns g/h values without conflict in the absence of closed arrays. This is planar, not a three-coordinate primitive-norm theorem. The Plovdiv Motzkin abstract GET returned 403; no retry. Its primary body is UNREAD; the search result describes convex Minkowski sums and epigraphs, so no applicable three-coordinate theorem is identified and none is inferred. Brawley's primary body remains unread; only screened for its distinct finite-field/right-polynomial meaning, not used as a clearance theorem. The anonymous MaRDI citation nodes and generic 'simpler Sternfeld proof' title do not specify an applicable primitive-norm result; their bodies are not claimed read.

The review's five GETs are separate from the inherited author's nine annihilation-route requests, which are already preserved in input/all-access.json. No shared registry request was repeated or charged as fresh here. All five outcomes, including denied/unavailable telemetry, remain candid. The long acquisition runner completed exit 0 in 83.93 seconds and all its child requests/converters were synchronously reaped. No outstanding tool job remains. Three native calls/nine strings are exhausted; no further search.

Source reading is limited to own input, three exact author query-plan files explicitly authorized for avoiding repeats, this lane's harness, the PDF skill, the independent author page and bounded primary acquisitions. Neither protected lanes nor unrelated author mathematics were opened. The author publication list was read only as routing metadata. Frozen-after rechecks the 146 exact authorized bindings, with no browsing of their directories. The final manifest includes actual hashes of all completed runner receipt JSONs and copied inputs; terminal exclusions are explicit to avoid circular hashes.

Terminal verification note: invoking verify_frozen.py underneath run.py failed before hashing because the verifier tries to set CPU hard limit 120 while the runner child already has hard limit 115. This failure is preserved as inventories-and-frozen-after.receipt.json, exit 1; the verifier's own traceback is preserved in its output. Corrected invocation used the supplied verifier directly under timeout140, as with the mandatory before invocation; it completed exit 0 and verified all 146 bindings with no mismatches. This is a changed invocation, not an unchanged failed-call retry, and does not modify the harness. The verifier is the explicit bootstrap/frozen-check exception to the run/writer workflow. All other source processing/writes use the provided runner/writer. Resource inventory records the failure rather than claiming every job succeeded.
