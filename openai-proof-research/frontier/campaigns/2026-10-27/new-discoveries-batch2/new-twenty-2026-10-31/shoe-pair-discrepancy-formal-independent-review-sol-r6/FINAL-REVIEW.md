# Independent final review — MathDB 324571

Recommendation: REVISE the manuscript description of the implemented block estimate, then submit to root for the separate process/prior/significance acceptance decision. The unchanged production mathematics and formal endpoints pass this independent technical review. Technical PASS is not acceptance. Credit is 0; the campaign remains 55/60 beyond 39 prior results.

This review was performed personally as GPT-6.1 Sol high/default, without children, network, mathematical programs or production edits. The incomplete r5 review was not adopted as certification.

## Literal, original and final source

The copied literal asks sup_p D(p,p)<1 over all discrete distributions. Its base64 copied raw line decodes to exactly the literal object; raw SHA256 is 6267c93aa889fa427f5e429183acdafe7fc0a283f7b3665189ae94abc033f48f, original line 4099. No original provenance path was research-opened.

I personally read original arXiv:1211.6486v2 Section 2, Section 4, and the full shoe section including original Conjecture 4 equation (30). I independently read the final AAP 47 (2015), 292–305, DOI 10.1239/aap/1427814592, Section 2, Section 4 and full Sections 9.1–9.2, including Conjecture 4 equation (19), Theorem 3 and the distinction from Conjecture 5. The final-source TV and strict-alternation passages were personally displayed before the first compilation in this lane (exact_source_sections receipt). Later source rendering independently confirms final pp.295,302–304. Figure 4 is only a limiting-family plot; its numerical maximum was neither checked nor used.

The model is L1,R1,L2,R2,... with independent equal marginal law p. A collision occurs as soon as any opposite-side earlier/current colors coincide. The first arriving matching shoe determines a unique color even with multiple partners. Same-side repetition does not stop the process. Source TV is sup_A|P(X in A)-P(Y in A)|, equivalently half the absolute-difference sum. The conditional independent pair law and chronological winner law are different experiments. No simultaneous-pair tie rule, random-side schedule, finite support, positive-support-only assumption or caller-provided law identity replaces them.

## Independent ordinary proof and all core bodies

Write s=sum_i p_i². A PMF has a positive coordinate, so 0<s<=1, including infinite support; p_i<=sqrt(s). The independent first-pair equality event is the disjoint countable union of its color events, giving mass s and conditional masses x_i=p_i²/s. Normalization is justified before toPMF. All coordinates and finite cylinders come from the actual infinite product measure, with measurable stopping and winner fibers.

The formal HasMatch prefix n includes positions strictly below n, with even zero-based positions left and odd positions right. FirstMatch n is HasMatch(n+1) and not HasMatch(n); firstLength is the least matching prefix, and winner samples firstLength-1. The firstMatch_color and winner_at_first bodies settle both arrival parities without an off-by-one gap. Failure through 2N implies failure of N aligned pairs. Reindexing the iid product into independent two-coordinate blocks proves the probability (1-s)^N. The tail bound and its zero limit prove almost-sure termination. Arbitrary fallback changes only a null set.

For small s<1/64 set K=floor(1/(4sqrt(s))). The floor bounds prove K>=2, K>=1/(8sqrt(s)), K sqrt(s)<=1/4, K²s<=1/16 and K²>=1/(64s). These inequalities use s>0; the threshold equality belongs to the large branch.

For a,b<K, Isolated specifies precisely one occurrence of color i on each side at a,b, all other first-K positions avoiding i. Even/odd parity and unequal same-side positions give the exact distinct two designated coordinates; erasing them leaves 2K-2 coordinates. The cylinder probability is p_i²(1-p_i)^(2K-2). Bernoulli's inequality and Kp_i<=1/4 give this at least p_i²/2, including p_i=0 without conditioning on a null event.

A competing pair c,d with c!=a,d!=b uses four distinct time coordinates. ShoeCollision bounds the intersection with Isolated by the unrestricted four-coordinate event, then sums its p_i² p_j² probabilities over j. Thus each cost is <=p_i²s. No independence of overlapping competing pairs is assumed. The finite union bound counts at most K² pairs and costs <=p_i²/16. The good event therefore has mass >=7p_i²/16>=p_i²/4. Repeated positions sharing a designated shoe cannot create a different common color; the GoodBlock definition and OnlyCommon proof explicitly handle this.

Two good events for the same i have unique isolated positions, so all K² events are disjoint. Each forces the actual first chronological winner to have color i before or at prefix 2K. Summing gives y_i>=K²p_i²/4>=p_i²/(256s)=x_i/256. For s>=1/64 the first pair alone gives y_i>=p_i²>=x_i/256. Zero coordinates, point masses, boundary equality and infinite support are all covered.

The two PMFs have real summable masses summing to 1. Absolute differences are dominated by their summed masses. Termwise |x-y|=x+y-2min(x,y) therefore sums to TV=1-sum min(x,y)<=255/256. Positive-difference subsets attain the subset supremum; arbitrary subsets satisfy both signed inequalities. The sourceTV_eq_countableTV body proves the source convention exactly. A uniform bound on the whole nonempty range yields sup<=255/256<1, not merely pointwise strictness. sourceDiscrepancy_bound actually rewrites conditionalColorMeasure_toPMF and sourceY_eq; these bridges are consumed, not hypotheses.

I read the full source text of all 23 core modules and the three control modules. The named audit modules were compiled and their outputs inspected; they contain print commands rather than additional mathematical results. No production proof fix is required.

## Source-to-definition map

| Source obligation | Actual definitions and proof bodies |
|---|---|
| Discrete law, independent chronological draws | ShoeBase.DiscreteLaw/Sample; ShoeProbability.sampleMeasure, cylinder_probability, coordinate_law |
| Odd-left/even-right chronological intersection | ShoeBase.HasMatch, FirstMatch, firstLength, winner, firstMatch_color; ShoeStopping.winner_at_first |
| Measurability and actual winner PMF | ShoeProbability.measurable_hasMatch/measurable_terminates; ShoeStopping.winner_fiber/measurable_winner/winningLaw_apply |
| Conditional pair sampling and nonzero overlap | ShoePair.collisionMass_ne_zero/pairLaw; ShoeConditional.pair_equality_probability/conditionalColorMeasure_probability/conditionalColorMeasure_toPMF |
| Almost-sure termination and arbitrary fallback | ShoeDiagonal.blocks_law/diagonal_failure_probability/stopping_tail_bound; ShoeTermination.nontermination_probability_zero/fallback_ae |
| Unique-color block forcing | ShoeBlock.Isolated/GoodBlock/OnlyCommon/winner_of_goodBlock/isolated_positions_unique |
| Exact cylinder mass, competitor bound and disjoint sum | ShoeBlockProbability.isolated_probability; ShoeCollision.four_coordinates_probability/isolated_le_good_add_collisions; ShoeBlockSum.goodBlock_sum_le_winning |
| Floor, sqrt, Bernoulli, both mass branches | ShoeScale.blockSize_scale/realProb_le_sqrt/bernoulli_complement; ShoeMinorization.real_goodBlock_lower/winningLaw_minorization |
| Infinite sums and source TV | ShoeTV.pmf_real_summable/pmf_real_sum/countableTV_overlap; ShoeSourceTV.sourceTV_eq_countableTV |
| Source-defined universal endpoint | ShoeEndpoint.sourceX/sourceY/sourceY_eq/sourceDiscrepancy_bound/source_strict_universal_supremum |
| Injective color coding and chronology | ShoeRelabel.hasMatch_relabel_iff/firstMatch_relabel_iff/firstLength_relabel/winner_relabel_of_terminates |
| Product-law and winner-measure transport | ShoeColorMeasure.colorSampleMeasure_map/colorWinner_relabel; ShoeColorWinner.colorWinner_measure_transport |
| Conditional measure transport | ShoeColorConditional.color_pair_equality_transport/colorConditionalMeasure_transport |
| Subset-TV and countable endpoint | ShoeColorEndpoint.colorTV_coding/colorDiscrepancy_coding/countable_color_strict_universal_supremum |
| Finite normalized zero extension | ShoeColorEndpoint.finite_zeroExtension_discrepancy; ShoeColorControls.finite_zeroExtension_outside |
| Generic normalization and PMF certificates | ShoeColorNormalization.color_ae_terminates/colorConditionalMeasure_probability/colorWinner_probability/color_fallback_ae; ShoeColorPMF.colorConditional_toPMF_transport/colorWinner_toPMF_transport |

## Generic countable transport

The hypotheses are a countable alphabet with measurable singletons, hence every subset measurable, and p:PMF alpha. An injection e:alpha->Nat exists. Coordinate relabeling pushes the genuine product measure to sampleMeasure(p.map e). Injectivity preserves HasMatch at every prefix, hence first time and its mark. The explicit fallback is mapped with e, so the transported colorWinner identity is even pointwise; default-based winner identities correctly assume termination. Pullback of the Nat null nontermination event establishes the generic almost-sure statement.

The conditional equality probability transports to collisionMass(p.map e)>0. Normalized restriction and first-coordinate projection commute with the injection, giving genuine conditional-measure transport. The winner pushforward also commutes. For TV, every source subset is represented by its image and every Nat subset pulls back; this proves equality of entire ranges of subset differences, including outside-image coordinates. colorDiscrepancy_coding then consumes the Nat sourceDiscrepancy_bound. This is semantic transport, with no conclusion-bearing premise or new answer definition.

The finite extension is p.map Fin.val, a normalized PMF, and the finite discrepancy theorem transports both experiments. The outside certificate proves every unused Nat mass is zero. Empty alpha admits no PMF; whenever a PMF exists it implies nonemptiness and permits a fallback. The universal theorem explicitly takes a fallback c, ensuring a nonempty PMF range via PMF.pure c. It excludes no possible probability law. Separate generic normalization/PMF certificates are true and audited, although the earlier measure-level endpoint already follows by transport.

## Fresh compiler, checker, replay and deep audit

The own build was empty. Before any compiler, I checked actual Lean 4.34.1 runtime, lean and leanchecker binary hashes against PINS.json, mathlib lean-toolchain/lake-manifest metadata and actual HEAD text against revision d13f23b723b8a846827a245b89c10fc7d3f11612. Reading pinned metadata was not a git command. Only own build and pinned upstream libraries entered LEAN_PATH.

All 28 copied modules passed -j1 -M3500 -DwarningAsError=true and module-form leanchecker. A separate replay started with empty replay/build, extracted only all 28 source texts through write_lane.py, and repeated strict compilation then checker sequentially using replay/build plus upstream libraries only. Postchecker source, extracted-source and both olean hashes, plus each of the 112 exact build/checker receipt and log hashes, are in results/strict-replay-evidence.json. Source hashes agree after checking. Olean hashes are recorded, not assumed path-independent.

I read and rebuilt the actual ShoeReachableAudit tool, and checked its module. Its setExporting false environment includes private/generated constants. getModuleIdxFor? selects actual source origins, not namespace guesses. Each reachable declaration contributes getUsedConstants of its full type and ci.value?(allowOpaque:=true), actual body presence, axiom status and unsafe flag. Unavailable bodies are not represented as inspected bodies. Imported library truth is trusted under AGENTS; no claim is made to independently mathematically reprove 29,367 library/proof nodes.

The fresh tool emits 259 roots and 29,367 union nodes, matching the author counts independently. Of these roots 242 belong to core modules and 17 to control modules; print-only named-audit modules add no declarations. A separate eight-way disjoint Name.hash-modulo-8 metadata partition enumerates all 428,468 environment declarations without dumping their unrelated bodies. Its union reproduces exactly all 259 production/control roots and agrees with every reachable node's origin/unsafe metadata.

audit/validate.py independently parses emitted edges, rejects duplicate/inconsistent nodes and missing dependencies, computes the iterative transitive closure and verifies the root union is exactly the node set. audit/own-nodes.json is the full memoized DAG; audit/own-closures.json contains exact 17 endpoint closures, axiom unions and origin/classification evidence. audit/environment-origins.json and audit/origin-validation.json establish the metadata partition and root coverage. Only propext, Classical.choice and Quot.sound occur; no unsafe reachable nodes. The Nat supremum closure has 29,263 nodes, countable supremum 29,308. Additional exact closures include finite discrepancy, outside mass zero, normalization, fallback and both PMF transports. The source scan finds no forbidden proof token/declaration. Print-axioms output alone was not used as the audit.

Own failed audit attempts are retained: combined metadata/body ReviewReachable reached CPU120, exit -9; monolithic metadata ReviewOrigins hit the -M3500 interpreter memory limit, exit -6; the first partition source had a parenthesis error, exit 1. I changed strategy/source before retrying, did not raise caps or rerun unchanged failure, and reaped each group. The successful body audit receipt is 1794123894993604931_lean_ShoeReachableAudit.json, log SHA f25f76afa4cb12707bdafcf07f7d5e08147a188b08a950e83738ab1c152fe037. Validation receipt is 1794124057411100904_validate_audit.json.

## Controls and manuscript

All three control modules pass strict/checker in both cold builds. Controls pay singleton/nonvacuity, odd winning arrival, same-side repeat without a match, fallback independence, unused finite zero mass and actual finite discrepancy transport. The independent read also checks both probability normalizations and the exact TV positive-subset attainment theorem. The isolated copied NegativeNoninjectiveCoding control imports the correct module and fails at its false claimed equality between distinct coordinates; receipt 1794124295012620376_lean_NegativeNoninjectiveCoding.json exits 1. No wrong-import failure is counted as semantic evidence.

I used the installed PDF skill read-only and independently rendered the existing five-page PDF via capped pdftoppm (receipt 1794124006366424367_render_paper.json). I actually viewed output/paper-1.png through paper-5.png. All five pages are readable, with no clipping, missing formulas or overlapping text observed. Text notation uses ASCII rather than typeset mathematics but is intelligible.

Page 1: source experiment, full-law scope, tail and fallback statements correct.
Page 2: ordinary conditional argument is correct, but its attribution of the sharper factor-retaining unconditioned calculation to the actual ShoeCollision/ShoeMinorization path is inaccurate. Minimal replacement for that paragraph: “The implementation bounds E_ab intersect each competing collision by the unrestricted four-coordinate event, of probability at most p_i²s after summation over colors. Thus P(F_ab)>=p_i²/2-K²p_i²s>=7p_i²/16>=p_i²/4.” Retain the ordinary conditional derivation as a separate valid proof. No production change needed.
Page 3: countable injection, actual measure/PMF transport, finite extension and empty-alphabet explanation correct.
Page 4: 23 core/3 control/2 named-audit module classification and 259/29367/29263/29308 audit counts agree with fresh evidence. The report describes author replay; independent replay is now separately evidenced. No imported universe was body-dumped.
Page 5: credit0, 55/60 beyond39, bounded novelty and inherited failures are properly separated. Add the existing recorded current deviation explicitly: “Final-source Section4 TV was personally displayed late after compilation; this does not claim personal prebuild reading.” The general displayed-source wording otherwise obscures this chronology. Independent prebuild reading in this lane does not waive the author's deviation.

Native image-display peak memory and compiler-internal memory telemetry are unavailable. Rendering receipts provide sampled process-group RSS, not a global or cgroup guarantee.

## Prior, significance, family and strongest contrary cases

I compared the copied 55 accepted literal statements and 39 trusted accepted scopes, without old certificate re-audit. None states the first bipartite-collision marked-color uniform bound. Vendi, Renyi-increment and other probability/mean scopes concern different observables; shared elementary inequalities do not identify a family duplicate. Countable/finite transport, the numerical constant, helpers and parameter variants earn no extra credit.

I personally read the copied Bhattacharya arXiv:1311.4243v5 (24 May 2016) Definition1.1, Theorem1.1 and Section2.1 proof/converse, Definition1.3/Theorem1.3, Section4.1 proof and Appendix A. Mapping urns to shoe colors and its two ball colors to left/right gives a related bipartite collision. However its side choices are independent random marks with fixed probabilities; its diffuse triangular-array hypotheses and conclusions concern scaled collision-time weak limits. The Poisson marking and product survival proof does not produce a fixed-law chronological winning-color minorization under deterministic alternation. Its general growing-graph framework can describe a deterministic bipartite schedule, but the inspected graph results specialize to preferential attachment and paths, not an all-law marked-color theorem for that schedule. Time laws alone do not determine the winning color.

The source's own Theorem3 concerns a particular asymptotic family and limit formula; a missing universal extremal theorem would be needed to turn it into this bound. Thus no complete earlier-theorem-to-target routine exclusion was established.

Strongest contrary possibility remains Galbraith–Holmes2012, A non-uniform birthday problem with applications to discrete logarithms, DAM160,1547–1560: the inspected primary paper describes a time-varying side selection variant and expected first collision time, which is closer to deterministic schedules. Its actual body remains 404/unread, with no alternate fetch authorized or attempted. No specific marked-color theorem applicable to this target was identified, so this is a concrete bounded-access limit, not automatic clearance and not a generic worldwide-unknown veto. Root must adjudicate this remaining limit.

The cached registry evidence contains only same-day root heads and indexed nonmatches; it does not certify current proof-body coverage or worldwide novelty. No new network check was performed. Exact heads and limitations remain in the copied registry inventory. Familiar birthday-scale blocking, elementary tools and a weak constant do not by themselves prove routineness. In favor of significance, a uniform bound over every countable law resolves an explicit conjecture retained in the final paper. Against it, the argument may be available in wider marked-collision literature. My bounded recommendation preserves the candidate as one possible significant family, with root alone deciding acceptance.

## Process and disposition

The historical r3 three full imported-universe audit failures (-6) and all direct uncapped/runpy/overlap/render/thread-session/checker chronology failures remain preserved in copied root integrations and CHECKPOINT. The historical claim of no endpoint/PDF belongs to an earlier segment; a later Nat endpoint and the current five-page paper exist. The r4 standalone display helper was prospective and self-capped only, never a retroactive waiver. Bulk receipt metadata machine-reading does not mean personal display of every record. The author's late final-source TV display remains a separate unresolved process decision.

The prior r5 two guessed log paths failed before displaying content; root records unchanged 1596 frozen files and no compiler execution. This is neither universal compliance nor mathematical rejection. My new review uses receipt-derived displays and is independently authorized.

Own bootstrap and before verifier were the exact first two commands. Frozen-before found all 2120 unchanged. All substantive subsequent operations used the own immutable runner; displayed source/log data used the exact completed receipt basename. Direct viewing was limited to own rendered pages. Own audit failures and output truncations are retained; focused later reads recover the substantive mathematical passages. Bulk imported metadata was machine-validated, not personally inspected node by node. No new protected access, frozen mutation, uncapped substantive execution, overlapping jobs or network action is known. No universal procedural PASS is assigned.

The report and keyed JSON recommend manuscript revision, technical PASS for the unchanged production theorem, and a separate root decision on inherited process/prior/significance. Final standalone frozen-after and terminal manifest close the disk handback. No ledger, author source or PDF was edited. Credit stays 0.

