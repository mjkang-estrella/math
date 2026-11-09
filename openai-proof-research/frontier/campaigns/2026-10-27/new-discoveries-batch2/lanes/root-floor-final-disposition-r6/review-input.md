# Final adversarial review of the revised floor-sum source packet

30 October 2026. Solo review; no children. Recommendation: retain the mathematical/source certificate as PASS, but HOLD campaign acceptance. PDF completion is an explicit uncompleted gate; current-registry and specified historical/citing-body novelty gaps remain open. SUBSTANTIVE is qualified PASS for the single full independently posed four-variable question, subject to root adjudication. Root alone accepts and counts. Counts remain 9 additional / 39 total / next40.

| Gate | Judgment |
|---|---|
| SOURCE | PASS for the separately stated JIS2018 p.15 all-modulus inequality |
| MATH | PASS for the universal literal inequality, with the supplied complete certificate |
| FORMAL | PASS on root/r4 replay evidence, independently byte-bound and seam-checked here; no new compilation claimed |
| PACKET | PASS: exact revised ZIP, deterministic rebuild and all-member equality |
| MANUSCRIPT | PASS as mathematical source text; no blocking mathematical wording error found |
| PDF | NOTAUTHORED / QA_NOTPERFORMED; remaining gate |
| SUBSTANTIVE | Qualified PASS; no complete classical/source-specific subsumer demonstrated |
| NOVELTY | Bounded HOLD; no full subsumer found in inspected coverage, incomplete current/historical clearance |
| Acceptance | HOLD; no credit or acceptance action by this reviewer |

## Bound inputs and independent work

The six minimal root inputs are frozen under inputs/, with original absolute paths, sizes and hashes in input-bindings.json: STATUS.md, root-independent-audit.json, reviewed-archive-receipt.json, verification-receipt.json, paper-reviewed.md and reviewed-packet/source-packet.zip. The ZIP hash is **d77b63418d77df6c1285d335e09c90f47a9ce233f0522114600caa0a72bd9c98**. Scientific bytes were copied/hashed before scientific inspection. Administrative ancestor/batch AGENTS.md, ledger.json and prior-campaign-context.json are snapshots only. The manifest and final verifier bind the review output; administrative live files are not declared immutable.

I extracted this distribution, not the root's 2510-file replay tree. Its 555 members are frozen in evidence/extracted-members.json; its internal manifest covers 554 payloads. Predecessor r2/r4 reviews, exactcoverage.json and failure reports already inside this immutable distribution were reused. I independently checked every internal payload hash, all 460 Lean files against root/extracted/formal, paper.md against paper-reviewed.md, and the included root independent-audit receipt against the supplied root receipt. Original Lean paths/hashes are references in evidence/packet-check.json, not additional copies of replay history.

I executed the extracted build_packet.py standalone mode under the prescribed guard. Its two ZIP builds reproduce the supplied revised ZIP; both tar builds reproduce a962eaffbd4632abc5e82fa2d5fbf403eabbc1e5c8be0b3b52cfd8511e60ef67. My separate check_seams.py independently compared every ZIP/tar/extracted member and reconstructed DAG reachability/counts. evidence/seam-check.json records PASS. No Lean invocation, build, source edit, PDF authoring, network retrieval, git/shared/public/browser/MathDB operation or descendant agent occurred. Extracted scientific .lean and paper files were never edited.

## Exact source and mathematical scope

The theorem is, for all positive integer m, all indexed a1,a2,a3,a4 and K with 0<=ai<m and 0<=K<m,

    sum(j=0..K) sum(T subset {1,2,3,4})
      (-1)^(4-|T|) floor((j+sum(i in T) ai)/m) >= -3 floor(m/3).

Subsets are of indices; equal values remain distinct labels. The empty subset has coefficient +1. Actual real floors, not approximate division, are identified by Source.actual_real_floor and actual_source_sum. LiteralEndpoint quantifies naturals, which precisely represents these nonnegative integer parameters; its integer-valued bound casts m/3 before multiplication by -3. No truncation of a negative natural quantity occurs.

I read the frozen actual primary text wong-current.txt introduction/definition (printed pp.1–2), Section4 (pp.14–15), full Theorem15 proof, following Conjecture17 (p.16), and publication line. Primary PDF: https://cs.uwaterloo.ca/journals/JIS/VOL21/Wong/wong7.pdf, SHA256 345c2cf3893d3c2c0371e0b2053bf02c6f04469243f7c1ca33e1d0681fc15d7d. The independently posed paragraph before Theorem15 states the exact all-m bound. Theorem15 proves only -2 floor(m/2)-floor(m/3), generally weaker. Conjecture17 additionally concerns other dimensions and specified extremal configurations; this certificate does not establish its full statement. Indexed repeats are also explicit in the source's repeated-entry examples, not a new domain extension.

Publication is 23 February 2018, confirmed by the primary body's publication line. arXiv v1 10 August 2017 / v2 14 February 2018 is inherited primary-response chronology, not a historical-version retrieval by this reviewer. The 30 October 2026 local manuscript date is not a public priority timestamp.

For H=K+1, 1<=H<=m. Each j+s lies in [0,5m), so its floor is the sum of four weak threshold indicators lm<=j+s. Counting j in [0,H-1] gives C_H(s+H-lm), where C_H(u)=max(0,min(H,u)). Threshold equality u=0 counts zero and u=H counts H. This verifies the off-by-one seam and all 64 clamps. The empty subset contribution vanishes for H<=m, but remains explicitly in the definition. At H=m the one-subset prefix sum is s; its fourth signed difference is zero. At m=1 all residues and K are zero. Sorting uses a permutation of Fin4, maps subsets bijectively and preserves cardinality, so ties cause no loss. I read Reduction.lean, Symmetry.lean, Source.lean, Endpoint.lean, and portions of SourceBridge/ClipBridge and generated semantics/node proofs; this is not a claim to have manually read every generated proof term.

I independently read the complete Theorem3.1 formula and proof of hermite2019-primary.txt, printed p.128 (Fibonacci Quarterly57(2), May2019, pp.126–133). PDF https://www.fq.math.ca/Papers/57-2/pongsriiam02072019.pdf, SHA256 29292c0a4c0fb29c80d855fe8ec48cb6db4cf4603c0e936cbfd608f1435c005a. Substitution x=s/m, their n=m, their prefix length=H gives F(s)=H floor(s/m)+max(0,H-m+(s mod m)). This is a known ingredient, properly credited, rather than a previously proved joint sharp bound.

## Formal seams and trust boundary

The root independent receipt reports 437 mathematical modules, 22 audit partitions, 459 strict serial invocations, 35,654 safe nonpartial actual declarations from 436 origins, only propext/Classical.choice/Quot.sound. The embedded root full-audit receipt agrees on the counts, endpoint and declaration-name hash 7abfdce5f2b7e1d6ba7df2fc0de7ee9a96faa975f113e04b512bfd42008a668b. The prior r4 replay is an additional independent report; this review does not relabel either as its own compilation. Exact mathematical-source identity transfers their result to the revised documentation packet. No material concern requiring another formal invocation appeared.

My cheap independent structural reconstruction finds 22,672 acyclic DAG nodes, 12,459 reachable rule nodes, 644 lemma/discharge nodes, 1,329 arithmetic-lemma nodes, and exact equality between all rule IDs and unique generated n<ID> theorem names. There are 10,188 explicitly integer/Prop semantic definitions, 64 canonical and 64 clip bridges, and 644 actual by_contra discharge blocks. These source checks supplement, not replace, kernel elaboration. Counts alone would not prove semantics.

Vars has exactly seven integer fields m,H,t,a,b,c,d. Fresh extensions are concrete conditional definitions, not freely assigned extra fields. Query has the seventeen used assertions. Assembly.query_of_neg_bound in Endpoint.lean uses the literal domain, sorting and strict negated bound and sets t=m/3; it derives all seventeen with proved source/clip/sum identities. The unused m>=3t assertion is omitted from the contradiction query, strengthening rather than weakening that obligation. In an inspected discharge (n7492), a classical contradiction explicitly reconstructs the two assumptions and applies n7490; assumptions are not merely deleted from a Python set. The full discharge coverage comes from bound root/r4 kernel evidence.

The final n22671 has only Vars and Query arguments and concludes e7489, defined as False. sorted_clamped_bound contradicts that theorem with the fully constructed query; literal_endpoint supplies the sorted-bound premise to the earlier conditional transfer. The older conditional-transfer comment in Symmetry is historically accurate for that module and is not an unresolved premise of the final endpoint.

Trust remains in Lean, the stated external environment/library cache and interpretation of the source. The distribution pins Lean4.34.1 and nine package revisions; it does not bundle/rebuild the external toolchain or all libraries. Historical generation scripts and verify_final.py have lane dependencies, explicitly disclosed in README. The supported standalone interfaces are replay.sh/full_audit.py for formal replay and build_packet.py for archive rebuilding. The rebuild's standalone branch checks hashes/build equality but returns before the historical extraction checks; I independently supplied all-member ZIP/tar/extraction comparison. README's general extraction description should be read with this branch distinction; it is not a missing check in this review.

## Manuscript, PDF and objections

The corrected abstract says “of at most one complete period,” consistent with K=m-1. Equations, integer remainder bound, source independence, actual-floor bridge and unconditional endpoint match the inspected sources. Root-completed replay is accurately documented; the revised packet is not claimed freshly recompiled. Historical worker documentation remains labelled provenance. “Final packet review ... pending” describes the packet's pre-review chronology, not acceptance. No stale PDF, public acceptance, publication, worldwide priority or full-Conjecture17 claim was found.

The manuscript explicitly depends on its full supplied computational certificate rather than pretending its explanation is a short analytic proof. This is acceptable source correctness, but does not complete the separate rendered-paper gate. The preserved marker logs report unsupported Node option then V8 initialization failure under fixed caps. I did not rerun/bypass the marker, increase limits, create a PDF or claim visual QA. PDF remains NOTAUTHORED / QA_NOTPERFORMED. Acceptance must not treat source-manuscript PASS as visual completion.

## Substantive and novelty judgment

Qualified SUBSTANTIVE PASS is appropriate for one full independently posed all-m source question. This is not a finite-modulus survey or merely formalizing a known theorem. Presburger decidability supplies a general method; it is not an actual previously established sharp inequality. Neither solver availability nor certificate length proves routine status or depth. The classical prefix formula, threshold count, sorting, decision procedure and formalization receive no separate credit. I found no complete source-specific classical subsumption bridge that would warrant exclusion as a routine corollary.

I independently assessed the inherited r2 bridge objection: C_H(u)=(|u|-|u-H|+H)/2 makes S one half the sum of four differences G(H-lm)-G(-lm). Individual lower bounds for G do not lower-bound those differences. Extra joint-shift/control and residue arguments would be required; a continuous S>=-m would still miss -m+r when m=3q+r, r=1,2. Older signed-block bounds similarly do not supply simultaneous extremality. This is an identified missing implication, not proof that a classical derivation cannot exist.

Actual-body breadth beyond my two readings is attributed to r2/exactcoverage.json and r4, preserved without laundering it into independent coverage here: Onphaeng–Pongsriiam2017 entire Theorem9 proof (pp.14–20 with introductory definitions); Tverberg2012 all three pages; Hermite2019 all eight pages; ScienceAsia2021 all five pages; and JMI2022 pp.1455–1464,1471–1475, with pp.1465–1470 unread by r2. Their documented scopes are respectively older block estimates/opposite-parity sharpness, two-variable and selected three-variable bounds, one-subset formula, univariate quadratic representation, and specified absolute-value inclusion–exclusion inequalities. No full four-variable joint prefix subsumer was identified there. I did not independently reread those additional bodies or claim a complete citing census.

NOVELTY remains bounded HOLD. Current registry head/content and the interval after the pinned 8 October2026 revision are not cleared. The pinned fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb alias screen is index evidence only. Jacobsthal1957, Carlitz1959/1960, Grimson1974 and four metadata-only predecessor citing bodies (Wythoff/Beatty sumsets, Fibonacci divisibility, Pell generating functions) remain uncleared. Metadata and absence of located matches are not priority clearance. No live retrieval was performed here: the task's parked denied GitHub API/raw/codeload/diff/patch, ScienceDirect and Google challenge routes remain parked, without HEAD loops, proxy, TLS-disable or browser bypass. The existing actual-body evidence supports the qualified substantive judgment but cannot fill these concrete novelty gaps.

Root should retain the proved source certificate, decide the single-family substantive standard explicitly, adjudicate these bounded novelty limitations without claiming exhaustive priority, and keep acceptance on HOLD while the mandatory PDF gate is incomplete. No new count is recommended now. A future acceptance requires a root decision and completion of applicable outstanding gates, not another redundant 459-invocation replay merely echoing this review.

## Integrity and failures

FAILURES.md preserves this lane's truncated administrative display and failed guessed filename reads, and identifies inherited PDF/access/replay failures. No failed scientific test was suppressed. All Python, copying/extraction, hashing, checks and archive generation used the exact assigned helper path with OPENBLAS_NUM_THREADS=1 OMP_NUM_THREADS=1 PYTHONDONTWRITEBYTECODE=1 and unchanged AS/groupRSS512MiB CPU210 wall230. Native bounded reads and apply_patch were used. Manifest excludes itself and verification-receipt.json; a separate guarded final_verify.py rechecks all frozen scientific originals/copies, archive members and complete output coverage after substantive writes. A passing integrity receipt does not alter PDF, novelty, acceptance or counts.
