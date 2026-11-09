# MathDB 352038: published-version and targeted registry comparison r2

2026-11-01 UTC. **Overall HOLD / PARK; credit 0; campaign unchanged at 3/20 beyond39.** Independent follow-up to significance-review-r1, not acceptance or a second significance vote. No Lean replay was run and the separate fidelity worker was not polled.

| Objection | Verdict | Disposition |
|---|---|---|
| O1 published mathematical body | **HOLD, unresolved** | Bounded legitimate retrieval did not obtain the journal body or an authenticated accepted manuscript. Retained/changed/removed/corrected/resolved are all **undetermined**. |
| O2 bounded prior-art characterization | **PASS as a bounded investigation; root disposition still required** | Complete current relevant subtree, complete Problems path inventory, direct three-file history/body comparison now obtained. No inspected full-scope subsumer. This is not complete literature or repository-history clearance and does not close O1 or prove novelty. |

## Inputs and integrity

Read the project, second-batch and new-twenty AGENTS; parsed current and ancestor ledgers and prior-campaign context. Read prior REVIEW.md and review.json fully first, then its entire HTTP receipt list and retained official XML/OpenAlex metadata, relevant Crossref record, author SUMMARY/PROOF/PRIOR-ART, literal raw352038, source receipts and formal endpoint. The supplied frozen-inputs.json binds165 files. All165 match before and after; see integrity-before.json and integrity-after.json. Files outside this assigned directory were read only. Packet verification is byte integrity, not a rebuilt certificate. No count or credit changes are authorized by this report.

## O1: actual source comparison and exact remaining gap

The authenticated bibliographic counterpart is Lachmann–Wiart, *The area of empty axis-parallel boxes amidst 2-dimensional lattice points*, Journal of Complexity76(2023),101724, DOI [10.1016/j.jco.2022.101724](https://doi.org/10.1016/j.jco.2022.101724), PII S0885064X22000899. The prior official API200 body was re-read: it has coredata, DOI, title and closed-access flags, and **no mathematical article body**. OpenAlex's only location is the closed publishedVersion with null PDF URL. Neither is an accepted manuscript.

The readable reference is [arXiv2109.11222v1](https://arxiv.org/pdf/2109.11222v1), SHA256 `f284e5f0dbf769bed66df954febd05b4f9e90435c754617a0d9195ac61fd2c43`. Its printed pages13 and26–28 were read directly from the frozen extracted full PDF body, with prior visual verification retained in the frozen inputs. Body findings:

| v1 label/page | Actual mathematical role | Published counterpart |
|---|---|---|
| §4 p13, definitions and Theorem4.4 | Pure period means reduced quadratic number; quadratic integer is essential for integral norms. Minimal period l. Noninitial coefficients bounded by floor((Delta−conjugate Delta)/2), in particular ceil(a0/2). | Unread; comparison unavailable. |
| A.1 p26, full proof | Expresses complete quotient as (integer+Delta)/signed norm. Reduced conjugate inequalities force the integer shift to zero for norm1. This isolates the initial period class, not every norm. | Unread. |
| A.2 pp26–27, full proof | Uses convergent product identities (16)–(18) and recurrence to show absolute norm invariant on period classes. It does not make distinct coefficients have distinct norms. | Unread. |
| A.3 p27, full proof | Convergent-error inequalities, norm periodicity and arbitrarily large translates give (Delta−conjugate Delta)/(ai+2) ≤ absolute norm ≤ (Delta−conjugate Delta)/ai. | Unread. |
| Proof4.4 and A.4 p28 | Integral positive norm<2 gives norm1, then A.1 excludes noninitial indices; shifted square-root corollary is a special case. | Unread. |
| A.5 p28 | Universal purely periodic quadratic integer; C is a set of coefficients, nth largest existing distinct value bounded by a0/n. No square-root-only restriction or distinct-norm hypothesis. | Retention, change, removal and resolution undetermined. |

For the already checked delta=(55+sqrt3049)/2, the existing seventh distinct coefficient8 exceeds55/7. The source proof route above is consistent with the established norm collision: distinct coefficients9 and8 share absolute norm6. It therefore supplies no injective norm-rank argument. This follow-up supplies no new mathematical or formal defect and no reason to reverse the qualified significance PASS. It also cannot claim that the journal still states the conjecture. Removal alone, were it later demonstrated, would not establish a resolution.

Bounded new access/search routes were exact changed-title/DOI/author searches, institutional-domain searches (epub.jku.at, sfb-qmc.jku.at, ricam.oeaw.ac.at), the JKU institute team page, SFB publication page, and the correct ScienceDirect landing page. The team page returned200 but lists Lachmann and Wiart as plain names, without a manuscript link. The indexed SFB publication item still says submitted and links arXiv2109.11222; it authenticates no later body. Direct SFB TLS verification failed; web retrieval gave502/timeout; no TLS verification was disabled. Correct ScienceDirect returned403 and was not directly retried. JKU repository root returned403; an inadvertent second web open of the same root returned403 again. This was a denied-route retry lapse, not successful access or a bypass; no further attempt was made. The inherited incorrect ScienceDirect PII and MathDB/Palomar denied routes were never opened. Search-engine cached snippets are retained only as snippets, never as appendix proof evidence. No author contact, accounts, private credentials, uploads or tabs.

**Park O1:** obtain a lawful readable journal body or an explicitly authenticated accepted manuscript, then fill the right column from actual definitions and proof pages. This task has not acquired such a copy. No journal/preprint equivalence is inferred from titles, abstract agreement, MaRDI's arXiv link, or the lack of arXiv revisions.

## O2: registry heads, complete relevant scope and history

Fresh heads at13:05:53–56UTC: OpenAI/math `4eaee87548250b2682affda7d05d947c05554bae`; Omega/trureturing `e194aa70f3b4c2c26ff472e932995c67e224bd24`. URLs, times, full status/headers, raw bodies and SHA256 are retained in http-receipts.jsonl. OpenAI is unchanged from r1; its complete preprints listing and filename-screen limitations therefore persist. No whole OpenAI proof-body audit is claimed.

Omega advanced from r1's9abc86d. The fresh compare reports31commits and14changed files, all listed in omega-delta.body; they concern cycle sums, graph domination and set families, not the continued-fraction subtree. This finite delta is below the300file cap. It is not baseline clearance.

The fresh nonrecursive root leads to a **nontruncated D5 tree**,13297entries, and a **nontruncated Problems tree**,1629entries. Thus the old1000Problems cap is replaced for this current path inventory only. Old truncated root and old capped historical comparisons remain incomplete evidence. The D5 screen and selected scope are retained in omega-d5-screen.json, omega-problems-screen.json and relevant-subtree.json.

All11current bodies under D5/S1/Depth/ContinuedFractions were downloaded and read, including proofs:

- CompleteQuotientBound: `pullback_discriminant` is a ring identity with det² factor; `unimodular_transform_preserves_discriminant` specializes det=±1. No coefficient rank theorem.
- CompleteQuotientRecursion: `complete_quotient_quadratic_chain_invariants` propagates crossover c[n+1]=a[n] and discriminant invariance through an assumed compatible chain. No norm injectivity or rank estimate.
- PeriodicImpliesQuadratic: `eventually_periodic_cf_implies_quadratic_irrational` uses positive transfer matrices, a quadratic fixed point and prefix transport. Its conclusion need not be monic and says nothing about the distinct coefficient ordering.
- QuadraticImpliesPeriodic: `quadratic_irrational_eventually_periodic_of_bounded_complete_quotients` explicitly assumes a bounded certificate, uses finite polynomial-root candidates and repeated quotient states. No construction of the counterexample or rank bound.
- BinarySimplestTail and PeriodicThreeComplement: specific golden/all-ones and constant3/complement examples, not the55/3049 witness or a rank obstruction.
- GaussInverseStep and GaussInfiniteFiber: floor recovery and infinitely many inverse branches, without integral-quadratic rank constraints.
- FiniteTerminationApproximation and IrrationalSlopeFaithfulness: Dirichlet/nearest-integer finite errors and irrational integer-pair encoding/golden separation. No all-rank continued-fraction assertion.
- ZarembaFiveFiniteFront: sound finite Euclidean checker and rational-denominator table through1024. Rational numerator choice with digits≤5 does not imply a purely periodic integral counterexample.

Additional path-screen leads were body-read: PartialQuotientExtraction mechanically extracts a **rational** tail maximum and substitutes it in an explicitly assumed twelve-scale sample minimum; DominantPartialQuotientGap is a finite complex-sum reverse-triangle wrapper (despite its name); ContinuedFractionTailBeattyRefutation refutes a different generalized continued-fraction tail rounding assertion by a contracting error operator for u=2,v=1. Its `IsTail` uses n²/s[n+1], and its conclusion concerns floors of linear asymptotics, not distinct regular coefficients of quadratic integers. None supplies the missing scope bridge.

Direct path histories at the frozen current head give exactly one commit each for Bound, Recursion and PeriodicImpliesQuadratic (per_page100, no next-page Link). Respective commit/date: `1ed2cfcc1776e4595462cee9e98314d7d13b7a88`, Aug23 15:25:41UTC; `dcb5bc1821a44474a8891787c2de6fbcc0b5f8ba`, Aug23 19:06:02UTC; `f86456bf0443d56fd6ba7301039c4b627ef30dcf`, Aug23 12:28:55UTC. Raw introduction-commit bodies are byte-identical to current bodies, respectively SHA256 d5c2720e8da131226bb02a2b9a5b348c6e90bd8412e30e17e8c31e1245d15e9f; d4e1a3894cc7bbb97cb947ebcc1b2726878c5ae66704cbe719e8ba969ac0ffe2; e77adb287bcbcc4c822bbd46ac1582a741d22027e4ed1c32b7fa35e91c93647a. Subtree history returns18commits with no next-page Link. This is path-filtered reachable history, not deleted/renamed/unreachable-history completeness. These modules precede this candidate but do not subsume it; no later independent same-result counterpart was found in read bodies.

Citation coverage remains bounded to the prior review's two body-read journal citers and selected specialist sources. New MaRDI citation links include older2013 Bilyk discrepancy work; a citation graph edge is not chronology or proof of a resolution of a2021 conjecture. No extra citation-universe clearance is claimed. Current MathDB search snippets are not live solution-body authentication and the open label has no novelty weight.

## Handback

No new source-fidelity consequence beyond the surviving journal gap. Preserve the qualified mathematical significance PASS, leave novelty and overall acceptance HOLD, award0. Root may accept this narrower O2 characterization, but O1 still blocks source/version clearance. No child agents, git, shared edits, publishing, external messages or background jobs. Fetch processes used two-CPU affinity,1GiB address-space and45CPU-second limits,18-second per-request timeout and20MiB per-response ceiling; all finished. Full downloaded outputs and failures are retained in this directory.
