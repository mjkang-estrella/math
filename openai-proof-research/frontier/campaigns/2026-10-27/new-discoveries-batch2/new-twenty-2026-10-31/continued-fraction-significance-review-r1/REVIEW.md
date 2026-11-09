# Independent source, novelty and significance review: MathDB 352038

Review date: 2026-11-01 UTC. **Overall HOLD; awarded credit 0.** Campaign remains 3/20 beyond 39. This is an independent content review, not acceptance, a manuscript, or an independent Lean replay.

| Gate | Verdict | Exact qualification |
|---|---|---|
| Source / version | HOLD | PASS for the literal arXiv v1 / cached MathDB statement; published counterpart authenticated bibliographically, but its mathematical body remains unread. |
| Bounded prior art / subsumption | HOLD | No matching refutation or full-scope subsumer found in inspected bodies. Published-version gap is material; Omega baseline listing remains incomplete. |
| Novelty | HOLD | New-to-literature status is not established. Neither the open label nor bounded nonfinding supplies that status. |
| Mathematical significance | PASS, qualified | The actual v1 universal rank conjecture suffers a genuine interior counterexample, with a concrete norm-collision obstruction to an apparent proof route. This supports conditional eligibility, not an unconditional novelty or acceptance verdict. |

**Recommendation: conditional 1 for this single refutation only if the material source/prior-art objection below is closed and the separate fidelity/replay and campaign requirements pass. Current recommended award is 0.** No mathematical defect was found in the ordinary counterexample or the read-only Lean endpoint.

## Frozen inputs and scope

Read applicable repository, batch and campaign AGENTS, ancestor ledger/prior-campaign context, source pin/catalogue, author SUMMARY.md, PROOF.md, PRIOR-ART.md, results.json entry 352038, raw/352038.jsonl, Candidate.lean, packet members and source receipts. All 130 bound files matched before review; all are checked again at handback. See integrity-before.json and integrity-after.json. All 15 author downloaded-byte receipts were recomputed successfully in author-receipt-verification.json.

Candidate SHA256: `cd853bb4e522d8cc6619f69140d25fc7d234f13a23572157e9811b4f81ff4ecd`.
Packet SHA256: `d49c192a38fa822deadf801b6a18ce7169c5db4e71d0b69618305cc6b3bccd8e`.
The packet contains exactly Candidate.lean, Audit.lean and replay.py; its Candidate bytes match the frozen source. The claimed 31-declaration strict audit is author evidence; I did not independently replay or attest it. No shared/author edits, git, uploads, external messages, browser tabs, child agents or background jobs were used. Writes are confined to this review directory.

## Source and version finding

The actual v1 Appendix A, Lemmas A.1–A.3 and their proofs, proof of Theorem 4.4, Corollary A.4 and Conjecture A.5 were read, together with the actual Theorem 4.4 statement on p13. The complete source p28 was visually inspected from the author's preserved image. The set braces in C(Delta) are genuine; there is no multiplicity, unit, prime-discriminant or square-root-only hypothesis in A.5. Natural ranks run through the finite set's cardinality; the witness uses an existing seventh value, not an undefined out-of-range rank.

A fresh [explicit v1 PDF](https://arxiv.org/pdf/2109.11222v1) has SHA256 `f284e5f0dbf769bed66df954febd05b4f9e90435c754617a0d9195ac61fd2c43`, identical to the author's unversioned PDF. The fresh [arXiv history page](https://arxiv.org/abs/2109.11222) lists only v1, submitted 2021-09-23 09:10 UTC. That authenticates the downloaded v1, not all later publication history.

**Material new finding:** a published counterpart exists with changed title, *The area of empty axis-parallel boxes amidst 2-dimensional lattice points*, Journal of Complexity 76 (2023), 101724, [DOI 10.1016/j.jco.2022.101724](https://doi.org/10.1016/j.jco.2022.101724). Crossref and the official Elsevier API independently identify it; the official metadata gives June 2023 and openaccess=false. This corrects any inference that lack of a journalref on arXiv means no journal publication. The author had explicitly left authentication incomplete, so this is a closure requirement rather than an accusation of a false priority claim.

The [official API request](https://api.elsevier.com/content/article/PII:S0885064X22000899?httpAccept=text/xml) returned HTTP200 but **only core metadata**, no theorem/proof body. OpenAlex likewise supplied no OA published-body location. A web attempt at a different, incorrect ScienceDirect PII returned403; that probe is not evidence about the correct paper and was not retried. DOI web opening failed. No MathDB/Palomar denied route was retried; search-index snippets remain snippets. No access-control circumvention or author contact occurred. The published A.5 may survive, change, disappear, or be resolved: this review cannot choose among those possibilities without its body.

## Independent exact mathematics

Run `timeout 15s python check_exact.py` from this directory. It uses integer arithmetic only, 2-CPU affinity, 512MiB address-space, 10CPU-second and 15-second wall limits. exact-check.log is the full output; exact-check.json records every independently generated state. This is an ordinary exact certificate check, not a Lean replay.

For s=sqrt(3049), 55<s<56. Delta=(55+s)/2 satisfies the monic integer equation Delta²−55Delta−6=0 and is irrational. Its conjugate lies strictly between −1 and 0 and Delta>1. Thus this is a reduced quadratic **algebraic integer**, not merely a reduced quadratic irrational. In particular, a classical example with nonmonic minimal polynomial would not suffice here.

Starting at (m,d)=(55,2), independently compute a=floor((m+s)/d) using `(m+isqrt(3049))//d`, then m'=ad−m and d'=(3049−m'²)/d. Exact division and positive denominators hold. At every step the stronger rational inequalities ad≤m+55 and m+56≤(a+1)d hold, so a<(m+s)/d<a+1 rigorously. The first repeated state is the initial state after 85 steps. The resulting M,D,A arrays equal all three author tables byte-value for byte-value. Rationalization gives q'=(q−a)⁻¹; induction therefore certifies the infinite actual expansion, not a floating-point approximation or finite lookalike.

The descending distinct set is {55,27,18,13,10,9,8,7,6,5,4,3,2,1}. Six distinct values exceed 8, and 8 occurs. Hence w7=8 and w7−55/7=1/7>0. This is inside the domain and inside the range of defined ranks. Repetition of the block or rechoosing a period cannot change this set.

Read-only formal inspection: SourceConjecture binds every coefficient to mathlib's actual IntFractPair.stream; it imposes integrality, irrationality, a monic integer quadratic equation, a positive period and coefficient periodicity from index0. Ranking counts strictly greater elements of a Finset, hence distinctness. actual_stream and source_refutation supply the semantic bridge and negated universal endpoint. This review does not replace separate formal fidelity and rebuild work.

## Subsumption and discovery content

The v1 A.3 proof uses periodic norm invariance and convergent error estimates to obtain

    s/(a_i+2) <= |N(p_i−q_i Delta)| <= s/a_i.

A.1 identifies norm1 with the initial period class. Theorem 4.4 then excludes noninitial a_i>s/2: the positive integral norm would be <2, hence1, contradicting A.1. The witness's largest noninitial coefficient27 respects floor(s/2)=27. Corollary A.4 applies this to the specially shifted square root; it asserts no all-rank theorem.

A concrete obstruction to extending that argument is independently checked here. For the standard preceding convergent P/Q (initially 1/0), d_i=2|P²−55PQ−6Q²| at every state. The highest seven coefficient values 55,27,18,13,10,9,8 have respective associated absolute norms 1,2,3,4,5,6,6. **Distinct coefficient values 9 and 8 share norm6.** A.3 permits both: 6 lies in [s/11,s/9] and [s/10,s/8]. An argument that assigns a different positive norm to each different coefficient would fail precisely here. A.1 only separates norm1; it does not furnish that injectivity.

I read the classical reduced/pure-periodic theorem and its backward-uniqueness proof in Dummit's 2021 lecture6 (classical.body/.txt). It guarantees periodicity, not an algebraic-integer all-rank bound or its refutation. Its worked reduced example (3+sqrt13)/4 has nonmonic minimal polynomial 4x²−6x−1, so its conspicuous coefficient6 is outside this conjecture's domain. Treating all reduced irrationals as integral would produce an invalid easy objection.

I also read Lerner, [arXiv:0810.0718v2](https://arxiv.org/pdf/0810.0718v2), Theorem2 and the actual Section3 proof: the gradual Nose–Hoover/Conway-river algorithm reconstructs quotients from integer triples satisfying h²/4−ab=discriminant/4 and counts triples for a divisor-sum upper bound on the period's coefficient sum. It is classical verification/enumeration machinery. Neither that upper bound nor its proof supplies the seven large distinct values for this integral witness, a universal refutation construction, or a pre-existing negative result about A.5. The downloaded PDF has a 2021 typesetting date despite the v2 archive label; I make no finer chronology inference from its cover. Original Perron, Conway, Arnold, Hickerson and their complete specialist citing corpus were not body-read; Lerner's references are not clearance of those originals.

This is a short computationally discoverable counterexample, which limits the size of the contribution. It does not become a known result merely because Gauss iteration can verify it. The substantive content is overturning a source's quantitative conjecture in its exact integral scope, and identifying that norm collisions defeat a plausible rank extrapolation. No full-scope routine bridge from the read classical theorems to a prior refutation was found. No stronger theorem, infinite counterexample family, optimal replacement bound, or consequence for the paper's proved dispersion results is claimed. The open label and 85-state formalization are not reasons for significance PASS. The exact interior failure and the demonstrated obstruction are the reasons for qualified PASS. Root's unrelated 347913 exclusion does not decide this candidate.

## Registries, citing literature and campaign duplication

Before independent computation, live heads were read at 12:56 UTC: OpenAI/math remains `4eaee87548250b2682affda7d05d947c05554bae`; Omega is now `9abc86d1d73c7f0588782acc67b741a40b79e350`, advanced from supplied `cc684e6326490f9173bfefcadb0294ee6ccbb0b5`. Exact dated URLs, statuses and byte hashes are in http-receipts.jsonl.

OpenAI's reused complete preprints tree has SHA256 `6ac178a0ebcece8f2c2c9aa1c22022068110bbdae4bb3d1ffa9f1b693b9e0305`, Git tree `3f56f68a176b4494c346091ea0a319651bc217ec`, truncated=false, 13578 entries. My wider filename screen is in openai-path-screen.json: no target-specific continued-fraction/Lachmann/Wiart title surfaced; unrelated quadratic titles occur. This is a complete listing of that subtree, not an all-proof-body audit or all repository history.

Omega's endpoint compare reports three commits and two changed theory-document paths, about quantum reconstruction and recursive observation; the recent delta is below the 300-file compare cap. This supplies bounded recent-delta context only. It **cannot repair the incomplete baseline**: the old recursive root was truncated, Problems listing capped1000, and old300-file compares were capped. I read actual cached current-baseline proof bodies CompleteQuotientBound, CompleteQuotientRecursion and PeriodicImpliesQuadratic. Their endpoints prove discriminant invariance, quadratic-chain invariants and periodic-implies-quadratic, respectively. Their proofs do not assert the rank bound or this refutation. The delta does not change those three files. No whole-Omega or historical-deletion clearance is claimed.

OpenAlex's journal-DOI citing index returned two records (citing-index.body). Both specialist dispersion successors were read in actual arXiv bodies: Trödler–Volec–Vybíral [2311.10666v3](https://arxiv.org/pdf/2311.10666v3), Theorem1 and its complete cover-free-family proof; and [2504.00715v2](https://arxiv.org/pdf/2504.00715), Theorem2 and Sections2–3 proofs. They cite this paper for dispersion of particular sets, and prove high-dimensional lower bounds using test boxes, cover-free families and rescaling. Those proofs contain no continued-fraction rank theorem/refutation or same-object bridge. The first attempted repository copy returned404 (preserved); its actual arXiv copy was then used. This two-record index is not an exhaustive citation universe, and does not cover all citations to the separately indexed preprint. Exact-title, author/conjecture and 55/3049 web searches located no matching resolution; irrelevant characteristic2 continued-fraction certificates were not treated as clearance.

campaign-search-paths.txt and campaign-search-context.json record independent ID/title/author searches across campaign Markdown/JSON/JSONL, with context sampling limited to four matching lines per old file and 900characters per line. Located historical 352038 records are inventory/routing records marked unreviewed/not reconciled; other hits include numeric substrings and unrelated Wiart papers. The campaign ledger's accepted IDs388087/333569/347712 have different source objects. Ancestor accepted families and inherited title-history were checked; no matching credited family or specific rejection was identified. This is a bounded nonduplicate finding, not a claim that every historical text was semantically audited. All protected holds/exclusions remain effective.

## Actionable objections and handback

1. **Blocking source/version and novelty objection:** obtain a lawful readable copy of the official 2023 article or an authenticated accepted manuscript, then compare its actual AppendixA conjecture, surrounding definitions, coefficient/norm arguments, and any correction or resolution with v1. Establish whether this is still a meaningful surviving question rather than already repaired text. Retain URL/date/status/hash and exact labels. Metadata-only HTTP200 does not close this objection. Do not retry denied routes or infer a resolution from removal alone.
2. **Prior-art qualification requiring explicit root disposition:** retain the incomplete Omega baseline and incomplete preprint/journal citation coverage. A stronger clearance needs complete relevant subtree retrieval or another justified targeted body/history investigation; do not promote the old1000/300 caps to complete coverage. Read any newly located directly relevant coefficient/rank theorem in full and provide an explicit scope bridge if claiming subsumption. No discovered theorem currently justifies mathematical FAIL.
3. **Separate acceptance work:** independent formal replay, final statement-fidelity adjudication, and eventual campaign manuscript/acceptance are outside this review. No credit should be awarded from author audit logs or this qualified significance verdict alone.

The mathematical candidate survives this adversarial content review. The material published-body gap prevents overall clearance. No worldwide novelty or publication-priority claim is supported. All retained downloads and failures are evidence with qualified meaning, never proof of absence.
