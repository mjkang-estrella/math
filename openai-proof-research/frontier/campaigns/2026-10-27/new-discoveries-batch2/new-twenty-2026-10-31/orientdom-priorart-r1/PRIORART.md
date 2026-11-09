# Targeted prior-art follow-up: MathDB 360905

**Recommendation to root: KEEP HOLD.** All three items are NOT CLEARED for the precise evidentiary reasons below. No prior general proof was found, and no SUBSUMED finding is made. This is not acceptance; credit remains zero and root decides.

The full TASK.txt and orientdom-review-r1/REVIEW.md were read before investigation. The review hash is `b711a02678b2ba1458b766b9427258292f0cc9891ccde1a4bf5fbe91f41b9fcd`. This follow-up does not rerun completed comparisons. Read-only historical context pages are distinguished from new proof comparisons.

## Item 1 — NOT CLEARED

The 1996 general interpolation proof was not obtained, and no faithful open source-level description of its actual proof was obtained. It is therefore unresolved whether its proof contains a repair that transfers to total domination.

The 1999 preliminary proofs establish existence of valid orientations via strong orientations of cyclic blocks (pp. 161-162), a lower bound (pp. 162-163), and the extremal cycle characterization using Hall representatives and cycle-cover reductions (pp. 163-164). They contain no comparison of two arbitrary valid orientations, no target-directed safe flip and no blocked-flip transfer lemma. This does not establish the content of the unobtained 1996 proof. VanderJagt’s actual WMU dissertation is Local Connectivity in Graphs (April 1973); its open-access landing record was obtained but PDF access returned 403. Hansen’s author page instead identifies a 1997 thesis Domination in Digraphs, a potentially relevant distinct source, not obtained.

Outstanding evidence: An open copy of pp. 51-63 of the 1996 paper, or a reliable later primary treatment reproducing its interpolation proof, including allowed reversals and treatment of infeasible orientations.

Obtained evidence: `cached-1999`, `wmumath`, `thesispage`, `thesispdf`, `author-hansen`, `lai-publications` (exact receipts below).

## Item 2 — NOT CLEARED

Publication is confirmed, but no newly obtained allowed primary text establishes retention of Conjecture 3.1 as open in the published version. Indexed publisher excerpts are suggestive and not promoted to a primary-body check.

Johnston’s research entry 20 links to the final publisher article, not a locally hosted accepted manuscript. The St. Thomas HTTP response is only an application shell. Search-indexed St. Thomas text confirms volume 382, pp. 48-59, 31 March 2026, but its abstract does not discuss interpolation. OpenAlex labels the publisher version closed and the arXiv location submittedVersion. Neither establishes the final conjecture’s open status. No request was sent to ScienceDirect.

Outstanding evidence: A legitimately accessible final or accepted body, or an allowed author/repository statement explicitly identifying the conjecture as retained and unresolved in that version.

Obtained evidence: `author`, `stthomas`, `openalex1` (exact receipts below).

## Item 3 — NOT CLEARED

The bounded search was executed and found no new general resolving proof, but no complete citing-work list was obtained. The second and final permitted OpenAlex request returned 429; two new potential leads remained without primary bodies after access denials.

The first OpenAlex search returned 10 relevance-ranked works, not citing works. The modern paper is W4416573736 with cited_by_count 0; that index value is not proof of no citations (the already reviewed Blazsik-Nagy paper cites the preprint). The results include a June 2026 applications review, DOI 10.9734/jamcs/2026/v41i62159, whose primary publisher page returned 403. Exact-title, arXiv-ID and interpolation searches, including MathOverflow, yielded no newly identified general proof. The recent arXiv math.CO listing covers 464 entries across 28 October-4 November 2026; keyword screening found no orientable-domination or interpolation/reconfiguration lead. It includes an unrelated planar-triangulation total-domination title, not a claimed orientation-interpolation result. The complete multipartite paper remains a potentially relevant older citing work: indexed text identifies Theorem 3 as restricted to complete r-partite graphs and displays graph-specific orientation constructions; no primary PDF/body was obtained, so this is not source-level clearance.

Outstanding evidence: An accessible citing-work route with primary bodies for potentially relevant items, especially the Lai-Chiang-Lin-Yu paper if its proof machinery is to be ruled out. No exhaustive citation graph or worldwide priority search is claimed.

Obtained evidence: `openalex1`, `openalex2`, `arxivnew`, `multipartite-rg`, `survey-page`, `lai-publications` (exact receipts below).

## Mathematical distinction that remains unresolved

For ordinary domination, reversing one arc can be repaired by inserting its former head into a dominating set; every orientation remains admissible. Thus a path in the full orientation cube and a change bound of one suffice. This is an independent explanation of an available ordinary-domination proof, **not an attribution of this proof to Chartrand–VanderJagt–Yue**. Total domination requires an incoming witness even for inserted vertices, and positive indegree can prohibit a reversal. The candidate’s claimed new ingredient compares arbitrary valid D and E when every target-directed reversal is blocked: it transfers every total dominating set of D to E. None of the newly obtained sources supplies that statement. The missing 1996 proof prevents a reliable decision between a new repair and an already published adaptation. An old conjecture label alone does not decide this.

## Retrieval and reading receipts

UTC values below are acquisition times from the HTTP wrapper, except the cached PDF, whose UTC is its original download time. SHA-256 is of obtained bytes, never of an unobtained paper. A dash means no response body was saved; failure receipts themselves are preserved. HTML has no print page numbers. Every download directory was fresh and empty at acquisition.

### arxivnew

- URL: https://arxiv.org/list/math.CO/recent?skip=0&show=2000
- UTC: 2026-11-05T00:51:43.107920+00:00
- Status: 200
- SHA-256: c2769cbbd56016ffe156f5c80502a23e80d644c4d703adf35793008f9cd59bdc
- Pages read: All returned titles screened by terms orientable, total domin, interpolation and reconfiguration; matching title and date headers read. Not a primary-body review of all entries
- Receipt: `downloads/arxivnew/receipt.json`

### author

- URL: https://sites.google.com/view/danielpauljohnston/research
- UTC: 2026-11-05T00:51:05.713564+00:00
- Status: 200
- SHA-256: 1de842354c7e44d6ae1e69e5650f7a872840fc87f9c70c38ea2d16cda611ffac
- Pages read: Unpaginated HTML, research-paper entry 20 and its outgoing link; publication/link inventory
- Receipt: `downloads/author/receipt.json`

### author-hansen

- URL: https://wne.edu/directory/lisa-hansen.cfm
- UTC: 2026-11-05T00:53:00.485206+00:00
- Status: 200
- SHA-256: 828b55839dc0c22711d548de108ec02039cbf04710a7a37c841ccfcbac4d5ae5
- Pages read: Unpaginated HTML, education and scholarly works entries 3-5
- Receipt: `downloads/author-hansen/receipt.json`

### lai-publications

- URL: https://web085004.adm.ncyu.edu.tw/eRes.pub/Res.aspx?thrid=a0243
- UTC: 2026-11-05T00:52:32.749780+00:00
- Status: 200
- SHA-256: b26e009f309341ea1148d5f141bf585f2693ee7d95e360921f03aad8404569d5
- Pages read: Unpaginated HTML publication inventory; complete r-partite paper entry and bibliographic context; no attached primary body obtained
- Receipt: `downloads/lai-publications/receipt.json`

### multipartite-rg

- URL: https://www.researchgate.net/publication/228969433_Orientable_Step_Domination_of_Complete_r-Partite_Graphs
- UTC: 2026-11-05T00:52:08.850931+00:00
- Status: 403
- SHA-256: — no saved body
- Pages read: None: HTTP 403
- Error: HTTP Error 403: Forbidden
- Receipt: `downloads/multipartite-rg/receipt.json`

### openalex1

- URL: https://api.openalex.org/works?search=Orientable%20total%20domination%20in%20graphs&per-page=10
- UTC: 2026-11-05T00:50:24.902528+00:00
- Status: 200
- SHA-256: 1a8b7ada527ddccb5c9ddc8f5aa46bef1f8f19277477bc562a821b73776d459b
- Pages read: JSON metadata: all 10 returned titles; first result locations and referenced-work identifiers; no article pages
- Receipt: `downloads/openalex1/receipt.json`

### openalex2

- URL: https://api.openalex.org/works?search=orientable%20domination&per-page=200
- UTC: 2026-11-05T00:51:17.668719+00:00
- Status: 429
- SHA-256: — no saved body
- Pages read: None: HTTP 429
- Error: HTTP Error 429: Too Many Requests
- Receipt: `downloads/openalex2/receipt.json`

### stthomas

- URL: https://researchonline.stthomas.edu/esploro/outputs/journalArticle/Orientable-total-domination-in-graphs/991015375967903691
- UTC: 2026-11-05T00:51:42.915952+00:00
- Status: 200
- SHA-256: 0bf2cb7491c80152dbf68b7b7ce3193dc2bb64b75bcc7991e5ba47205e15501e
- Pages read: HTTP HTML body is an application shell, not an obtained article or substantive record text
- Receipt: `downloads/stthomas/receipt.json`

### survey-page

- URL: https://www.journaljamcs.com/index.php/JAMCS/article/view/2159
- UTC: 2026-11-05T00:53:14.242195+00:00
- Status: 403
- SHA-256: — no saved body
- Pages read: None: HTTP 403
- Error: HTTP Error 403: Forbidden
- Receipt: `downloads/survey-page/receipt.json`

### thesispage

- URL: https://scholarworks.wmich.edu/dissertations/2852/
- UTC: 2026-11-05T00:51:05.376008+00:00
- Status: 200
- SHA-256: 21d0471a62ed752f77e9cd19207dcf0b2b961ec2c86dfe31648710d03334209b
- Pages read: Unpaginated HTML, title, author, award date, access setting and PDF metadata
- Receipt: `downloads/thesispage/receipt.json`

### thesispdf

- URL: https://scholarworks.wmich.edu/cgi/viewcontent.cgi?article=3964&context=dissertations
- UTC: 2026-11-05T00:51:05.583528+00:00
- Status: 403
- SHA-256: — no saved body
- Pages read: None: HTTP 403
- Error: HTTP Error 403: Forbidden
- Receipt: `downloads/thesispdf/receipt.json`

### wmumath

- URL: https://scholarworks.wmich.edu/math_dissertations/index.2.html
- UTC: 2026-11-05T00:50:36.166843+00:00
- Status: 200
- SHA-256: 94d203f46aaf49aa087a96b3fe7640709216b55dead874cd3d20e4e315a17f41
- Pages read: Unpaginated HTML, entry for Local Connectivity in Graphs and its PDF link
- Receipt: `downloads/wmumath/receipt.json`

### cached-1999

- URL: https://combinatorialpress.com/article/jcmcc/Volume%20029/vol-029-paper%2013.pdf
- UTC: 2026-11-05T00:20:27.440505+00:00
- Status: cached original HTTP 200; no repeat download
- SHA-256: 756b125e5254a7e83196d6d6b6948a2eb6b8cc26e5890932256ae2fdac21887d
- Pages read: Printed pp. 159-164 (PDF pp. 1-6), rendered locally; substantive new comparison confined to preliminary proof machinery pp. 162-164. Pages 159-161 context only, already inspected in review. No repeat of Theorem 14 pp. 179-181.

## Search scope and limitations

The archived search results are `logs/search2.json` through `logs/search13.json`. Searches covered the 1996 exact title/authors, proof/reversal/intermediate-value terminology, WMU and author dissertation identities, later papers/surveys, published-version/accepted-manuscript routes, exact 2023 arXiv ID/title, 1999 title and citing-work leads, and MathOverflow. Search results include cached excerpts from prohibited destination hosts; those destinations were not fetched. An excerpt is not a downloaded primary source. Earlier initial search batches were inspected but not byte-archived and are not claimed as hash-bound primary evidence. No open survey chapter reproducing the 1996 proof was located; unauthenticated pirated-book mirrors were not used.

The initial OpenAlex request at 00:50:24.902528 UTC succeeded. The final request at 00:51:17.668719 UTC, approximately 53 seconds later, returned 429; no further OpenAlex request was made. It was a broader discovery query, not a completed citation-edge query. Its failure is explicitly charged to item 3. The first response’s ten results are preserved in `downloads/openalex1/body`. The intended derived screen of the second response could not run because there was no body; its empty output is not evidence.

WMU’s dissertation PDF, ResearchGate’s public multipartite page and the JAMCS review page each returned 403 once. No host was retried after denial; no alias, proxy, sign-in, TLS bypass or redirect to a denied host was used. The St. Thomas application shell and search-indexed bibliographic record do not imply possession of its article.

No new candidate general interpolation theorem emerged for primary-body inspection. The uninspected multipartite and applications-review leads are not certified harmless from their titles or snippets; the relevant limits remain charged to item 3. The 2002 date for the multipartite conference paper appears in Lai’s institutional list; ResearchGate’s indexed 2008 date is not treated as an authoritative publication chronology.

## Integrity and handback

All 357 source/review/candidate input hashes are unchanged, recorded in `inputs-before.sha256`, `inputs-after.sha256` and `logs/input-check.log`. Instruction hashes are in `instruction-hashes.sha256`. The entire review lane was hashed conservatively, but its completed comparisons were not rerun. All writes, temporary files, download bodies, logs and scripts remain inside this lane. Python ran only as isolated scripts under the two-CPU, 120-second CPU, 140-second wall and 6-GiB RSS watchdog wrapper, with local TMPDIR/cache and MALLOC_ARENA_MAX=2. PDF rendering was capped by the same wrapper. No heavy jobs overlapped. No Lean or leanchecker invocation was needed. No background job remains.

Root should preserve HOLD until the actual 1996 proof comparison and permitted published-retention evidence are obtained, and the bounded citing-work gaps are adjudicated. Absence of a discovered duplicate is not clearance.

### Search-archive hashes

- `logs/search10.json`: `83b6f8f9e1acfc48707914b0bdfb080df31328ab797f6e53ba10e2bdeafde783`; archived 2026-11-05T00:52:32.642637+00:00.
- `logs/search11.json`: `9312f99fc374782259e766f1e7d79bc869d3ac4b85f4f15489283ea598d5f897`; archived 2026-11-05T00:53:14.636781+00:00.
- `logs/search12.json`: `5fdd370410b1c7a5fe4687c11de8ec3cb3203b873012efa07b7a12a98efac785`; archived 2026-11-05T00:53:14.640781+00:00.
- `logs/search13.json`: `a1d9115afa217f6190a18e4e2c0acdd488a666bc9934403f817bbc43799f8655`; archived 2026-11-05T00:53:48.783898+00:00.
- `logs/search2.json`: `3cf9b1d1f8fbdd00222641495b7392a5c90c5b55a6ebb46555dd63fca535740b`; archived 2026-11-05T00:50:09.915148+00:00.
- `logs/search3.json`: `9f45b0588132ba959d3ece30fe56e307b92831a0102b7fa4e23f14f341f5cf14`; archived 2026-11-05T00:52:32.590637+00:00.
- `logs/search4.json`: `896b81ceb7015d2df383f48f2072e68e91895b4bbfcfad81bf404d197ab334a3`; archived 2026-11-05T00:52:32.600637+00:00.
- `logs/search5.json`: `8a96dabd11515454c2861d0bf251323941fa5daf5afaac80959756c21dcb1d0a`; archived 2026-11-05T00:52:32.607637+00:00.
- `logs/search6.json`: `f632017467edd23b6e45c0466288605514cf8775280ecdc012db564bc4235466`; archived 2026-11-05T00:52:32.617637+00:00.
- `logs/search7.json`: `a9db698ba3f8c187212355a945c193b8c6e3ed0fe693f7b0e320d1318cc17348`; archived 2026-11-05T00:52:32.623637+00:00.
- `logs/search8.json`: `0f3c6f392b01901b14e867d1ce4f2ba4a9fce57d2b580894575d56fb12306e34`; archived 2026-11-05T00:52:32.632637+00:00.
- `logs/search9.json`: `2d2c3a7319b22836afe1f9ff8bdadb4fb69745a941d6a4ab5073ae215ee84f41`; archived 2026-11-05T00:52:32.637637+00:00.
