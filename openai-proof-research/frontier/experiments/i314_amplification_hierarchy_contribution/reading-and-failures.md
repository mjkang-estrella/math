# I314 — reading, authentication, and limits

2026-10-13. Independent contribution review of the single all-r I312 nomination. The requested model is GPT-6.1 Sol, high reasoning, Standard service. The runtime identifies GPT-6.1 Sol/high; a service-tier verification API was not used. No subagents were started.

## Authorized local reads

All work used `/home/mj-kang/Documents/Dev/math/openai-proof-research` as its working directory. Read root AGENTS.md and sources/upstream.json. The upstream pin exactly matches the requested revision. The manuscript catalogue was initially requested too broadly and the tool truncated its output; that retrieval is **not** claimed as a full catalogue read. A focused read of catalogue entry 325 and a path-only inspection of preprints-tree.json supplied the two actual pinned manuscript paths. No frontier shared index was read or edited.

Read the entire 102-line frozen `frontier/iterations/i312-parent-amplification-construction.md`; its SHA256 matches `da83fdf48779e56c2c8c694973282ecf61ea14c1134e86b9f48bfed12cc89070`. This is the specifically authorized parent proof, not the separate live I312 reviewer's work.

Read R019 in full, the completed I292 review and parent disposition in full, and all 167 lines of the completed I292 analysis. An initial guessed directory name was inspected by filename lookup; no live sibling bodies were opened. A broad filename-only inventory at the start was noisy; all subsequent body reads were restricted to authorized paths or the required catalogue.

I309 was not read while prohibited. After the user's supplemental message expressly authorized its completed review and analysis, both were read in full. Their supplied SHA256 values match:

    review:  9b7ee330d72e71db4791693b82be69d1f86a7e4a904060faae77c2e70672eabf
    analysis:d273cbf1800cbc28f6bb5649d6bbb7e6191bf62565e5b4e16acc0a044220e0af

The combined local/external tool output was sometimes truncated at the orchestration layer. The final 45 lines of I309's analysis were consequently reread separately. The earlier combined external output was also repaired by separate complete Gau–Wu and DPW calls. No read-completeness claim rests on the truncated combined output alone.

The user's updated administrative facts are recorded as fourteen accepted and R020 accepted; older local counts in the completed reviews are not copied into a present-count assertion. No acceptance, count or integration file was edited.

## Primary-source reads

Gau–Wu: web extraction lines 0–829 across overlapping calls, covering all ten pages, the full scalar construction and necessity proofs, statements, and references. A fresh in-memory raw download produced SHA256 `aaebae81c7cc045f3778cea0a975ab0ecb517ac5e9acb0313e9381859c158ba3`. The raw bytes were discarded. This reviewer did not compute ten page hashes or inspect ten rendered page images; the parent's supplemental assertion about matching page hashes is not represented as this reviewer's own action.

DPW: entire eight-page preprint, lines 0–535, including the exact n-to-2n converse operation. In-memory raw SHA256 `ef6c7c29bc28cc0e3231887ffb2082918c7a6c200d82cdb9c795f94828d4ac24`; discarded.

Benhida–Fricain–Timotin: actual matrix model formulas and Lemma 2.2, plus all the Section 3 reducibility statements/proofs, through Remark 3.5. Relevant range 175–435, with surrounding definitions also inspected. In-memory raw SHA256 `18f611b16a5c04984d6dfb3632ca645bf63c6643f8125d7c90cfd4840614dec2`; discarded. Later truncated-Toeplitz applications are not claimed read.

Knese v2: actual realization Theorems 2.1 and 3.1 with proofs, Proposition 2.2 with proof; selected adjoining remarks. ACV v3: complete Section 5 and the dimension-three equality proof. He–Spitkovsky–Suleiman: only introduction and early extreme-rank statements, lines 0–163. Exact URLs and interpretation limits appear in literature.md. Web line numbers are extraction coordinates, not page-image certification.

Pinned OpenAI source TeX was fetched directly from immutable raw GitHub URLs in memory. Read direct `thm:main`; structural `thm:structural`, `thm:representation`; and all of `prop:extremal` with proof. Full raw hashes authenticate retrievals, while only the recorded passages are claimed read. Bodies were not saved. Stipulated theorem truth was not audited.

## Searches and failures

Bounded searches tested matrix-valued extensions of Gau–Wu, matrix-inner reducibility, nilpotent partial isometries, disk-algebra k-contractivity, and polynomial/complete norm differences. Several multiquery searches returned irrelevant multivariable, noncommutative or numerical-linear-algebra hits. These were not treated as mathematical evidence. The decision comes from an explicit reduction, not absence of a matching title.

Holbrook publisher full page: raw web error `Failed to fetch https://www.sciencedirect.com/science/article/pii/0024379593003509: (403) Forbidden`. Only publisher abstract/search metadata was available; no unseen proof was ruled out.

Davidson–Katsoulis optional dilation lead: ETH mirror returned `Internal Error`. Kyoto mirror initially reported a cached 88-page/5162-line PDF, but `find` failed to match the requested text. Focused `open` returned `Failed to fetch https://www.kurims.kyoto-u.ac.jp/EMIS/journals/DMJDMV/vol-16/28.pdf: (403) Forbidden`; fresh terminal retrieval returned `HTTP Error 403: Forbidden`. This is not a successful reading of Example 3.3 or the full paper. The analysis instead gives the elementary one-generator argument directly.

The original LSS paper was not requested afresh. Its inaccessibility in I292 is reported as that completed review's limit. I do not assert that its unread contents cannot contain a useful construction. No additional inaccessible source is necessary for the explicit weighted-model/reducibility reduction used here.

## Operational limits and deliverables

No git command, numerical scan, external publication, communication to another person, subagent delegation, live sibling read or shared-index edit was performed. No new full external body or section was retained. Shell/in-memory retrievals wrote no PDFs or scratch source bodies. Only the five assigned authored files were created. Authentication records distinguish complete local reads, selected catalogue/source reads, whole-byte hashes, and unavailable source bodies. Final authored-file hashes are detached to avoid self-referential metadata.
