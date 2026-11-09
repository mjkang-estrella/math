# I342 reading record, limitations and preserved failures

2026-10-13. GPT-6.1 Sol (`gpt-6.1-sol`), high reasoning. Standard speed was requested in the brief; speed is not independently exposed by this harness. No subagents, git operations, publication, numerical scans, shared-index changes or frozen-candidate edits. Only the five assigned files were written.

## Local reads and authentication

Read the complete assigned brief, project AGENTS.md, sources/upstream.json, the FULL frozen I341 candidate, and the complete I341 literature file. Candidate SHA256 matched the required `1e66ba9bc7c98ced6deb292c960e9e5eb731b24aefd0e0884e5647d718078e91` before audit and is checked again at finalization. Read the complete parent postselection supporting note only after the user explicitly directed this read. It is distinguished and hashed as a supplemental input, not silently substituted for I341.

The initial full `cat sources/CONTENTS.md` output was truncated and is not claimed a full catalogue read. Subsequent scoped rg reads established the complete result-272 entry at lines 6865–6874 and all catalogue matches for PPT, secret key and entanglement breaking. The complete preprint-tree JSON was parsed in memory and paths matching zero-distillable/PPT-square were printed; bodies of unrelated manuscripts were not read. Catalogue result 272 lists one manuscript, with the companion state, pair, channel and projection mechanisms inside it. This is not an exhaustive search of every mathematical paper under every possible synonym.

No additional AGENTS.md existed at the checked frontier, reviews, experiments, sources or assigned-output-directory ancestor paths. All commands after the initial inventory used the project root as workdir.

## Pinned manuscript read scopes

All source retrievals used raw GitHub URLs at commit `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Source bodies existed only in transient memory/tool output and were not saved as new files.

- `build/source/sections/foundations.tex`: complete 238 lines, including `lem:ppt-stability`, `def:represented-class`, `lem:tensor-closure`, `lem:choi-transfer`, their exact dimensions and normalization. Independent new-use algebra was checked; upstream theorem truth was stipulated.
- `build/source/sections/applications.tex`: complete 155 lines, including `prop:channel-completion` and the source square's non-EB consequence.
- `build/source/sections/secret-key.tex`: controlled reads of lines 1–141 and 230–379. Exact `def:distillable-key`, complete `thm:zero-key` statement, first-bit argument and complete `prop:operational-extensions` statement/proof were read. Lines 142–229 of its proof were not independently audited; an earlier oversized retrieval is not counted as that audit.
- `build/source/sections/transcripts.tex`: lines 1–65 and controlled reread 77–220, covering the finite-record mechanism and the FULL `def:protocol` at 77–196. The long measurable-transcript proof and later parts were not audited.
- `build/source/sections/introduction.tex`: large initial output was truncated. Confirmed read scopes include controlled lines 1–68 and the visible theorem/application/background passages through the organization discussion; only the operative labels `thm:main-state`, `thm:main-channel` and the source's machinery/companion discussion were used. No claim of a complete independent proof read of the manuscript or its geometric/arithmetic construction is made.
- `build/source/main.tex`: complete 74 lines for author/title/date and included manuscript structure.
- `build/source/references.tex`: keyword excerpts and controlled lines 105–113 for the CMHW source/version credit, not a full bibliography read.

Full-body hashes of the fetched objects authenticate retrieval identity, not breadth of reading. These scopes and byte counts are machine-recorded in input-authentication.json.

## External primary read scopes

CMHW, arXiv:1807.01266v2: actual Lemma I.1(2), Section IV.A/IV.1, FULL Section IV.B/IV.2 at web lines 492–508 and nearby mapping-cone theorem statements. The HTML renders lettered subsection locators numerically. This checks the local-product equivalence and rectangular transpose-adjoint machinery, without crediting CMHW for a key-capacity theorem.

Wang–Wilde, arXiv:1905.11629v3: FULL Appendix A.2 Choi isomorphism, obtained by transient raw HTML extraction after web find failed. Equations (69)–(70) are the displayed contraction; the journal/PDF convention is often cited as (A15). Resource-theory body and general transformation theorems were not used. The correct paper is *Resource theory of asymmetric distinguishability*, Phys. Rev. Research 1, 033170, not the companion channel-box paper 033169.

Kaur–Wilde, arXiv:1707.07721v3: Definition 1; Section 2.5 including Proposition 8 and its proof; Section 3.1 and purification excerpts in 3.2; Section 3.4; Proposition 13 statement and nearby proof excerpts. This supplies comparison scope, not an asserted zero entanglement upper bound or deterministic C-resource simulation.

Bäuml–Christandl–Horodecki–Winter, arXiv:1402.5927v2: Results section's resource model and equations (11)–(13), including Charlie's untrusted role and PPT bounds. Some supplementary examples were returned by broad find but are not relied on. No full supplementary theorem proof read is claimed. The rate model is distinguished from the present inaccessible serial composites.

These primary bodies were not saved locally. The retrieval HTML digests are recorded; they identify the observed rendering, not an immutable publisher revision. Generated HTML display dates are not treated as publication dates. Searches supplied leads only; no secondary-site result is used as mathematical authority.

## Preserved failures and corrected approaches

1. **Scope deviation:** the first filesystem commands ran from the containing math directory to read the assigned brief, and an initial `rg --files -g AGENTS.md` inventory ranged over `/home/mj-kang/Documents/Dev`. This exceeded the brief's project-root/project-only filename-search boundary. It returned filenames in other projects but no other-project body was opened and no outside write occurred. The deviation is preserved rather than reported as perfect scope compliance. Subsequent filesystem commands were rooted in openai-proof-research.
2. Full catalogue and combined source/web outputs exceeded output budgets. No hidden/truncated passage is represented as a completed read. Targeted catalogue searches and narrower source reads repaired the operative theorem-interface coverage.
3. An inventory of not-yet-existing output directories returned missing-path errors and exit 2; the final output paths were later checked individually and created only as needed.
4. Nature's repeater URL first redirected through a cookies-not-supported URL, then returned `Internal Error ()` on repeated open. The primary arXiv HTML was used instead.
5. Broad searches returned irrelevant/secondary material. Missing keyword matches and failed theorem-number finds were not treated as absence or novelty evidence.
6. APS paper 033169 was an initial postselection lead, but the exact appendix belongs to the companion 033170 / arXiv:1905.11629. This credit was corrected. APS find reported `No matching text found for "postselected teleportation"`; arXiv find later returned `Internal Error ()`. Direct in-memory extraction read the actual appendix.
7. A raw-HTML parser attempt failed with `ModuleNotFoundError: No module named 'bs4'`. No package was installed and no extra file written. Standard-library extraction recovered the full relevant subsection.
8. **Rejected mathematical shortcut:** whole-run conditioning on Bell success was not assumed transcript preserving. The weights w_r depend on adaptive dimensions; equalization or branchwise closure is necessary. This failure belongs to the naive reduction, not frozen I341.
9. **Rejected information shortcut:** a simulated gap with extra Eve registers was not pushed through their discard. An explicit Eve-only comparison-lifting channel appends the unused-resource states conditionally on r and proves the valid inequality in the required direction.

The final mathematical validation is symbolic and analytic. It includes reshuffling indices, Bell normalization, actual environment contraction, both public-weight repairs, source operational compatibility, first-bit/capacity implications and retained-information limits. No upstream truth audit, numerical scan, deterministic teleportation claim, infinite-memory result or exhaustive priority certification was undertaken.
