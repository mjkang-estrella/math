# I278 reading, restrictions and failures

2026-10-12. First independent CONTRIBUTION review of I275. No independent I275 proof verdict was assumed or issued. No subagents, live sibling-content reads, shared edits, staging, commits, publishing, research programs/tests/numerical scans, snapshots, broad history replay or communications to others were used. Only assigned I278 records and the limited fully read primary excerpts were written. Shell/Python utilities performed text extraction, retrieval, hashing and record serialization only; they did not compute research evidence. Raw retrieval bytes remained in memory and no temporary PDFs/images were saved.

## Local reads

- AGENTS.md and sources/upstream.json: complete. Pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb stipulated true.
- sources/CONTENTS.md: family-354 catalogue window, lines approximately 8605–8619. An initial larger output was truncated; only this window is claimed read.
- I275: all 141 lines, plus its complete input-authentication.json; required target hash matched directly.
- I274: all 81 lines. I276: all 15 lines and its complete literature.md.
- R017: complete 97-line accepted theorem record. I269: complete 38-line review and complete analysis; the small truncated common-flow paragraph was recovered by rereading analysis lines 65–95.
- I270: complete 70-line review, complete 95-line analysis and complete literature.md. The literature opening and ending were reread to repair combined-output truncation. These are completed records explicitly authorized for overlap, not live sibling reads.
- I269 retained 354-paper.tex: actual theorem lines 54–84, not the whole entry manuscript or included proofs. Complete retained AFM page-7 and page-22 primary extracts were read.
- I270 retained 354-nesting.tex: complete 574-line primary section. Complete ABLW v4 Section 4.4 primary excerpt, 383 lines, read.
- I269/I270 authentication JSONs were incidentally requested together and the combined output was truncated. Only the visible metadata windows were inspected; complete manifest reading is **not** claimed and no new source-read assertion is borrowed from them.
- I277 and I273: not opened, searched for content, or used.

The pinned raw family-354 paper.tex was additionally streamed and hashed: `ab75095f542adf4073a41a26a3c3ae97be7b55fa19674ec4fb4c288f7145a813`, identical to the retained file and I275's source identifier. This authenticates bytes; it is not an upstream truth audit or a full-manuscript read.

## Independent primary reading

Exact URLs, PDF hashes, extraction ranges and mathematical scope are in literature.md and input-authentication.json. Lacasse–Grest–Levine Section III through equation (34), Lv Sections 4.2–4.3 and Appendix B.2, and Ginot Sections 2.1–2.3 were read directly. Ginot's combined pages 1–5 output truncated part of page 3; that page was reread in full. Saitoh's English abstract and Section 2.1 were read, with page 2 reread to recover its contact-model block. The article is labeled a review; it is used only for its own current presented model scope. Incidental unread/partially inspected neighboring sections are disclosed separately.

The PDF skill was applied for read-only extraction. No PDF authoring workflow or rendering was invoked. The user's no-snapshot constraint took precedence over the skill's preference for page images. This limits visual/layout verification, not the explicit read extents.

## Search scope

Bounded manual web batches searched both exact paper titles and possible duplicate/standard routes. Representative exact queries:

    Morse Witten 1993 Droplet Elasticity Weakly Compressed Emulsions pdf
    Hohler Weaire 2019 Surface elasticity of liquid foams revisited Morse Witten pdf
    droplet contact logarithmic deformation two droplets rigorous asymptotic perimeter minimization capacity
    "Droplet elasticity" "Witten" pdf morse.umn.edu
    "droplet" "contact" "perimeter" "logarithmic" asymptotic minimum
    "Droplet Elasticity" "witten" site:uchicago.edu
    "Can liquid foams and emulsions" site:hal.science
    "Morse" "Witten" "droplet" site:umn.edu
    "Juggling bubbles in square capillaries" arxiv
    "Morse-Witten" "2025" three dimensional
    "Morse-Witten" "2024" contact
    "Can liquid foams and emulsions" site:tara.tcd.ie
    "Many-body interactions in soft jammed materials" arxiv
    "sharp" "logarithmic" "droplet" "perimeter" minimizers
    "ball" "slab" "nested" "perimeter" torus
    "nested" "isoperimetric" "contact" logarithmic

Further title/DOI searches located publisher records and author metadata. Search hits on liquid dynamics, drop impact, unrelated Morse theory, patents, repositories, and nonprimary summaries were navigation only or discarded. A recent Saitoh article was actually read at its model statement, rather than relying on the search result. No exhaustive bibliography or global novelty inference is made.

## Access failures and unrepaired read limits

1. Web opens of Morse–Witten DOI/PDF returned Internal Error and finally robots.txt denial. Terminal retrieval of the PDF endpoint reported HTTP 200/application-pdf, but Poppler found HTML and no PDF trailer. The apparent successful type was misleading; the paper calculation was not read. Original publisher abstract was accessible in search and was read.
2. Höhler–Weaire ScienceDirect full and abstract URLs returned Internal Error/403. Accessible publisher snippets and original abstract/highlights were read. HAL page returned an anti-bot page. HAL's public metadata API found hal-03390528 and its external ISTEX link. ISTEX PDF and text endpoints returned an institutional-selection HTML page. No authentication was attempted; full Section 2 and the full paper remain unread.
3. ISTEX metadata independently located Morse–Witten, but its text endpoint likewise returned institutional-selection HTML. Metadata access is not full-text access.
4. Höhler–Cohen-Addad correct RSC full-text URL returned explicit 403; its original abstract was accessible via search. One preliminary RSC URL had the wrong article code and failed; it was corrected to C6SM01567K and no content from the wrong code was used.
5. Several combined local/source outputs were truncated. Required candidate, hypothesis, predecessor mechanism and actual source sections were reread at the disclosed missing extents. Complete reading of the truncated predecessor authentication JSONs was unnecessary and is not claimed.
6. Saitoh extraction warned Invalid Font Weight and the initial three-page output lost a short introductory block. Complete Section 2.1 was recovered by the page-2 reread; the damaged introductory characters do not support any conclusion. No whole-paper or complete later-section reading is claimed.
7. An authentication utility's JSON output was initially capped too tightly and could not be parsed. It was rerun with an adequate output budget before creating the manifest. This affected no mathematical reading or research computation.

## Boundary of the conclusion

The substantiality verdict concerns the nonroutine singular lower passage remaining after R017, not the logarithmic law or sharing. Full original Morse–Witten/Höhler–Weaire arguments and general second-order contact/shape-sensitivity theories remain outside the available read scope. They could change priority or reveal a standard theorem. Their absence neither establishes novelty nor forces a known/technical classification without an identified corollary route.

Runtime instructions identify gpt-6.1-sol with high effort. Standard tier was requested by the task; no independent billing/service-tier attestation was obtained. No model switch or delegation occurred.
