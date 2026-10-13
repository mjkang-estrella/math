# I316 — reading extents, limitations, and failures

2026-10-13. This is a new independent quantitative correctness round. Frozen-proof verdict: **FAIL**, because section 3 line 96 asserts a strict inequality that is false when epsilon=0. Q315 itself is independently verified with the same scope and constants. The authenticated frozen I315 input matches the exact dispatch digest. Completed I312 evidence also matches both dispatch digests. No I313 or I314 body was read.

## Local semantic reads

- `AGENTS.md` and `sources/upstream.json`: complete. Root and relevant frontier ancestor rules were checked; no additional AGENTS file was found on the output paths.
- Frozen `frontier/iterations/i315-quantitative-amplification-gap.md`: complete, all five proof sections, proposed theorem, and contribution/validation boundary. No section was omitted from the independent audit.
- Completed `frontier/iterations/i312-amplification-hierarchy.md` and `frontier/experiments/i312_amplification_hierarchy/analysis.md`: complete, separately recovered in an untruncated call. These are context, not premises validating Q315.
- `frontier/iterations/i312-parent-amplification-construction.md` and `frontier/iterations/i312-parent-rank-defect-obstruction.md`: complete, original construction and warning only.
- `frontier/experiments/i312_amplification_hierarchy/input-authentication.json`: complete, used to identify earlier context/source reads, not to inherit their proof validation or raw-fetch claims. `reading-and-failures.md`: targeted matches concerning old rank-defect context and read limitations only.
- `sources/CONTENTS.md`: targeted result 325 and the two companion entries, explicitly recovered at lines 7920–7954; targeted search also located them. No full catalogue semantic read is claimed.
- `sources/preprints-tree.json`: parsed as a path listing only for the two Crouzeix source manuscripts; no other manuscript content read. `sources/tree.json` was not used.

The initial broad filename inventory exposed path names, including live sibling path names, but read no sibling body. A first concatenation containing the large catalogue exceeded the output limit. This did not count as a complete read of the catalogue or obscured context. The required I312 documents were read again separately in an untruncated call. Both events are recorded rather than silently treated as full reads.

## Primary-source reads

Two pinned TeX responses were fetched with Python urllib into memory, hashed as raw bytes, and only selected lines were displayed. Direct manuscript: lines 30–95, including base-first evaluation and `thm:main`. Structural companion: lines 299–350 and 380–431, including `eq:optimal-similarity`, `prop:density`, `prop:extremal`, and initial proof context. Neither complete source body nor selected full section was written into the repository. All upstream truth is stipulated. Neither manuscript supplies the new gap argument as a dependency.

Gau–Wu (2009) was opened through web extraction for discovery and markers, then independently fetched as raw PDF bytes in memory and hashed. Poppler `pdftotext` through stdin/stdout displayed PDF pages 3–5 (printed pages 2184–2186): Theorem 5 statement and complete proof, Theorem 8 statement and beginning of its necessity proof, with intervening local context. The remainder of the necessity proof and references were not read in this round and are not dependencies. The PDF was not retained and no page-image inspection was needed for this text-level model attribution. No priority or full literature search is claimed.

## Validation and operational limits

Independent validation was exact symbolic reasoning, recorded in the analysis for every integer r>=2 and every integer 1<=d<r and every admissible matrix Schur function. It was not a numerical scan or finite test substituted for the quantified proof. File checks verified authentication, output completeness, and the exact parent digest again after writing. The only retrieval/read failure was oversized initial output truncation, resolved by bounded targeted reads. A final full output reread caught an erroneous draft characterization of the parent as using only a weak comparison; the draft and verdict were corrected before finalization. A first local link check used an overly broad regex and misclassified mathematical `Q[C](...)` notation as a Markdown link; the checker was restricted to actual path-like link targets and rerun. No network retrieval failure occurred.

Actual necessary repair: replace section 3 line 96's final `<5epsilon` by `<=5epsilon`, or qualify its strict version by epsilon>0. The level-r witness is an exact endpoint counterexample to the frozen strict assertion. The parent remains unedited. Distinct explanatory expansions: explicit basis, radial compression, explicit loss spectra, D-based quadratic defect, exact constants before rounding, sign-safe rank inequality, and irreducibility pairing. No compactness modulus or weaker gap is used. No child agents, live sibling reads, git, shared-index changes, publication, acceptance change, or full external-body retention occurred. The final output hashes are detached to avoid self-reference.
