# I241 — reading, route changes, and limits

## Scope and early record

Work stayed inside /home/mj-kang/Documents/Dev/math/openai-proof-research. AGENTS.md and sources/upstream.json were read first. Initial notes were written to the assigned analytic and iteration files before the solution route was established.

The complete finalized I236 proof was read, and its supplied SHA-256 was verified. The full original I230 and earlier I224/review material supplied in the task prompt were treated as context. The filesystem copy of the I230 literature map and authentication map was used only to locate completed sources. The I236 literature map was also used as a source locator. No I238 or I240 contents were opened. A preliminary filename-only inventory included their names; no content or live findings were consumed.

## Successful route

The first idea was a second transverse blowup. Direct compactness failed because the given fixed-box fits do not bound the wider boxes uniformly. The crucial refinement is to make the larger radius depend on tau, preserve its larger fitting parameter, and seek small oscillation only after dividing by the natural epsilon-scaled amplitude.

The running maximum can be strengthened to give s/lambda^N ->0 for every fixed N. It therefore pays the domain cost of radius tau². At that radius its parameter is kappa lambda with kappa/tau ->0. Same-center comparisons keep the coarse slope nonzero. An inscribed epsilon-ellipsoid has normalized oscillation O(sqrt(kappa/tau)), so the actual p-equation enters Savin's local uniformly elliptic small-jet regime. The resulting Hessian estimate improves the original supposedly bad fit. All steps and quantifiers are in analytic-attempt.md.

The final argument uses no unproved gradient modulus of the p-functions, no REG_tau, and no uniform-in-tau conclusion from I236.

## Failed independent route

Exact p-energy was examined separately. Its local normalized density has the exponential limit on bounded first jets, but neither that expansion nor the weighted excess identity bounds the actual flux mass before derivatives are controlled. There is no independent energy-only closure here. The successful PDE route supplies the needed derivatives first.

The naive limit Delta_x V=0 still admits sin(t) with exact inherited fits. A fixed-box actual-p argument also cannot force longitudinal affinity: the explicit radial family in analytic-attempt.md has a nonaffine temporal blowup. Its domain ends before the selected growing radius; it is not a counterexample to the new theorem or to gradient convergence.

## What remains unpaid

No proof is supplied that every sequence u_p converging uniformly to an infinity-harmonic v with inf|Dv|>0 has the source's uniform qualitative cylinder flatness and nonzero fitted slopes at all selected microscopic radii. The source obtains those using its exact infinity equation and an affine lift that is invalid for p-harmonic functions. The high-viscosity exclusion is now an actual-p theorem under explicit selection hypotheses, but those hypotheses must not be relabeled as consequences of mere value convergence.

The elementary fixed-ball consequence when affine value error is O(1/p) is proved as a restricted application and identified as a standard transfer. Available general value rates do not satisfy that smallness requirement. It is not offered as the tenth finding.

## Primary reading and retrieval

- Savin: author-hosted PDF retrieved successfully; PDF pages 1–4 and 14–18 extracted and fully read. The complete PDF was hashed and removed; unread pages are not retained.
- Julin–Juutinen: existing primary excerpt, PDF pages 1–6, fully read.
- Sobral–Teixeira–Urbano: existing primary excerpt, PDF pages 1–4, fully read.
- Bungert: existing text, lines 1–210, read; no later argument attributed to this read.
- Pinned introduction and reduction: complete sections read; the reduction was displayed in overlapping bounded sections. Relevant local Git blob hashes matched the immutable catalogue.
- Catalogue: only family-377 summary and same-family path lookup used.

Web searches sought p-uniform gradient regularity and small-perturbation results. Search snippets and aggregators were discovery aids only. The substantive new input was checked in Savin's actual author-hosted paper. No bibliography-wide novelty claim follows from these searches. PDF extraction drops some Greek glyphs; no numerical constant depends on reconstructing those missing glyphs.

## Constraints

No subordinate agents, live sibling outputs, shared edits, staging, commits, publication, research code, tests, numerical experiments, parameter scans, workspace snapshots or seals were used. Computation was limited to ordinary retrieval, source extraction/local lookup and provenance hashes. Only the specifically assigned outputs and fully read primary excerpts under the assigned source directory were written. The transient downloaded source PDF was removed after extraction and hashing.

No acceptance change. Independent proof and contribution gates are not supplied by this research note.
