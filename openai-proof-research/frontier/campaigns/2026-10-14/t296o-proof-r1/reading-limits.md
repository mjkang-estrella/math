# T296O proof review r1: reading, provenance and verification limits

Reviewer: independent proof-correctness sub-agent, with no nested agents, no shared-index changes, no staging, no commits, no uploads and no publication. Writes were confined to this directory. Scratch work was done in /var/tmp/t296o-proof-r1-scratch. No third-party bodies were copied here.

## Read in full

- From the frozen packet (anchors verified first): candidate.md, scope-freeze.md, comparison.md, reading-limits.md, checkpoint.md, verify.py, diagnostics.py.
- Canonical source copies from the packet (blob identity verified against the complete tree): sections/independence.tex, sections/perturbation.tex, sections/generation.tex.

## Read in part

- sections/introduction.tex, lines 1–135 (it contains thm:relative-generation and thm:main).
- sections/consequences.tex: only a keyword scan for norm, orbit, conjugation and spectrum statements, plus the theorem headers. No orbit or operator-norm result was found there. This scan is not a full reading.
- MANIFEST.json, source-receipts.json and primary-receipts.json: parsed by the verifier, with partial terminal display.
- Campaign helper t314c-proof-r1/review_check.py, lines 1–172 and 519–564. I adapted its structure, as recorded in the docstring of review_check.py.

## Not read

- The primary bodies (Ma–Shi–Yang 2604.21482v2, Shi 1911.07696v2, DSSW 0706.1953v2). The candidate proof imports nothing from them, and comparison is a contribution question outside this role. Their receipt hashes were verified only.
- main.tex, preamble.tex, README.md and references.bib. The canonical PDF.
- Popa's and Haagerup's original papers. These are stipulated or classical as used by the source.
- The parallel T296O review directory. I did not open or infer it. The only other campaign directories I opened were the t314c helper and directory listings.

## Verification limits

- The integrity checks (author identity, 16 author-packet controls, and the review self-controls reported externally after sealing) certify bytes and provenance only.
- The finite diagnostics are exact identities on small instances in L(K*F). They do not test ultrapowers, clipping, Baire genericity or any infinite-dimensional statement. They certify no theorem.
- The proof verdict rests on the written re-derivation in review.md.
- No formal or manuscript gate was run.
