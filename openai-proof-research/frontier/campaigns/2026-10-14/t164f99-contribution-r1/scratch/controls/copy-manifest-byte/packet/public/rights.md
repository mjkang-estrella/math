# Rights separation, T164F99 contribution r1

- `packet/public/` is original reviewer prose and code (review.md,
  reading-limits.md, rights.md, inputs.json, search-log.json, verify.py,
  controls.py, seal.py). Provenance: Factory Droid / claude-opus-5-5 / high,
  2026-10-20, written for the r99 contribution review.
- `packet/private/` retains third-party and project-internal bodies under their
  original rights, copied verbatim for audit only:
  - `private/primary/`: arXiv PDFs, pdftotext extractions and arXiv abstract
    pages (Alweiss x2, Hunter, Bowen-Sabok, Bergelson-Leibman, Kousek, Moreira,
    Bergelson-Moreira x2). Rights remain with the authors/publishers.
  - `private/source/`: pinned OpenAI math repository files at
    fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb (family 164), fetched from
    raw.githubusercontent.com, blob-hash verified. Rights per upstream.
  - `private/history/`: copies of immutable prior-round project files
    (r1, r35, r94, r130, r99-parent) retained for audit.
  - `private/context/`: copies of AGENTS.md, the common research brief, the
    role brief and sources/upstream.json, bound explicitly so the review does
    not depend on the live ledger.
  - `private/author/`: verbatim copies of the immutable r99 author packet
    public documents and detached anchor files (FINAL.json, MANIFEST.json,
    REPORT.md) used as review inputs.
  - `private/search/`: raw API/search responses (arXiv Atom XML, OpenAlex and
    Semantic Scholar JSON). Rights per the respective services.
No third-party text is reproduced in the public files beyond short quoted
fragments for attribution and comparison.
