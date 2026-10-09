# Weighted capacity for four-state reconstruction with variable edge channels

Myeongjin Kang, Independent researcher.

Standalone English manuscript for R009 and its locally finite extension, prepared on 2026-10-09. The PDF has nine pages. This paper is separate from the prime-predecessor manuscript.

- [PDF](output/pdf/variable-channel-capacity.pdf)
- [LaTeX source ZIP](output/variable-channel-capacity-arxiv-source.zip)
- [Main source](main.tex)
- [Announcement draft](ANNOUNCEMENT.md)
- [Proof and source review](evidence/publication-review.md)

The main theorem is conditional on Assumption 2.1: the preserved posterior-law class and binary moment-saving inequality asserted in the cited pinned OpenAI manuscripts. All subsequent arguments, including the uniform local estimates, quantitative bounds, zero-edge pruning, and boundary examples, are included in the paper. The numerical constants are not claimed to be optimal.

Status: drafted, compiled, visually inspected, and packaged locally. No external submission or public record has been created for this paper. There is no DOI or arXiv identifier. Internal AI reviews and exact finite algebra checks are not human peer review or formal proof certification. The bounded literature review does not establish worldwide priority.

## Build

The manuscript uses standard AMS LaTeX packages and has an inline bibliography. It requires no figures, external data, shell escape, or bibliography processor. From this directory:

```sh
mkdir -p tmp/pdfs
tectonic --keep-logs --outdir tmp/pdfs main.tex
cp tmp/pdfs/main.pdf output/pdf/variable-channel-capacity.pdf
```

Alternatively, compile `main.tex` twice with pdfLaTeX. The delivered builds were checked with Tectonic 0.17.0; pdfLaTeX and the remote arXiv processing service have not been tested here. The ZIP contains only `main.tex`, `references.tex`, and the five section files, with relative paths preserved. It was extracted into an empty directory and rebuilt successfully.

Run the supplementary exact checks with `python3 evidence/validate.py`. Their recorded result is [validation-results.json](evidence/validation-results.json). They check selected finite identities and inequalities; the universal argument is the manuscript proof.

The source dependency is fixed at `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. [upstream-manifest.json](evidence/upstream-manifest.json) records retrieval URLs, SHA-256 hashes, Git blob identities, and local cache paths. The upstream source files are excluded from the submission ZIP.
