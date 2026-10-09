# Prime-predecessor publication package

Author: **Myeongjin Kang**, **Independent researcher**. No coauthors supplied.

Status: an English manuscript prepared for external review. It is conditional on the exact analytic inputs listed in Assumption 1.1 and Appendix A. Nothing has been submitted, posted, pushed, or sent to a reviewer.

## Deliverables

- [Manuscript PDF](output/pdf/prime-predecessor-residues.pdf)
- [arXiv source ZIP](output/prime-predecessor-arxiv-source.zip)
- [LaTeX entry point](main.tex)
- [Submission metadata draft](arxiv-metadata.txt)
- [MathDB announcement draft](mathdb-announcement.md)
- [External review request draft](external-review-request.md)
- [Separate R009 paper track](R009-publication-track.md)
- [Validation report](evidence/publication-validation.json)

The paper combines R008 and R010. It includes the needed unsigned progression argument from R006 and states that dependency explicitly. It does not include R006's primitive-root application or the unrelated R009 reconstruction result.

## Build and reproduce

The source ZIP contains only `main.tex`, `references.tex`, and seven section files. It has no local absolute paths, external input files, generated bibliography, or custom style dependencies. Standard LaTeX packages are used. The local build was tested with Tectonic 0.17.0; this does not replace checking arXiv's own processed PDF at submission.

From this directory:

```sh
mkdir -p output/pdf
tectonic --keep-logs --outdir output/pdf main.tex
cp output/pdf/main.pdf output/pdf/prime-predecessor-residues.pdf
python3 package_sources.py
```

A conventional PDFLaTeX build should use repeated passes to resolve the contents and references. That engine has not been tested in this environment.

This checkout also retains the downloaded local compiler at `tmp/publication-tools/tectonic`; use that path in place of `tectonic` if it is not on the shell's path. Temporary tools and rendered inspection pages are ignored by Git.

The upstream source cache is ignored by Git and excluded from the upload ZIP. To retrieve the exact files used in the audit and repeat the finite checks:

```sh
python3 fetch_upstream.py
python3 check_identities.py
```

Both scripts use only Python's standard library. The fetcher verifies every file against the existing SHA-256 and Git-blob manifest. The identity checks cover small residue moduli, local squarefree densities, full small-prime covariance, Fourier filters, and the signed coin and allocation identities. These checks do not prove the analytic estimates.

## Provenance and editing

The source corpus is pinned to `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. The research snapshot is `e7ce0ecad79b6e330dd345dbec68369a843dc0d8`. The publication work is isolated on `publication/prime-predecessor-paper`; it does not change the main research thread or its original checkout.

AI assistance is disclosed in the abstract and Appendix A.2. Previous internal proof reviews were performed by AI agents; they are not human peer review or formal verification. The paper does not claim worldwide priority.

The user-requested [unslop skill](https://github.com/cursor/plugins/blob/main/pstack/skills/unslop/SKILL.md) was applied to the prose. The [editorial record](EDITORIAL-REVIEW.md) describes the pass. Mathematical meanings and qualifications take precedence over stylistic shortening.

## Remaining publication decisions

The author should review this concrete draft and its AI-use disclosure, obtain independent mathematical criticism, and decide whether and where to submit. The targeted review questions are in the unsent review request. This recommendation is not an additional approval requirement for local drafting.

For arXiv, the account, contact details, endorsement status, and distribution license remain for the author to supply or select. arXiv requires registration, may require endorsement for a first submission or new category, and asks authors to check the processed source and metadata. See its [submission instructions](https://info.arxiv.org/help/submit/index.html) and [endorsement guidance](https://info.arxiv.org/help/endorsement.html), checked October 9, 2026. Endorsement is not peer review.

For MathDB, the draft targets the [Moree–Hommersom parity problem](https://mathdb.com/p/377990/parity-conjecture-for-the-mobius-function-on-shifted-primes). A stable manuscript link or attachment should accompany a future announcement. No public manuscript URL or arXiv identifier has been invented.

External submission, posting, or contact requires a new explicit instruction. No permission is being requested to complete this local package. If publication to the existing GitHub repository is later requested, use its filtered `openai-proof-research` history; never push the unfiltered local repository history.
