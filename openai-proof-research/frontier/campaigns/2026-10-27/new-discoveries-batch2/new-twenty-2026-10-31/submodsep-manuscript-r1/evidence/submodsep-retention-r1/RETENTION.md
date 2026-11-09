# Version-of-record retention check: MathDB 341850

UTC: 2026-11-05T06:03:03.982428+00:00

**Overall: NOT DETERMINED. Recommendation to root: HOLD, zero credit.**

The permitted sources do not establish whether the 2022 SICOMP article retains, modifies, replaces or withdraws the preprint conjecture. There is no positive withdrawal evidence either. The root ruling already resolves routine-corollary eligibility in favour of the candidate; this investigation does not reopen that ruling or accept the result.

The strongest new negative finding is that Brakensiek’s Stanford doctoral thesis is a coding-theory thesis, not a reproduction of the CSP paper. The later matroid paper cites SICOMP 2022 but does not quote the separator conjecture. None of these facts certifies journal retention.

## Source receipts and passages

Each SHA256 below binds the downloaded body, including denial/challenge bodies. Null passages/pages mean no scientific content could be inspected. Receipts preserve exact UTC, status, headers and redirect history.

### Stanford Digital Repository thesis record

- URL: https://purl.stanford.edu/rc211rc7517
- UTC: 2026-11-05T05:58:35.037398+00:00
- Status: HTTP 200
- SHA256: `04d991bcf671d124eedbf2b48795f0ec2981aff88b90381bb4ce0d38421ab290`
- Page: HTML title and Summary, unpaginated
- Verdict: **NOT DETERMINED**

Exact passage:

> Higher order MDS codes

Identifies the coding-theory thesis and links SearchWorks. The summary is unrelated to the CSP separator conjecture.

### Stanford repository XML

- URL: https://purl.stanford.edu/rc211rc7517.xml
- UTC: 2026-11-05T05:58:56.150278+00:00
- Status: HTTP 200
- SHA256: `4fc53a23d0108e4493c4dddd4ddf140f37d6d360a76113d8aea368ac7ae10199`
- Page: contentMetadata resource 1, unpaginated
- Verdict: **NOT DETERMINED**

Exact passage:

> <file id="thesis-augmented.pdf" mimetype="application/pdf" size="1104076" publish="yes" shelve="yes" preserve="yes">

Supplies the legitimate open thesis download filename; metadata alone says nothing about retention.

### Stanford SearchWorks record

- URL: https://searchworks.stanford.edu/view/in00000028070
- UTC: 2026-11-05T05:59:07.862729+00:00
- Status: HTTP 200 CHALLENGE
- SHA256: `e2f061c7506368bc3cb202cb86a8e9e5d7a9a01639a083a8438d44b1076d2f20`
- Page: Not available
- Verdict: **NOT DETERMINED**

Exact passage: none; access response did not expose the paper.

HTTP 200 is a JavaScript challenge, not catalogue content. Stopped without retry or challenge execution.

### Joshua Brakensiek, Higher Order MDS Codes

- URL: https://stacks.stanford.edu/file/druid:rc211rc7517/thesis-augmented.pdf
- UTC: 2026-11-05T05:59:06.510627+00:00
- Status: HTTP 200
- SHA256: `cbef932dffdfe876517492baaed54c65695a4a9f64c3235c0dd11a954a2e18f7`
- Page: printed p. 7 / PDF p. 19; contents vii-ix; full-text screen
- Verdict: **NOT DETERMINED**

Exact passage:

> Most of the material in this thesis is adapted from the papers
> [BGM21, BGM22, BDG23b, BDG23a].

Title page: November 2023; homepage identifies the 2024 PhD thesis. Contents and source-material paragraph show no reproduced global-modular-CSP chapter. Full extracted text has zero occurrences of global modular, HORN, SUBMOD-MIN, or Conjecture 3.33; its sole submodular occurrence, printed p. 73 / PDF p. 85, is a generic-intersection LP separation oracle, not the monomial-image separator. Absence here does not imply withdrawal from the journal.

### Joshua Brakensiek homepage

- URL: https://jbrakensiek.github.io/
- UTC: 2026-11-05T05:58:55.709945+00:00
- Status: HTTP 200
- SHA256: `ae4b062644127046b85bc062eac1f15074bc25a31d2d69280a9900b86fcfbb15`
- Page: HTML publication entry, unpaginated
- Verdict: **NOT DETERMINED**

Exact passage:

> Constraint Satisfaction Problems with Global Modular Constraints: Algorithms and Hardness via Polynomial Representations

Lists SICOMP 2022 but links existing arXiv/ECCC preprints. No accepted-manuscript equivalence statement found. A journal listing alongside a preprint link does not certify identical body text.

### Venkatesan Guruswami publication list

- URL: https://people.eecs.berkeley.edu/~venkatg/pubs/venkat-papers.html
- UTC: 2026-11-05T05:58:55.452158+00:00
- Status: HTTP 200
- SHA256: `c49a3d1e50ff1eef7a8c029d4a6c0c42cecbe7d9a9e324d77c81c5809325d0b0`
- Page: HTML publication entry, unpaginated
- Verdict: **NOT DETERMINED**

Exact passage:

> Constraint Satisfaction Problems with Global Modular Constraints: Algorithms and Hardness via Polynomial Representations

Lists SICOMP 2022 but links existing arXiv/ECCC preprints. No accepted-manuscript equivalence statement found. A journal listing alongside a preprint link does not certify identical body text.

### Sivakanth Gopi publication list

- URL: https://gopisivakanth.github.io/publications/
- UTC: 2026-11-05T05:59:21.184438+00:00
- Status: HTTP 200
- SHA256: `75f344aaf8d95111f7a084fe9ba93e1ee83a1f7686323efab80e015ab8a9f667`
- Page: HTML CSP entry, unpaginated
- Verdict: **NOT DETERMINED**

Exact passage:

> Journal version

Journal version links the denied SIAM DOI landing URL; Download Paper links arXiv:1902.04740. Neither link establishes body-text equivalence. Did not follow the denied-host link.

### DBLP journal article record

- URL: https://dblp.org/rec/journals/siamcomp/BrakensiekGG22.html
- UTC: 2026-11-05T05:59:43.664213+00:00
- Status: HTTP 202 CHALLENGE
- SHA256: `c2a94120ea45f84ef7f2beb11147ba5260f1a973187ae4255eb672462c5d82dd`
- Page: HTML title, unpaginated
- Verdict: **NOT DETERMINED**

Exact passage:

> Making sure you&#39;re not a bot!

Anubis challenge; stopped without solving or retrying.

### SICOMP version-of-record HTML landing page

- URL: https://epubs.siam.org/doi/10.1137/19M1291054
- UTC: 2026-11-05T05:58:55.233269+00:00
- Status: HTTP 403 DENIED
- SHA256: `99f9e98700805246ed6f3d9d54910035da31bb27483a38ce61b9ad5e840e7fa2`
- Page: Not available
- Verdict: **NOT DETERMINED**

Exact passage: none; access response did not expose the paper.

Single explicitly permitted non-PDF HTML request returned 403. No redirect or retry; no SIAM PDF requested. Search-engine snippets expose abstract/bibliography but no conjecture body and cannot close the gate.

### On the Congruency-Constrained Matroid Base

- URL: https://arxiv.org/pdf/2311.11737
- UTC: 2026-11-05T06:00:15.325006+00:00
- Status: HTTP 200
- SHA256: `faa0e0230d3f563283c4079733cf5789c447fac98ee7d980c20324881996917d`
- Page: printed p. 1 / PDF p. 1; journal reference [6], printed p. 9 / PDF p. 9
- Verdict: **NOT DETERMINED**

Exact passage:

> constraint satisfaction problems [6]
> SIAM Journal on
>      Computing, 51(3):577–626, June 2022.

Reference [6] is BGG, SIAM Journal on Computing 51(3):577–626, June 2022. This is a positive journal citation, not a quotation or endorsement of Conjecture 3.33. The only citation-context occurrence is general motivation; no target separator statement located.

### Advances on Strictly Delta-Modular IPs

- URL: https://arxiv.org/pdf/2302.07029
- UTC: 2026-11-05T06:00:15.531478+00:00
- Status: HTTP 200
- SHA256: `547fc0dd96c75110f80c1088d3c5eff4ee443d95c81404f0b06b1b14ad2c61ac`
- Page: printed p. 3 / PDF p. 4
- Verdict: **NOT DETERMINED**

Exact passage:

> on congruency-constrained submodular minimization [NSZ19] to solve the optimization version of the

The passage concerns a prime-power algorithm. No Brakensiek/Gopi citation or target separator conjecture located. It cannot establish retention.

### Congruency-Constrained TU Problems Beyond the Bimodular Case

- URL: https://arxiv.org/pdf/2109.03148v3
- UTC: 2026-11-05T06:00:15.805210+00:00
- Status: HTTP 200
- SHA256: `3c695efd08bddb3322a28dee4db781ebe67f352fe63fd1d48ce479d75320ebc6`
- Page: printed p. 32 / PDF p. 33, Theorem 47 and Lemma 48
- Verdict: **NOT DETERMINED**

Exact passage:

> It remains to discuss our reduction from CTC problems to CCSM problems.

Section treats prime-power CCSM algorithms and a TU reduction. No Brakensiek/Gopi citation or target separator conjecture located. It cannot establish retention.

### CNF Satisfiability in a Subspace and Related Problems

- URL: https://arxiv.org/pdf/2108.05914
- UTC: 2026-11-05T06:00:16.272429+00:00
- Status: HTTP 200
- SHA256: `c3f0d05c12da45005baee02ad3126f7a9dab50145a0b30ee030147a82100ecfa`
- Page: printed p. 3 / PDF p. 3; reference [2] p. 21 / PDF p. 21
- Verdict: **NOT DETERMINED**

Exact passage:

> posed in [2] on the fixed-parameter complexity of 2-S AT with a global modular constraint,

Answers a different question, about fixed-parameter complexity. Reference [2] cites STOC 2019, not SICOMP 2022. No submodular separator statement located.

### ECCC TR19-013 baseline

- URL: https://eccc.weizmann.ac.il/report/2019/013/download/
- UTC: 2026-11-05T06:00:16.470417+00:00
- Status: HTTP 200
- SHA256: `bb9df9e013a834455d824a35db29d9b74b64c1f8455612e4a546e78886ad03c3`
- Page: printed p. 23 / PDF p. 25, Conjecture 3.33
- Verdict: **RETAINED UNCHANGED**

Exact passage:

> there exists a submodular function f

RETAINED UNCHANGED applies only to this live 2019 preprint relative to the review baseline. It is not a journal-equivalent manuscript. The universal r,d statement, integer codomain, polynomial evaluation and both sign conditions remain. Visually checked the rendered page.

## Meaning of the retained preprint statement

The live ECCC statement on printed p. 23 still universally quantifies integers 0 ≤ r ≤ d, uses n = Σ(k=0 to r) binom(d,k), and defines F(r,d) as the image of the vector of all squarefree monomials of degree at most r, including the constant monomial. It asks for an integer-valued submodular f on the entire n-dimensional Boolean cube, evaluable in polynomial time, with f ≤ −1 on F(r,d) and f ≥ 0 off F(r,d). Thus the baseline statement is unchanged. This is a mathematical transcription; exact line extraction is in eccc.txt:1337–1354 and the page image is tmp/eccc-conjecture.png. No inference of equivalence to the 50-page journal article is made.

## Bounded search and access limits

Bounded public web searches for exact DOI/title, author accepted copies, exact conjecture number, later congruency-constrained papers and ProQuest thesis abstract. No ProQuest result identifying this thesis surfaced; no ProQuest page fetched. Search snippets were discovery leads, not body-text evidence. No global completeness claim.

Search queries included the exact DOI, full title with PDF/manuscript/repository terms, Joshua Brakensiek doctoral thesis Stanford modular constraints, exact Conjecture 3.33 with submodular, Brakensiek/Gopi with submodular conjecture, and site:proquest.com with Higher order MDS codes. Search results repeatedly returned the known preprint, author lists, journal abstract and unrelated results. No search snippet was used to certify journal-body text. A ProQuest route was sought but no matching abstract page was identified.

The SICOMP landing request was the explicitly allowed HTML exception, not a PDF attempt. After its 403 no epubs.siam.org request was made. SearchWorks returned a challenge despite HTTP 200; DBLP returned an Anubis challenge with HTTP 202. Both were abandoned immediately. No challenge bypass was attempted.

## Integrity and process

inputs-before.sha256 verified at handback; inputs-after.sha256 freshly recomputed. Individual downloaded bodies independently rehashed by this script.

No prohibited routes requested; no denied-host retries. SIAM HTML requested exactly once under explicit brief exception. SearchWorks and DBLP challenges were not executed. TLS verification enabled. No child agents, git, browsers, accounts, uploads, author contacts or external messages.

Every Python invocation used python3 -I with a real lane-local script path, inside scripts/capped.sh: 2 CPU affinity, CPU 120 s, wall 140 s, 6 GiB sampled group RSS watchdog, MALLOC_ARENA_MAX=2, lane-local TMPDIR/cache. Downloads used distinct initially empty directories. Poppler follow-up operations also capped. No background work remains.

The report and JSON were generated by scripts/report.py after rehashing every downloaded body and checking the quoted passages. scripts/inspect.py preserves page-location evidence in logs/page-inspection.txt. The PDF skill was read for page inspection, and thesis abstract and baseline conjecture pages were rendered and viewed. No Lean or discovery-lane program was executed.

**Required next evidence:** an openly accessible final journal section or an author manuscript explicitly established as journal-equivalent. Until that exists, gate A remains qualified and root’s hold condition remains unclosed.
