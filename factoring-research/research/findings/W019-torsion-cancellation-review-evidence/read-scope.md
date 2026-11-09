# Read scope and frozen inputs for ../W019-torsion-cancellation-review.md

All writes in this review are confined to that report and this directory. There was
no delegation, installation, commit, or edit to solver, Lean, STATE, registry, or task
files. Network use: one arXiv PDF download (Sutherland). Two PDFs were copied
byte-for-byte from the W017 review evidence; the hashes below match the W017 ledger.

## Repository inputs (snapshotted in inputs/ before analysis)

| file | sha256 | read |
|---|---|---|
| AGENTS.md | dc826260f9df986dd899270772d05443d6e3a3b6db521921969ccf1c370cc094 | complete |
| RESEARCH_TEAM.md | b460bb1785ef5f2514a475054962d515f2210a855b474497a5291e524bf53185 | complete |
| RESEARCH_LOOP.md | a1491eabfb67a9df1eb76ed5eb689c5165173ae995c859baa3d8b5f3436a46e1 | complete |
| README.md | b91bb2101c18e59706959612683e9b8c18b7bbdafe02bddfce7abbf705c3344f | complete |
| docs/SPECIFICATION.md | a851351f23ee1847f2bc306d190755bc3d407fb75baf2b45bb217d8eddb6c3db | complete |
| research/hypotheses/W019.md | afea2b58f83e36801e8630bfac5ed787f29801c4f589914aeaa04fb29e6f40df | complete; only section B audited |
| research/findings/W017-character-batch-review.md | 458efeef7e9760df8df2c215bfb61f6b8cbd6c4cccc00bfc657fe6fe7338378e | lines 1-60 (decisions) and 360-558 (sections 6-8: annihilator, extraction, cost); middle sections not reread |

From the W017 evidence tree, only `read-scope.md` (opening ~40 lines) and
`source-retrieval.json` were read, to locate and verify the already-frozen PDFs.
research/STATE.md was deliberately not read or frozen. The brief scopes this task to
W019-B, and nothing load-bearing here depends on STATE. The sibling review directory
`W019-public-cover-review-evidence/` was listed but not opened; it belongs to review A.

`brief.txt` transcribes the full task message. Its hash is in `delivery-manifest.json`.

## Primary sources

1. Schoof, "Quadratic fields and factorization" (Computational Methods in Number
   Theory, MC Tract 154, 1982), author copy; bytes copied from W017 evidence,
   sha256 d58c6b9f73b1bfc1a17735f52fa62a25b32e361a2c0fc8bd04896e0eef15e7d3.
   Read: printed p.265 (PDF page 31) and printed p.271 (PDF page 37), from rendered
   images `sources/schoof-p265-31.png`, `sources/schoof-p271-37.png`, plus the OCR
   text around Algorithm 6.4 (printed pp.270-272) and the bibliography entries [12],
   [18]. Load-bearing content: the ambiguous-form shapes and factorizations of the
   discriminant (p.265); Algorithm 6.4 Step 1 (D=-N if N=3 mod 4, D=-3N if N=1 mod 4)
   and Step 3 (subgroup H initialized to {1,(3,3,(N+3)/4)}, adjoin the 2-primary
   generator of each <f>, stop when H is noncyclic) (p.271). Theorem 6.3 /
   Corollary 6.2 (GRH) are cited from Schoof's text, not reproved. Ref [18]
   (Lenstra, Exeter 1980) was not obtained.
2. Sutherland, "Structure computation and discrete logarithms in finite abelian
   p-groups", arXiv:0809.3413v3 (7 Apr 2012), Math. Comp. version. Downloaded
   2026-10-09T01:03Z from https://arxiv.org/pdf/0809.3413, sha256
   0a11a858da57044826bdfcbddec0270e743bc1e2b87840da56d2fef84b4eab13
   (`sources/dl/`). Text extracted with pdftotext to `sources/sutherland.txt`.
   Read: abstract and introduction (pp.1-2, including Teske's bound (1) and the
   O(n^2) / O(n lg n) remarks), and section 4 pp.10-13 (Lemma 3, Algorithm 3,
   Lemma 4, Algorithm 4, statement of Proposition 2). Proof of Proposition 2,
   sections 2-3 and 5-6 were not read.
3. Schnorr-Lenstra, "A Monte Carlo factoring algorithm with linear storage",
   Math. Comp. 43 (1984); bytes copied from W017 evidence, sha256
   8c88b039dc33d3e449839552c778a01e89137832ef88036efe2ba26b800a7547. Only PDF page 4
   was viewed (two-up scan, 80 dpi, `sources/schnorr-lenstra-pdfpage04-80dpi.png`).
   That is too low a resolution for an audit. **Nothing in the report relies on
   Schnorr-Lenstra** beyond the bibliographic fact, recorded in W017, that it is a
   class-group factoring method with ambiguous classes.

Not consulted: Teske's papers, Pohlig-Hellman's original paper, Buchmann-Schmidt,
Cox's book, Hafner-McCurley, Lenstra-Pomerance. The genus-count statements in the
report are proved there directly from the reduced-form enumeration. They do not
rely on an unread genus-theory source.

## Certificate

`preregistration.md` and `certificate.py` were frozen before execution
(`preregistered-manifest.json`). Before the run the code got an `ast.parse` syntax
check only. It was run exactly once (`run-record.json`), with output in
`certificate-output.json`, and `certificate-stderr.txt` is empty. Nothing failed, so
no failure is omitted.
