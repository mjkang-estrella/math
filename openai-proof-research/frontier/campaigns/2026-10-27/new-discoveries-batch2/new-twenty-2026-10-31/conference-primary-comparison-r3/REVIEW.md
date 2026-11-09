# Focused primary-source comparison r3: MathDB 324342 (conference-matrix MDS conjecture)

Reviewer: Claude Opus 5.5, lane `conference-primary-comparison-r3`, 2026-11-01, 13:07–13:25 UTC. This is a bounded review only. It awards no credit and changes no count. The campaign stays at 3/20 beyond 39; the "2/20" in adjudication r2 is stale. Root acceptance, the paper and the final replay are separate gates.

## Scope accepted, not reopened

- Qualified significance PASS (root adjudication r2): narrow full-scope refutation; no demonstrated routine reduction.
- Technical PASS: independent Lean replay, 90 main + 26 control declarations; root wording corrections closed.
- Endpoint: `ConferenceMDS.conjecture5_false`, in `conference-mds-resume-r4/lean/ConferenceMDS324342.lean`, sha256 `49a2c41f…a111` (verified in the frozen set). One order-20 conference matrix over F₁₉ has a row-code word of weight 9, so d ≤ 9 < 11. The dimension clause (p+1)/2 = 10 is true.
- Not claimed in Lean: exact d = 9, the 180/6,180 word counts, minimality of p = 19, the two-class dichotomy.

I did not re-replay Lean or build a paper. I did not reopen significance, and I did not widen the candidate into a structural theorem.

## Verdicts on each gap

| Gap | Verdict | Basis |
|---|---|---|
| **TIT 2013 journal math (damaged glyphs)** | **RESOLVED (PASS)** | Journal pp. 6712–6723 were rendered locally from the frozen author-posted IEEE typeset copy, including the orphaned p. 6715. Conjecture 1, Theorem 4 and open problem 2 read with all math glyphs. They agree clause-for-clause with arXiv v1/v2 Conj 5 and ISIT Conj 1 (§2). |
| **Arasu–Gulliver 2001 body** (§2, Props 2.1–2.2, tables) | **UNRESOLVED: exact gap retained; novelty HOLD stays under root's standard** | Every bounded lawful route is closed, rate-limited or behind a challenge (§3). The gap is narrowed by secondary descriptions and arithmetic, but not body-cleared. |
| **Grassl–Gulliver 2008 body** | **UNRESOLVED, low risk** | The body is closed. The journal EVY text itself cites GG only for "Codes with these parameters (self-dual MDS of length q+1, q a prime power) were constructed in [17]" (§2, §4). |
| **Live registries** | **No hit** | openai/math is unchanged at `4eaee875`. Omega moved to `e9b39e56`; its one path hit is unrelated (§5). |
| **Public refutation / citing bodies** | **None found (bounded)** | 7 of the ~16 citing bodies have now been grepped; the rest were screened by title only (§6). |

## 1. Inputs read

- **AGENTS:** `openai-proof-research/AGENTS.md`, `new-discoveries-batch2/AGENTS.md`, `new-twenty-2026-10-31/AGENTS.md`.
- **Ledger:** `ledger.json`. It records `accepted_new: 3`; candidate 15 is `technical_PASS_qualified_significance_PASS_novelty_body_gap_HOLD`, followup 105 is this lane, and three prior-art gaps are listed.
- **Prior reviews:**
  - `conference-significance-adjudication-r2/REVIEW.md` and `review.json`, plus `conference-adjudication-parent-integration-r2.json`.
  - `conference-significance-review-r1/REVIEW.md`, its `work/fetch.log` (14 receipts) and its cached bodies `1311.2637.txt` (Armario–Frau) and `hm.txt` (Harada–Munemasa).
  - `conference-fidelity-review-r1` source receipts.
  - `conference-parent-revision-r1` SUMMARY, PROOF (header) and review.json.
- **Source texts:** `fresh-corpus-r3/sources/1210.5725.txt`, `1210.5725v1.txt` and `web/28_Lee_Manhattan_ISIT13.txt`.

## 2. EVY IEEE TIT 59(10) 6712–6723 (2013): readable journal math authenticated

**Source.** The frozen file `conference-mds-resume-r4/web-untrusted/r4/IT13.pdf`, sha256 `a7b49ca6…2c70`. It was fetched by r4 at 08:20:02Z from `yaakobi.net.technion.ac.il/files/2015/04/7_Lee_Manhattan_IT13.pdf`, HTTP 200, 3,472,993 bytes.

- It is the author-posted copy of the IEEE typeset article. The rendered p. 6712 shows the running header "IEEE TRANSACTIONS ON INFORMATION THEORY, VOL. 59, NO. 10, OCTOBER 2013", DOI 10.1109/TIT.2013.2268156, "Manuscript received December 11, 2012; revised May 16, 2013; accepted June 06, 2013. Date of publication June 12, 2013; date of current version September 11, 2013", and "0018-9448 © 2013 IEEE".
- The journal date is 2013. "2015" is only the upload directory.

**Why earlier text extraction failed.** The PDF is truncated: it has no xref or trailer, and the page dictionary for p. 6715 (object 269) is cut off. Poppler cannot parse it, and Ghostscript rendered only 3 pages.

**Rebuild (copy only; the frozen file is untouched and its hash was re-verified afterwards).**

1. `scripts/rebuild_pages.py` appends a fresh Pages tree, catalog and xref to a copy (`work/it13-rebuild/IT13-repaired.pdf`, sha256 `54273741…abc6`). Ghostscript `-dSAFER` then rendered 11 pages, pp. 6712–6714 and 6716–6723 (`q01…q11.png`).
2. `scripts/orphan_page.py` wraps the unreferenced content stream, object 129 (290,534 bytes compressed, 1,536,099 decompressed), in a synthetic page. The stream uses only the fonts /TT10, /TT2 and /TT4 and the graphics state /GS1. Each of these maps to exactly one font object across all resource dicts in the file, so the mapping is unambiguous. The content stream bytes are unmodified; only the page wrapper is synthetic. Output: `work/it13-rebuild/p6715.pdf` (sha256 `8c35df3c…bbe`), rendered to `p6715.png` (sha256 `1c42c15e…192`).

**Journal text read from the rendered images.**

> *Theorem 4:* If 𝒲 is a conference matrix of order n = p + 1, where p is a prime, then its rank over ℤ_p (also 𝔽_p) is (p+1)/2.
> … We believe that a surprising result will be derived if we will examine the Hamming distance of these codes.
> *Conjecture 1:* If ℂ is a code of length p + 1 constructed from a generator matrix which is a conference matrix then ℂ is a maximum distance separable (MDS) code of dimension (p+1)/2 and minimum Hamming distance (p+3)/2.
> Conjecture 1 was verified to be true up to n = 23, where the conference matrices are based on the Paley's construction from quadratic residues modulo p. Codes with these parameters (self-dual MDS of length q + 1, q a prime power) were constructed in [17]. (p. 6715)

> 2) Is the code of length p + 1, p prime, obtained from a conference matrix of order p + 1 an MDS code? (p. 6722, §V)

Reference [17] is "M. Grassl and T. A. Gulliver, 'On self-dual MDS codes,' in Proc. IEEE Int. Symp. Inf. Theory, Toronto, ON, Canada, 2008, pp. 1954–1957." The same page also has Theorem 2: the code over ℤ_w reduced from Λ(W) is self-dual.

**Clause comparison.**

| Clause | arXiv v1 (Conj 5) | arXiv v2 (Conj 5) | ISIT 2013 (Conj 1) | TIT 2013 (Conj 1) |
|---|---|---|---|---|
| Length | p+1 | p+1 | p+1 | p+1 |
| Generator | conference matrix | same | same | same |
| Conclusion | MDS | MDS | MDS | "maximum distance separable (MDS)" |
| Dimension | (p+1)/2 | (p+1)/2 | (p+1)/2 | (p+1)/2 |
| Distance | (p+3)/2 | (p+3)/2 | (p+3)/2 | (p+3)/2 |
| Theorem 4 order | n = p − 1 (typo) | n = p + 1 | n = p + 1 | n = p + 1 |
| Paley-only evidence remark (n ≤ 23) | yes | yes | yes | yes |
| GG cited for existence of the parameters | yes, [17] | yes, [17] | yes, [14] | yes, [17] |
| Open problem 2 | — | "…is an MDS code?" | — | "…an MDS code?" |

**Conclusion.** The parameters and quantifier scope are identical in all four versions. The only differences are the label (5 vs 1), the spelled-out "maximum distance separable", and a one-word grammatical fix in open problem 2. No Paley restriction appears in any version. The earlier "same wording" claim was previously unverifiable; it is now verified from rendered journal glyphs. I am not inferring identity from missing glyphs.

**Limit.** This is the author-posted typeset copy, not a publisher retrieval. Its header, DOI and dates match Crossref (r4 receipt `b7f762b1`).

## 3. Arasu–Gulliver 2001 (IEEE TIT 47(5) 2051–2055, DOI 10.1109/18.930940): bounded routes

Every request was made once; there were no retries of denied routes and no challenge was solved. Receipts are in `receipts/http-receipts.jsonl`.

| Route | Result |
|---|---|
| OpenAlex work (live, 13:10Z) | 200, metadata only. `oa_status: closed`, `any_repository_has_fulltext: false`. Locations: DOI, and the CORE Scholar page `math/563` ("submittedVersion", but no file) |
| CORE Scholar `math/563` (cached r1 body `3f23c4d7`, re-read) | Metadata page. Links only to DOI/openurl and the WSU ezproxy (campus login), which was **not** used |
| Crossref work | 200, metadata. Its only link is `xplorestaging.ieee.org/…00930940.pdf`, marked `intended-application: similarity-checking`. That is a licensed Similarity Check route, so it was **not** fetched (not a lawful public route) |
| fatcat API lookup | Timeout (curl 000, 60 s). Not retried |
| scholar.archive.org search | 200, but the body is a JavaScript proof-of-work "Session Verification" challenge. **Not** solved |
| Gulliver's UVic homepage and `journals.html` | 200. A general e-journal link list; no publication PDFs |
| arXiv API (au:Gulliver, weighing/MDS) | One unrelated hit (1207.3384) |
| Web searches (2) | Only CORE Scholar, the WSU research portal (metadata), Armario–Frau and arXiv citing papers. No copy |
| AG citing list (OpenAlex, 28 works) | Elsevier-hosted citers: ScienceDirect returned **403** (no further Elsevier requests). HAL `hal-04089321`: Anubis PoW challenge, **not** solved. CiteSeerX: **429**, not retried. arXiv 2009.06609 (Choi–Kim) body read: AG appears only in a group citation for optimal self-dual codes; there is no conference-matrix row-code statement |
| Gaborit self-dual code tables | 200, but they cover only GF(2), GF(3), GF(4), GF(5) and GF(7). No GF(19) |

**Primary body: still unread.** §2, Propositions 2.1–2.2 and the tables were not inspected.

**Narrowing (secondary and arithmetic only, not body clearance).**

1. **Armario–Frau, arXiv:1311.2637v1** (cached r1 text, re-read §1.2, §2.C and §3):
   - The AG method is Prop 1.4: G = [αI, βI + W] for skew W with α, β ≠ 0 and α² + β² + k ≡ 0 (mod p). It reduces to Prop 1.3 (Gulliver–Harada, [αI, W], α² + k ≡ 0) when β = 0.
   - AG's tabulated data are "values of α providing self-dual codes with **symmetric** conference matrices and the distance of these codes", summarized as Table 1 "orders n = 6 and 14".
   - "Length 40 was the limit of the search for minimum distance given in [2]."
   - The conclusion cites "[2, Proposition 2.1 and 2.2] for conference matrices". The AG d-bound quoted is for the length-2n code C(n, n−1).
2. **Arithmetic check** (`scripts/ag_arith.py` → `work/ag_arith.json`, < 1 s):
   - The nonzero squares mod 19 are {1,4,5,6,7,9,11,16,17}, so −1 is not a square.
   - For p = k = 19, the equation α² + 19 ≡ 0 has no solution with α ≠ 0, and α² + β² + 19 ≡ 0 has no solution with α, β ≠ 0.
   - So neither AG construction yields any F₁₉ code from an order-20 conference matrix.
3. **The abstract's "all weighing matrices of order n ≤ 13"** stops below order 20.

**Residual risk, stated exactly.** An unread AG remark or table entry could still discuss the length-n row code of W itself when p | k. For order 20 over F₁₉, the risk would be a computed minimum distance below 11 or a statement that such codes need not be MDS.

- EVY Theorem 2 (journal p. 6715) shows the general self-orthogonality/self-duality observation was standard to EVY themselves. It is not the refutation datum.
- EVY 2012–13, writing 11 years after AG and citing the Gulliver-coauthored GG paper, posed the question as open. This is weak circumstantial evidence and **not** clearance.
- Harada–Munemasa 2011 uses length-n row codes mod p | k but does not cite AG. This is weak evidence only.

**Verdict.** The gap stays exactly: AG §2 (Props 2.1–2.2) and tables, body unread. Root's targeted novelty HOLD is not lifted by this lane. I did not continue retrieval after the bounded routes, per instruction.

## 4. Grassl–Gulliver 2008 (ISIT, DOI 10.1109/ISIT.2008.4595330)

- OpenAlex (live) reports closed with no repository full text. Crossref reports metadata only.
- fatcat timed out; scholar.archive.org returned a challenge; the web search found no copy. The OpenAlex citing query for GG got **429** and was not retried.
- **New primary datum:** all four EVY versions cite GG only as the construction of "Codes with these parameters (self-dual MDS of length q+1, q a prime power)". That is the existence side, consistent with the Paley/RS half and with GG's abstract.
- Choi–Kim (arXiv 2009.06609, read) cites GG as solving the characteristic-2 case. Nothing found ties GG to non-Paley conference row codes.
- **Verdict:** body unread, low risk, gap disclosed.

## 5. Live registries (checked before any clearance statement)

**openai/math.**
- `commits/HEAD` at 13:10:25Z gives `4eaee87548250b2682affda7d05d947c05554bae` (committed 2026-10-30T00:35:35Z, "Align CM Hodge comparator declarations…"). Unchanged since the last receipt.
- The recursive tree `71e8eaa3…` is **truncated** by GitHub (55,173 entries).
- A path-keyword screen (conference, weighing, Etzion/Vardy/Yaakobi, Lee/Manhattan, Reed–Solomon, MDS, self-dual, Hadamard, Paley, 324342, Arasu/Gulliver/Grassl) gives 17 hits: Hadamard comparator challenges, Littlewood–Paley, self-dual lattices and cones. None is about conference-matrix codes.
- r4's CONTENTS/history/README/preprints screens at this same head remain applicable.
- **Limit:** path screen only, on a truncated tree.

**Omega (the-omega-institute/trureturing).**
- HEAD moved from `9abc86d1…` to `e9b39e568e8e0b68788ec0f007bc0107069db513` (13:06:17Z).
- The compare shows 33 commits and 15 files: cycle sums, minus-four domination reassembly, cross-intersecting layer gap and a sparse-paving doc. None is relevant.
- The Problems subtree (`48b27580`, 1,629 entries) and the D5 subtree (`9fad7f87`, 13,297 entries) are not truncated and are unchanged from the r2 screen. Library has 2,598 entries.
- Path screen hits:
  - Problems: pseudo-Paley, Hadamard-power and Hadamardness items, and an unrelated Yaakobi deletion-channel item.
  - Library: Hadamard and Paley–Zygmund items.
  - D5: one relevant-looking path, `D5/S3/Quantum/Fermionic/ConferenceMatrices.lean`. Its **body was read** at the head (sha256 `88f05537…`). It is a recursive skew conference family of order 2^{r+1} (`conference_properties`: skewness, signs, order, scalar square), added in commit `697fa44d` on 2026-10-10. It has no codes, no prime field and no order 20. **Unrelated.**
- **Limit:** path screen plus that one body. Not a full-body clearance of either registry.

**MathDB.** The state is still known only to 04:46 UTC. The inherited 403 was respected and not retried.

## 6. Citing-body refresh (bounded)

Semantic Scholar now lists 14 citers of arXiv 1210.5725; the TIT DOI node is a self-duplicate. The titles cover Lee/lattice/DNA/grid/NOR-memory topics.

- **Bodies newly read:**
  - 2202.10005 (grid codes);
  - 1611.00435 (Constructions D/D′ l₁);
  - 2404.12868 (composite DNA);
  - 1306.5350 (NOR memory).
  None mentions conference matrices or MDS except in the reference to EVY.
- **Cumulative:** 7 bodies read, together with r1's 2303.16879, 2207.08031 and 1412.5797. The remaining citers are title-only, with no arXiv copy.
- **Two live web searches** found no counterexample to, or resolution of, Conj 5 / Conj 1 / open problem 2. One relevant datum: arXiv 2102.08422 lists the best-known [20,10] self-dual code over GF(19) as d = 11, which is the MDS/Paley side and consistent with the record.

This is not a global clearance.

## 7. Primary-scope bridges

- **MathDB literal ↔ journal.** The MathDB record 324342 wording ("Let p be a prime … conference matrix … MDS code of dimension (p+1)/2 and minimum Hamming distance (p+3)/2") matches TIT Conj 1, read from the rendered glyphs, in every parameter. "Let p be a prime" in MathDB corresponds to the journal's surrounding context: Theorem 4 immediately precedes and fixes "n = p + 1, where p is a prime", and open problem 2 says "p prime".
- **Journal ↔ Lean.** The journal's "code … constructed from a generator matrix which is a conference matrix", read with Theorem 4's "rank over ℤ_p (also 𝔽_p)" and Theorem 2's reduction from Λ(W), is the F_p row span. This is what `rowCode` and the bridge `latticeCode_eq_rowCode` formalize; fidelity was already reviewed in r1.
- **Refuted clauses.** The journal conclusion "MDS … and minimum Hamming distance (p+3)/2" is refuted by d ≤ 9 at p = 19. The dimension clause, Theorem 4, stays true.

## 8. Qualified current novelty recommendation

- **Literal/source fidelity:** **PASS, now including the journal version.** The TIT glyph gap is closed.
- **Prior art (bounded):**
  - No public resolution was found in live registries, the refreshed citing bodies or searches.
  - No source states the order-20 F₁₉ row-code distance.
- **Material remaining gap: Arasu–Gulliver 2001 body only** (§2, Props 2.1–2.2, tables). It is narrowed, because its constructions as described cannot produce any F₁₉ code from an order-20 conference matrix and its data are length-2n codes. But it is not body-cleared. Under root's current standard the **novelty HOLD remains**; this lane supplies no data that lifts it.
- **If root applies the 388087 disclosed-gap precedent** (as adjudication r2 proposed), the strongest supportable novelty wording is: *"bounded novelty PASS; no prior statement found; Arasu–Gulliver 2001 body unread (closed access), with constructions as described incapable of producing the F₁₉ order-20 code."* That is a policy choice for root, not a finding of this lane.
- **Grassl–Gulliver 2008:** low-risk disclosed gap; EVY cites it only for existence of the parameters.
- **What would close the AG gap:** a lawfully obtained AG body, for example through institutional access by root, an author-posted copy appearing later, or a library scan delivered through authorized channels. This lane contacted no one and bypassed nothing.

## 9. Frozen checks and conduct

- **Frozen inputs:** `frozen-inputs.json` (140 files, frozen at 13:07:25Z). Before (13:09Z): 140/140 match (`receipts/frozen-before.json`). After (end of review): 140/140 match, 0 mismatch, 0 missing (`receipts/frozen-after.json`). This includes the frozen `IT13.pdf`; all rebuilds were made on copies under `work/`.
- **HTTP:** 34 single requests in `receipts/http-receipts.jsonl`, each with UTC, URL, status, final URL, bytes and sha256. Results:
  - HTTP 200: 29. Of these, 3 are challenge pages (scholar.archive.org ×2, HAL Anubis), recorded as challenges and not as bodies;
  - 403: 1 (ScienceDirect);
  - 429: 2 (OpenAlex, CiteSeerX);
  - timeout: 2 (fatcat, curl status 000).

  Metadata-only 200s are not treated as body reads. Downloaded content is under `web-untrusted/`, treated as untrusted, and processed only with `python3 -I`, `pdftotext` and Ghostscript `-dSAFER`.
- **Compute:** at most 1 CPU per process (`taskset -c 0`). Ghostscript ran with `ulimit -v 2 GB` and `timeout 240–300 s`, each render taking a few seconds. The arithmetic and screen scripts ran in under 1 s. No background jobs remain; the one fetch batch that was auto-backgrounded finished before any further work.
- **Not done:** no child agents, git, shared or author edits, external messages, uploads, browser or preview tabs, account actions, or Lean/paper rebuilds.
- **Credit:** zero awarded. All prior artifacts are preserved and unmodified.
