# Source-access report — squared Pólya–Szegő first-clause refutation (r22)

Reviewer: pi-squared-polya-source-access-r22 (solo, no children). Date: 2026-10-27.
Scope: own lane only. Read pi-squared-polya-final-review/review.md + provenance.json and the
candidate's (parent-matrix-screen-r7) source/novelty notes first; no exhausted route repeated
except as re-verification. No parent/shared/candidate edits, no git, no tally/credit changes
(29/30 and credit 0 untouched), no contacts/uploads, no captcha/auth/paywall bypass.

Mission: close the two exact unread primary-body gaps that hold the novelty gate:
1. Published **Moslehian–Fu, Linear Algebra Appl. 491 (2016) 73–82** (PII S0024379515001160,
   DOI 10.1016/j.laa.2015.01.041) — does Conjecture 2.16's first squared clause (coefficient
   ¼ OUTSIDE the parentheses, proposed α² = ((√(M₁M₂/m₁m₂)+√(m₁m₂/M₁M₂))/2)²) survive
   publication unchanged vs arXiv:1501.02939v1 Conj 2.16 (p.9)?
2. Closest on-topic citer **Gümüş–Moradi–Sababheh, J. Math. Anal. Appl. 465(1) (2018) 267–280**
   (PII S0022247X18303883, DOI 10.1016/j.jmaa.2018.05.003) — actual theorem bodies; does it
   contain or imply a resolution/subsumption/counterexample to the target?

---

## Result 1 — JMAA 465 (2018) 267–280 body: **READ — CLEAR** (gate item 2 closed, with one caveat)

**How obtained.** Google Scholar's "All versions" for the paper (cluster 17140694746198115779)
lists a `[PDF]` version that is an author-shared copy on Academia.edu
(paper page `https://www.academia.edu/81792067/More_accurate_operator_means_inequalities`,
uploads id 87713646). The copy is **Elsevier's own "Accepted Manuscript"** of
PII S0022-247X(18)30388-3 (header: "Please cite this article in press as: I.H. Gümüş et al.,
More accurate operator means inequalities, J. Math. Anal. Appl. (2018)"; received 26 Dec 2017;
16 pages). The full page-by-page public renders (HTML text layer + SVG graphics) were fetched
from `attachments.academia-assets.com/87713646/N.html` (plain curl, HTTP 200, no login).
All 16 page HTMLs, 6 load-bearing SVG layers, and my extracted full text are preserved and
hashed in `sources/jmaa2018-pages/` (`SHA256SUMS.txt`); visual records of pages 8–12 that I
actually read are in `evidence/visual-page*.png`.

**What the paper actually contains** (read textually page-by-page, and visually for the
load-bearing displays on pages 8–12):

- The word **"conjecture" occurs zero times**. There is **no** statement, resolution,
  subsumption, or counterexample of MF's Conjecture 2.16 (either clause) anywhere.
- MF's paper is cited **exactly once**, as [19]: "The problem of squaring operator
  inequalities has been studied extensively in the literature. We refer the reader to
  [12, 16, 19] as sample of this work." — a literature nod; no content of [19] is used.
  (Reference [19] misprints the volume as 490; the published volume is 491.)
- **Every squared result runs in the reverse-AM-GM (Lin) direction**, bounding the squared
  *map of an arithmetic-type mean*:
  - Corollary 2.5 + (2.13)/(2.14): Φ(A∇B) ≤ K(h)Φ(A♯B) and **Φ²(A∇B) ≤ K²(h)(Φ(A)♯Φ(B))²**,
    K(h) = (h+1)²/4h, h = M/m;
  - squared version of their Theorem 2.1: **Φ²(A∇ᵥB) ≤ K(h)·((m∇λM)/(m♯λM))²·(Φ(A)♯ᵥΦ(B))²**;
  - (2.15): Φ²(A∇ᵥB) ≤ K²(h)Φ²(A♯ᵥB);
  - Proposition 2.3: Φ²(A∇ᵥB) ≤ C·Φ²(A♯ᵥB) and Φ²(A∇ᵥB) ≤ C·(Φ(A)♯ᵥΦ(B))²,
    C = min{K(M/m)·((m∇λM)/(m♯λM))², K²(M/m)}, λ = min{v,1−v}.
  (This manuscript's own "(2.16)" is the scalar lemma f(αt) ≤ αf(t) — unrelated to MF's
  Conjecture 2.16 despite the matching number.)
- The **target direction** — (Φ(A)♯Φ(B))² ≤ α²·Φ(A♯B)², bounding the squared geometric mean
  of images by the squared image of the geometric mean — appears **nowhere**, and nothing in
  the paper implies it. Structural reason: their squaring method (Lemma 2.1, Kantorovich
  constant) exploits the unital-map identity Φ(A∇B) = Φ(A)∇Φ(B) (arithmetic mean passes
  through unital maps); there is no analogous identity in the ♯ direction, and correspondingly
  their positive-map inequality (1.6) is never squared toward the Pólya–Szegő side.
- **No counterexample** (numerical or symbolic) to the first clause exists in the paper.
- The paper's own program — the sharper constant (m∇λM)/(m♯λM) for reverse AM-GM, operator-
  monotone-f comparisons (2.17) f(A)♯ᵥf(B) ≤ ((m∇λM)/(m♯λM))·f(A♯ᵥB), and the refined
  Golden–Thompson reverse — is orthogonal to the conjectured sharpening.

**Caveat (recorded honestly).** This is the *accepted manuscript*, not the typeset final
article (the final remains behind ScienceDirect's interactive captcha). Mathematical content
of an accepted manuscript is what was accepted; copyediting renumbers but does not change
content. For the gate question ("does the closest citer contain or imply a resolution or
counterexample") the residual risk is LOW; the typeset final remains unread and is noted as such.

**Ancillary new body read (bonus).** Dinh–Moradi–Sababheh, "On the Pólya–Szegő operator
inequality", Hacet. J. Math. Stat. 49(5) (2020) 1744–1752 (OA PDF from DergiPark, sha256
0e568bd8…, `sources/dinh2020.pdf`): cites the JMAA 2018 paper only glancingly ("[6, 8]
treating similar topics"); contains no conjecture handling and no counterexample to the
target. One more on-topic published body now checked and clear.

**Gate consequence.** Novelty gate item 2 (JMAA 2018) is **CLOSED-CLEAR**: the closest
on-topic citer neither contains nor implies a resolution, subsumption, or counterexample of
the target first clause. The two papers must still appear in any revised prior-art list
(with their actual content, per this report).

---

## Result 2 — Published LAA 491 (2016) 73–82 body: **STILL UNREAD — HOLD retained**

**The only public copy in existence is the ScienceDirect open-archive PDF.** Re-verified
today across every aggregator: Unpaywall v2 (bronze publisher-only; `any_repository_has_
fulltext` is true only because of arXiv v1), OpenAlex locations, OpenAIRE (3 instances, all
DOI/zbMATH pointers), zbMATH Open Zbl 1336.47019 (links: DOI + arXiv 1501.02939 only),
Semantic Scholar (openAccessPdf = SD bronze). **No repository, author, or archive copy
exists.** (For the JMAA paper, zbMATH likewise confirms no arXiv version exists — closing
that earlier sub-question definitively.)

**Routes attempted and exhausted this round** (all evidence hashed in the lane):
- ScienceDirect via a real Chrome session (preview browser): **interactive human captcha**
  on both the article page and the `/pdf` endpoint (reference numbers a5143971fb5d3911 /
  a5143c648d0c3911, IP 136.152.42.161 — `sources/sd-captcha-evidence.txt`). Not bypassed.
  Tab closed afterwards.
- Wayback Machine targeted CDX (PII prefix): only an abstract page (2024, read — see below),
  a 2022 `/pdfft` **Cloudflare challenge interstitial**, and redirects; **no PDF asset
  archived**. Domain-wide CDX later rate-limited ("Temporarily Offline").
- Elsevier full-text API: parent's saved metadata-only XML re-examined — no body (unchanged).
- CORE: Cloudflare-blocked (moot — no repository copies exist). scholar.archive.org: JS
  challenge; fatcat API: connection refused (000).
- Author channels: moslehian.ir parked, no matching PDFs in its Wayback captures; Fu's
  Hainnu page bibliography-only (parent); Moslehian TWAS CV bibliography-only; Gümüş Adiyaman
  ABYS profile lists the paper linking to the publisher only (`sources/adiyaman-gumus-
  profile.html`); formasyon.adiyaman.edu.tr: nothing; Sababheh's PSUT Google Site: no PDF
  links (`sources/sababheh-site.html`); Academia.edu full-text search: 8 hidden results
  behind login, LAA paper not identifiable among them; ResearchGate: no public full text.
- Google Scholar for the LAA paper: no alternate public version surfaced (only citing
  papers' PDFs).

**Supporting (explicitly NOT body-level) evidence gathered:**
- The **published abstract**, read from the Wayback 2024 capture of the ScienceDirect
  article page (`sources/sd-laa-article-wayback-20240415.html`), is identical to the arXiv v1
  abstract: it states only the two **proven** inequalities (constants
  ((M₁M₂+m₁m₂)/(2√(M₁M₂m₁m₂)))⁴ and the Diaz–Metcalf constant). No conjecture in the
  abstract, matching v1; "Open archive" license confirmed.
- zbMATH 1336.47019 and Crossref show **no erratum/corrigendum/update relations**; MathDB
  329636 remains open with empty activity (parent's hash-verified snapshot).
- The JMAA 2018 paper (now read) cites the published MF paper as a mere "sample of squaring"
  work and uses nothing from it — weakly consistent with the conjecture surviving publication
  unchanged, but **not** a body-level confirmation.

**Gate consequence.** Item 1 (published-body comparison vs arXiv v1 Conj 2.16 first clause)
**remains open**. I do not force it PASS: the residual risk (published version could in
principle have modified/withdrawn the conjecture) is unchanged in kind, though nothing
accessible supports it. The HOLD on the bounded eligibility decision stays; only the root
can convert it.

---

## Strongest remaining objections / limits (independent statement)

1. **Published-body gap (open).** Until the LAA 491(2016) 73–82 body is read (it requires
   either a non-datacenter IP/interactive session on ScienceDirect or a copy the authors
   might share), first-clause *eligibility* is bounded, not closed. Everything else about the
   source (arXiv v1 statement visually verified; MathDB record) is already PASS.
2. **Accepted-vs-typeset caveat (new, small).** The JMAA 2018 clearance rests on the accepted
   manuscript. A future reviewer with publisher access should confirm the typeset final's §2.2
   matches (expected: yes).
3. **Secondary-evidence limits.** zbMATH reviewer texts are license-blocked; MathScinet
   unreachable; MR/IR none. No inference about the two bodies was drawn from abstracts,
   metadata, or absence of searches — only from the actual text obtained.
4. Prior-review items re-confirmed and not relitigated: Yang–Fu 2016 (JMI 10:571–575) does
   not subsume (K⁻¹ slack; and its reference list does not even contain MF); arXiv 1610.04162
   p.5 example violates its own bound; Hoa–Binh–Ho printed defect is wrong.
5. Access hygiene: interactive captchas on ScienceDirect (and CORE) were left unsolved; no
   shadow libraries; no author contact.

## Deliverables in this lane
- `report.md` (this file), `provenance.json`, `SHA256SUMS.txt` (51 hashed files)
- `sources/jmaa2018-pages/` — all 16 page renders + 6 SVG layers + extracted full text
  `jmaa2018-full.txt` + visual composites
- `sources/`: dinh2020.pdf/.txt, sd-laa-article-wayback-20240415.html,
  sd-laa-pdfft-challenge-2022.html, sd-captcha-evidence.txt, up-laa.json, up-jmaa.json,
  zb-laa.json, zb-jmaa.json, openaire-jmaa.json, openalex-cites-jmaa.json,
  scholar-cluster-jmaa.html, scholar-search-laa.html, sababheh-site.html,
  adiyaman-gumus-profile.html
- `evidence/visual-page2,8,9,10,11,12.png`

No acceptance, packet, tally, or credit change is made or proposed. Tally 29/30 and
candidate credit 0 untouched.
