# Four-projection source access r3: independent source/novelty assessment

Date: 28 October 2026 UTC (27 October 2026 America/Los_Angeles). Solo lane
`pi-fourprojection-source-access-r3`; no child agents; no git; writes confined to
this lane. Scope: legitimate primary-source retrieval for the published journal
body of Banica–Nechita, *Flat matrix models for quantum permutation groups*
(AAM 83 (2017) 24–46, DOI 10.1016/j.aam.2016.09.001, PII S019688581630077X) and
completion of the last uncovered novelty record (Jung 2019 thesis). I do not
prove, refute, or re-review the mathematics or the Lean artifact.

**Verdict: SOURCE HOLD — the actual journal conjecture page remains unread
after every legitimate public route tried this round. NOVELTY HOLD — no prior
resolution or complete subsumption found; all 26/26 Semantic Scholar citation
records now have at least some body coverage (Jung thesis newly read via a
public Wayback copy), with honest limits. No acceptance, no count change.**

Inputs (hashes verified before use): root candidate
`root-fourprojection-complete-r1` (freeze `a81ca96d98`, 35 hashes,
`sources/four-projections-arxiv-v3.pdf` sha256
`82ea37c2f43e0f2940ce190891306a08881d05149e98a0e743bbb48be5950fd1`),
`astra-fourprojection-preliminary-review-r1/review.md`,
`astra-fourprojection-source-novelty-r2/review.md`, batch AGENTS.md, ledger,
prior-campaign-context.

## 1. New primary fact: arXiv v3 predates journal acceptance

The Wayback snapshot of the ScienceDirect landing page (captured 2022-11-29,
200 HTML) contains the journal's editorial metadata:

- Received 15 February 2016; **Revised 1 September 2016**;
  **Accepted 5 September 2016**; available online 12 September 2016;
  Version of Record 12 September 2016; AAM 83, pages 24–46, February 2017;
  "Under an Elsevier user license **Open archive**".

The latest arXiv version v3 is dated **23 July 2016** — *before* the journal
revision and acceptance. Therefore arXiv v3 is **not** the accepted/typeset
journal version, and a journal-specific change to the conjecture (numbering,
hypotheses, inverse-root convention, or survival status) cannot be excluded
from v3. This makes the published-body gate materially stronger than an
ordinary "same content, different typesetting" situation. It also means the
journal's own Conjecture numbering (is it 6.6?) is unverified.

## 2. Retrieval evidence (all actual responses hashed in sources/retrievals.json)

New routes tried this round, none previously attempted by the earlier reviews:

| Route | Result | Evidence |
|---|---|---|
| Unpaywall API for the DOI | 200: `is_oa=true`, oa_status **bronze**; the ONLY OA locations are the SD publisher PDF (403) and arXiv (already held) | `unpaywall-doi.json` sha256 `6d55080b…d47599` |
| Semantic Scholar DOI record | 200: `openAccessPdf` = the same SD PDF URL (BRONZE); nothing new | `s2-doi.json` sha256 `5013d293…18d749` |
| Semantic Scholar arXiv record | 429 rate-limited; stopped without retry | `s2-arxiv.json` sha256 `65ab993d…5a148` |
| HAL API, DOI query | 200, **0 records** for the DOI | `hal-api-doi.json` sha256 `316b5968…88ba8064` |
| HAL API, title query | 200, exactly one record `hal-02980384v1`, `submitType_s: notice` (metadata only, no `fileMain_s`) — confirms the inherited finding and closes HAL-wide | `hal-api-title.json` sha256 `5db0145d…47f7e34` |
| Wayback CDX, all PII URL variants | Exactly one capture: landing HTML 2022-11-29 (200). **No `/pdf` or `/pdfft` capture exists.** reader.elsevier.com: zero captures | `wayback-cdx-sd*.json` |
| Wayback landing snapshot body | 200 HTML 111,950 bytes, sha256 `073ce2e4…73847`; abstract + navigation only, **no article body** | `wayback-sd-article-20221129.html` |
| api.fatcat.wiki lookup | Connection timed out (40 s, 60 s); host unreachable from this network | logged entry `api-fatcat-unreachable.txt` |
| scholar.archive.org search | 200 HTML but JS "Session Verification" challenge; stopped, no bypass | `scholar-archive-search.html` sha256 `5b2526ab…53879e` |
| BASE public search | Anubis bot-check challenge; stopped | `base-search.html` sha256 `f67e0bfb…c6abdb197` |
| CORE public search | Cloudflare 403 "Just a moment…"; stopped | `core-search.html` sha256 `b6a48970…8582858` |
| Preview-browser plain visit of the SD article page | Cloudflare "Just a moment…" persisted >20 s; stopped, no bypass, no captcha interaction | logged `preview-browser-sd-challenge.txt` |
| ResearchGate (Banica's own profile PDF link, found by search) | curl 403 "Temporarily Unavailable"; browser visit → explicit DataDome captcha; stopped, no interaction | `rg-banica-pdf.pdf` sha256 `abd1be90…441fabe64` + logged browser entry |
| ion.nechita.net/research/ (new host vs old nechita.net) | 200: links only DOI + arXiv for this paper; no hosted PDF | `nechita-ion-research.html` sha256 `038b49a7…f1522147` |
| Web searches for any public mirror of the published version (arXiv-only, DOI, PII, "24-46") | No journal-body copy exists anywhere public found; all hits are DOI landing, arXiv/ar5iv, MaRDI/Wikidata metadata, catalogs | search responseIds `mvrp20h9rtcfih`, `mvrp863o9kar9y` |
| MathDB 332493 current status | 200: `status: open`, `solutions: []`, `lean_formalization_count: 0`, references cite arXiv only | `mathdb-332493-current.json` sha256 `25b88021…92c847` |

No paywall, captcha, or challenge was bypassed; no key was acquired; no
account or browser profile was mutated; no author was contacted. Empty
solution arrays and open statuses are recorded as status facts, **not** as
novelty evidence.

**Conclusion of the source gate:** every legitimate route now tried is either
exhausted (HAL, Wayback, OA registries, author pages) or challenge-blocked
without bypass. The actual journal conjecture page remains unread. SOURCE
HOLD stands; the only legitimate closure routes are (a) an authorized copy
appearing in a public archive/repository/mirror, or (b) root explicitly
resolving the gap under its acceptance policy as a documented limitation.

## 3. Jung 2019 thesis: last unread record, now read (body screen)

Stefan Jung, *Easy quantum groups: Linear independencies, models and partition
quantum spaces*, Dissertation, Universität des Saarlandes, April 2019; DOI
10.22028/D291-28017. The SULB original is 403 (inherited). **New**: the exact
bitstream
`https://publikationen.sulb.uni-saarland.de/bitstream/20.500.11880/27621/1/thesis.pdf`
has three Wayback captures (2020-02-10, 2024-07-12, 2026-04-05) with the
**same digest `HNR2ZCFTC3IW3VRTAOUDNJJML7VL6O2O`**, i.e. an unchanged stable
public copy. Retrieved 2026 snapshot: 200, `application/pdf`, 1,604,019 bytes,
sha256 `881869dfc2b4c5192df1fa9d47a715974f80d6f054597c53eec957272945f2df`,
`%PDF-1.5`, 214 pages, text-extracted to `jung-thesis.txt` (sha256
`4934a58d…26125cb`). Title page confirms author/title/institution.

Relevance screen of the actual body (extracted-text searches + targeted
reads):

- **Sinkhorn: 0 hits. Moore (–Penrose): 0 hits. polar: 0 hits.
  "four projection(s)": 0 hits. arXiv 1602.04456: 0 hits.**
- `[BN17]` is cited once as bibliography `[BN17]` "Adv. Appl. Math. 83:24–46,
  2017" plus one body mention, PDF p.142 (printed p.132), which is an explicit
  disclaimer: "Another work asking for (specific) models of C(S_N^+), so
  called flat matrix models, is [BN17], but this chapter does not share with
  it more than this initial question."
- The thesis's own conjectures (Conjecture 4.7.12, PDF pp.~160–161) are: no
  compact matrix quantum group strictly between S_N and S_N^+, and equality of
  the inverse-limit model with S_N^+ — different endpoints.
- Remaining "rank"/"projection" occurrences concern intertwiner-map ranks
  T_p and representation decompositions, not projection trace normalization.

**Assessment:** the Jung thesis contains no normalization/descent theorem, no
four-projection trace inequality, and no subsuming statement. The disclaimer
is positive evidence the author did not develop [BN17]'s models further there.
This record is now covered by an actual body screen (not just abstract).
Limitation: this is a keyword/section screen with targeted reads of the
relevant passages (Chapter 4 model chain, Section 4.7 conjectures, §4.2
disclaimer), not a line-by-line proof audit of all 214 pages; the thesis's
provenance rests on the stable Wayback digest, not on comparison with the
live SULB file (403).

With this, **all 26/26 Semantic Scholar citation records have at least some
relevant-body coverage** (duplicates included; "some body coverage" ≠ "25/26
full papers read"). I also verified the coverage count inherited from r2 and
did not alter the astra lane's files; my update is this report plus saved
sources in my lane.

## 4. Independent novelty assessment

- No read source resolves, refutes, or subsumes the target inequality
  (normalized cross-trace bound Tr(P'Q')+Tr(R'S') ≤ Tr(PR)+Tr(QS), or the
  candidate's rank-free strengthening).
- Closest actual bodies remain those inventoried by the two prior reviews
  (1911.04912 §3, 1608.05811 App. A, de la Salle 2103.14126, Xu–Zhang
  2507.14940v2, LAPACK LN83, Makarov–Seelmann, Frank–Paulsen–Tiballi,
  Antezana–Chiumiento, plus the Banica-family corpus). I did not repeat their
  math; I found no new relevant matrix-analysis candidate this round beyond
  the Jung screen.
- MathDB 332493 (today): open, empty solutions, zero formalizations — status
  fact only, no novelty weight.
- **NOVELTY HOLD stands.** A bounded negative search can never certify
  worldwide priority; the journal body itself is unread, so what the journal
  states cannot yet be compared against prior art either.

## 5. Strongest remaining objections (against clearing the HOLDs)

1. **Journal body unread, and now known to postdate arXiv v3.** The published
   paper was revised (1 Sep 2016) after v3 (23 Jul 2016). Any v3↔journal
   difference (statement, numbering, added results, withdrawn conjecture)
   is possible until the actual page is read. No abstract, metadata, OA flag,
   or citation agreement can close this.
2. **Challenge-blocked hosts (SD/ResearchGate/BASE/CORE/scholar.archive.org)
   could legally contain readable copies** (the article is open archive);
   their content remains unknown, not known-absent.
3. **Coverage caveats**: viXra 2009.0045 (200 pp.) and several other long
   works received only targeted readings; historical/published variants were
   not all compared; Jung screen is keyword+targeted, not a full audit.
4. **Subsumption is never excluded by search**: a routine corollary of an
   unread source (e.g., a sharp polar-factor specialization with the
   PQ=RS=0 grading used as data) would defeat credit; none was found in any
   read body, but unaccessed bodies remain.

## 6. Precise remaining gap for root

Single decisive item: **an authorized reading of the published AAM 83 (2017)
24–46 conjecture page and its surrounding definitions** (journal numbering,
exact hypotheses, inverse-root convention, rank balances or their absence,
and whether it is stated as open). Everything else in the candidate's gates
(formal endpoint, replay, integrated review, paper) is root-controlled and
already in progress elsewhere. For novelty, no further blocking record is
known; the novelty HOLD can only be lowered by root policy (documented
bounded-novelty acceptance) or a positive prior-art find, not by more
metadata.

## 7. Provenance summary

All URLs, timestamps, HTTP statuses, content types, byte counts and SHA-256
values for this round are in `sources/retrievals.json` (26 entries, sha256
`645b36759da5d23c3797f8ebc6168712abdf5022269d315e79a8a94ab621e932`) plus the
files in `sources/`. This report: sha256
`2bcafea0434b977e0e22653e153778176a797a7c0492f55a75eafc11b6606a54`. Access
limits honored: no retry after any 429; no challenge, captcha, or paywall
bypass; no API key acquisition; no author contact; no account/profile
mutation; browser used only for plain public visits and closed after
challenge detection. Children started: 0. Git commands: 0. Files written
outside this lane: none.
