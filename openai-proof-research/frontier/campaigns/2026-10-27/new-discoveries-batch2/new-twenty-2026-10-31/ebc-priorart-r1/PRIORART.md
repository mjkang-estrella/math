# Prior-art retrieval: MathDB 337062 (Classes 4, 7 and 8 of Conjecture 2.1)

Lane: `ebc-priorart-r1` (Claude Opus 5.5). This is retrieval, not acceptance. Credit is zero and only root decides.

**Verdict: NOT OBTAINED.**

I could not read the body of the 2022 Theory and Applications of Graphs (TAG) follow-up by any legitimate open route. No passage on circulants, on Conjecture 2.1 or on C_n(1, a, b) could be quoted from it.

I found no other later document that proves, refutes, restricts or replaces Conjecture 2.1, or that treats Classes 4, 7 or 8. That is negative evidence only. It does not clear the unread 2022 body. The review lane's HOLD (`ebc-review-r1/REVIEW.md` §7) therefore stands unchanged.

## 1. Target document

J. Coroničová Hurajová, T. Madaras and D. A. Narayan, "Characterizing Edge Betweenness-Uniform graphs", Theory and Applications of Graphs 9(1) (2022), Article 5, DOI 10.20429/tag.2022.090105.

New metadata from this lane:

- **Length and indexing.** zbMATH Open has it as Zbl 1486.05071 (document 7510749): 11 pages, keywords "vertex betweenness" and "edge betweenness-uniform graph", MSC 05C12, 05C90 and 91D30.
  - zbMATH holds only the authors' summary, identical to the abstract. There is no reviewer text and no reference list.
- **CORE.** CORE indexes it as work 132695175, with outputs 524620253, 542663701 and 1009241916, harvested from the publisher, Crossref and DOAJ.
  - CORE's API reports `fullText: "Not available for public API users."`
- **Citations.** OpenAlex lists **zero** works citing it (W4220696407).

The abstract (CORE and zbMATH) is the only text I obtained:

> "… Graphs whose vertices all have the same edge betweenness centrality are called edge betweeness-uniform. It was recently shown by Madaras, Hurajová, Newman, Miranda, Flórez, and Narayan that of the over 11.7 million graphs with ten vertices or fewer, only four graphs are edge betweenness-uniform but not edge-transitive. In this paper we present new results involving properties of betweenness-uniform graphs."

The abstract says nothing about circulants, Conjecture 2.1 or any class.

## 2. Routes tried for the body

All requests used `scripts/fetch.py`:

- `python3 -I` urllib with default verified TLS, run under `ulimit -v 2000000; timeout 100`.
- No automatic redirects, and one attempt per URL.
- Each body went into its own fresh `dl/` directory.

Full receipts with sha256 are in `receipts/network.jsonl` and `priorart.json`. The table gives the first 16 hex digits of each sha256.

| UTC (2026-11-05) | URL | Status | sha256 (first 16) | Outcome |
|---|---|---|---|---|
| 08:14:51 | api.core.ac.uk/v3/search/works?q=title:"Characterizing Edge Betweenness-Uniform graphs" | 301 | 185995a6b134e760 | same-host trailing-slash redirect |
| 08:14:54 | api.core.ac.uk/v3/search/works/?q=… | 200 | 3e1363f8e59bb0ef | record found; full text "Not available for public API users"; download URL core.ac.uk/download/524620253.pdf |
| 08:14:57 | core.ac.uk/download/524620253.pdf | **403** | 1c69236237fb99f4 | Cloudflare "Just a moment" challenge; not retried; host abandoned |
| 08:15:47 | api.core.ac.uk/v3/outputs/524620253/download | 302 | c50a7d487ced4d83 | redirects to the denied core.ac.uk PDF; **not followed** |
| 08:15:28 | api.zbmath.org/v1/document/_search?search_string=ti:Characterizing edge betweenness-uniform | 200 | 7c09230015f9ea1a | summary only; no review |
| 08:15:34 | api.zbmath.org/v1/document/_search?search_string=betweenness uniform | 200 | 54f517894eaefbbf | 32 hits; see §3 |
| 08:16:00 | people.rit.edu/dansma/DNpublication_files/DNpublications.html (Narayan) | 200 | 6fccf97b50c458ca | old publication list; nothing on betweenness; no PDFs |
| 08:16:22 | www.math.fau.edu/combinatorics/narayan49.pdf | 302 | fe26af312fd7b692 | redirect to www.fau.edu, a host that had not denied; followed once |
| 08:16:25 | www.fau.edu/science/departments/mathcombinatorics/narayan49.pdf | 404 | 844bf5441d850d75 | not found |
| 08:16:28 | www.lehigh.edu/~ingsims/Abs_Spring2019/hector_miranda_abstract_1.pdf | 200 | bd30561f86e98294 | see §3 |
| 08:16:49 and 08:16:52 | lacuna.tiptreesystems.com/work/uniform-edge-betweenness-centrality | 301, then 200 | 6dc2df1a659e177b, bf2362072478777f | AI summary of the 2020 paper; see §3 |
| 08:16:57 | arxiv.org/pdf/2401.00347 | 200 | 6356a6890a513170 | no edge-betweenness or Narayan content |
| 08:17:09 | api.openalex.org/works?filter=cites:W4220696407 | 200 | 2786688be1d11914 | count 0 (my only OpenAlex request) |
| 08:17:14 | www.base-search.net/Search/Results?lookfor="Characterizing Edge Betweenness-Uniform graphs" | **403** | e3b0c44298fc1c14 (empty body) | not retried |
| 08:17:35 | ais2.upjs.sk/…/tomas.madaras.upjs.sk.html (Madaras, UPJŠ) | 200 | c00ce8354a61825c | profile lists cooperation with "USA (D. Narayan)"; no PDFs |
| 08:17:52 | www.upjs.sk/en/…/kosdim/information/publications/ | 200 | 3584c31f369da4eb | team list ends at 2018; no TAG entry |
| 08:18:09 | repository.rit.edu/theses/9802/ | 200 | 0827b8b74d253430 | Belchikova 2018 thesis record; see §3 |
| 08:18:13 | repository.rit.edu/cgi/viewcontent.cgi?article=10953&context=theses | **403** | 22236221c52f6c40 | Cloudflare challenge; not retried |
| 08:18:32 | arxiv.org/pdf/2105.06777 | 200 | 557968aff6e61eea | see §3 |
| 08:18:35 | arxiv.org/pdf/2609.09342 | 200 | 3e432715e4dd5a54 | see §3 |

**Routes not requested, and why:**

- **Barred by the brief:**
  - digitalcommons.georgiasouthern.edu, after its earlier 403.
  - The Wayback Machine, after its earlier 429.
  - ResearchGate, Academia.edu, Semantic Scholar, Crossref, the arXiv search API and Sci-Hub-like sites.
- **scholar.archive.org:** it serves its PDFs from archive.org, so it is futile under the Wayback bar.
- **Google Scholar:** it is a bot-challenge host.
- **Unpaywall:** it requires an email parameter, and the user's email may not be sent to services.
- **A second OpenAlex request:** not needed. The review lane already recorded that the only full-text location is the denied publisher host (`any_repository_has_fulltext: false`).
- **Coroničová Hurajová's current faculty (phf.euba.sk, University of Economics in Bratislava, Košice):** search shows only annual bibliographic registers there, and no full-text repository.

**Web searches.** I ran 14 queries, listed in `priorart.json`. All but one excluded the barred domains. The last two let the search engine draw on its own index of the publisher PDF. No result exposes any sentence of the TAG body about circulants or Conjecture 2.1. No result anywhere states that Class 4, 7 or 8 fails, or that Conjecture 2.1 is false or has been corrected.

One search summary claimed the 2022 paper "reportedly views a complete characterization of the non-edge-transitive cases as an ambitious problem". That is unverifiable machine text drawn from a truncated snippet. It is not evidence either way about Classes 4, 7 or 8.

## 3. Other later documents checked

These are the passages found. The page or line references point to this lane's `extract/` files.

- **Hector Miranda (co-author of the source), Lehigh 2019 one-page abstract** (p. 1; `extract/lehigh/miranda-2019.txt`, sha256 e88ece2f…):
  > "We have been able to identify infinite classes of circulant graphs that have uniform edge betweenness centrality but are not edge-transitive, including the 2-circulants C_{18n−3}(1, 6n) and C_{18n+3}(1, 6n), n ∈ N. In doing so, we develop an original method for demonstrating uniform edge betweenness centrality without making explicit centrality calculations."

  It covers only the two proven 2-circulant families. It is silent on Classes 3–9 and does not restate the conjecture.
- **Hartman–Pokorná, arXiv:2105.06777** (p. 2, `extract/a2105/t.txt` L70–71):
  > "There exist other studies concerned with both the values of betweenness in betweenness-uniform graphs[6] and edge betweenness-uniform graphs[8]."

  Reference [8] is the 2020 source. There is nothing on circulants or on Conjecture 2.1.
- **Ghanbari–Hartman–Jelínek–Pokorná–Šámal–Valtr, arXiv:2401.00347:** vertex betweenness only. It does not cite Narayan or the TAG paper.
- **Madaras–Paralič, "Betweenness centers of graphs", arXiv:2609.09342 (2026):** this is a later Madaras paper, but it cites neither the 2020 source nor TAG 2022. It contains no edge-betweenness or circulant content.
- **zbMATH "betweenness uniform" (32 hits):** the only edge-betweenness-uniform items are the 2020 source, TAG 2022 and M. Belchikova–D. A. Narayan, "On k-uniform edge betweenness centrality graphs", Congr. Numer. 231 (2018) 183–203. The rest concern vertex betweenness or are unrelated.
- **Belchikova, RIT MS thesis, 21 May 2018** (committee includes Narayan). The abstract studies graphs with exactly k = 2 or 3 distinct edge-betweenness values. The PDF returned 403, and the Congressus paper is not online.
  - Both items are unread.
  - Both predate the 2020 version of record, which reprints Conjecture 2.1 unchanged after peer review. So neither led the authors to withdraw or correct the conjecture.
- **Lacuna (AI-generated summary of the 2020 paper):**
  > "computational evidence suggests at least seven more classes of circulant graphs share this property. Future work remains to provide formal proofs for these conjectures"

  This is not scholarly evidence. It only treats the classes as open.

## 4. Answer to the brief's question

- **Does TAG 2022 prove, refute, restrict or replace Conjecture 2.1, or treat Classes 4, 7 or 8?** UNKNOWN. The body is unread, and no passage is available to quote.
- **Does any other later paper do so?** Among those reachable (zbMATH, CORE, OpenAlex citations, arXiv, the authors' institutional pages, web search), **none** does. TAG 2022 itself has no recorded citing works.
- **Classes covered by any obtained text:** only the proven C_{18n±3}(1, 6n) families, in the Miranda 2019 abstract. None of Classes 3–9 is covered.

## 5. What root needs

To close prior-art gate C, root needs the 11-page TAG PDF. The publisher copy is at `https://digitalcommons.georgiasouthern.edu/cgi/viewcontent.cgi?article=1219&context=tag`, and the CORE cache is at `https://core.ac.uk/download/524620253.pdf`. Both sit behind Cloudflare challenges for automated clients.

A non-automated route outside this lane would work, for example the user opening either URL in a browser. Once the text is in hand, apply the resolution rule in REVIEW.md §7:

- If the paper is silent on Classes 4, 7 and 8, the verdict becomes CLEARED and root may PROCEED.
- If it reports their failure or replaces the conjecture, the verdict becomes SUBSUMED and the candidate is EXCLUDED.

## 6. Integrity

- **Input hashes.** Inputs were hashed before (08:14:25Z) and after, in `receipts/input-hashes-before.txt` and `receipts/input-hashes-after.txt`. The two lists are **identical**:
  - REVIEW.md c185e2eb…fdbda
  - TASK.txt e7e751ee…d934
  - launch.json
  - the three AGENTS.md files
  - the review lane's network-receipts.json
- **No discovery-lane or review-lane scripts** were imported or run.
- **No computations.** I ran no Lean, lake, leanchecker, SAT or ILP. The only processing was `pdftotext` and small text parsing.
- **Write scope.** Nothing was written outside this lane.
- **Excluded actions.** I used no git, no child agents, no browser and no uploads.
- **OpenAlex notice.** One OpenAlex response suggested registering an API key with the user's email. I ignored it.

I do not self-accept. Root decides.
