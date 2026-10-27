# Source-access report — Horwitz 1996 (JMAA 200, 126–148) actual body

Lane: `pi-horwitz-source-access-r2` (solo, no children, no git staging/commits, no counts, no external contact).
Task: locate and read the ACTUAL full body of Horwitz, "Means, Generalized Divided Differences, and
Intersections of Osculating Hyperplanes", J. Math. Anal. Appl. 200(1) (1996), 126–148,
DOI 10.1006/jmaa.1996.0195, and assess whether it contains a general closed form (or remark) that
immediately supplies the intersection last coordinate for α(t)=(t, t², …, t^{n−1}, log t).

**Verdict: BODY STILL UNREAD (22 of 23 pages). HOLD must be retained.** One genuine page of the
actual published paper (p. 126: header, title, author, abstract, start of introduction) was read and
rendered from a public document-share viewer; the remaining pages are behind an explicit anti-bot
captcha (`safe-captcha` slider) plus a points/login paywall on that site, which I did not bypass.
No legitimate full-text copy exists anywhere I could find, online or archived.

## 0. Exact metadata (verified from Crossref/OpenAlex/zbMATH/doc88 page 1)

- Title: "Means, Generalized Divided Differences, and Intersections of Osculating Hyperplanes"
- Author: Alan Horwitz, Pennsylvania State University, 25 Yearsley Mill Road, Media, PA 19063
  (email in paper: ALH4@PSU.EDU). Submitted by Bruce C. Berndt; received June 9, 1995.
- Journal: J. Math. Anal. Appl. 200(1), 126–148, May 1996 (cover date 1996-05-15).
  Article no. 0195. PII S0022-247X(96)90195-X. © 1996 Academic Press, Inc.
- zbMATH: Zbl 0848.26011 (reviewer J. Aczél).
- Open access status: **bronze/free at publisher** — Elsevier API `openaccessArticle: true,
  openaccessType: Full`, `openArchiveArticle: true`, user license
  `http://www.elsevier.com/open-access/userlicense/1.0/` (vor, delay 6286 days); Unpaywall
  `is_oa: true, oa_status: bronze, has_repository_copy: false`. **The article is free; the only
  access barrier is Elsevier Cloudflare bot-protection, not a paywall.**

## 1. Routes attempted and exact outcomes

1. **ScienceDirect PDF** `https://www.sciencedirect.com/science/article/pii/S0022247X9690195X/pdf`
   (and with GS-signed `?md5=5c49adc01645eeaf96f494b4201f10ff&pid=1-s2.0-S0022247X9690195X-main.pdf`):
   HTTP 403, Cloudflare error box "CLOUDFLARE_ERROR_1000S_BOX", ref a511bcf1c8e533fc. Same 403 with
   full browser headers and with the signed GS deep link (1.2 MB HTML error body saved as
   `sd-signed-403-error.html`, `sd-direct-attempt.html` — HTML, never passed off as PDF).
2. **ScienceDirect article page in a real (Electron/Chrome) browser**: "Are you a robot? Please
   confirm you are a human by completing the captcha challenge below." (ref a5122c89be8612b6 /
   a51219b5ab652510). **A real captcha — not solved.** Same result on the signed PDF URL.
3. **Elsevier API** `api.elsevier.com/content/article/pii/S0022247X9690195X`: metadata-only coredata
   XML without a key (already in parent sources); `?httpAccept=text/xml|text/plain` → 401
   "Invalid API Key". Same for the 1995 companion (PII S0022247X85711523).
4. **OpenAlex content endpoints** `content.openalex.org/works/W2046808613.pdf` and `.grobid-xml`
   (record says `has_content: {pdf:true, grobid_xml:true}`): 401 `{"error":"API key required"}`.
   Key is free-registration self-service; creating an account was out of scope.
5. **Unpaywall**: only OA location is the publisher PDF; `has_repository_copy: false`.
6. **Semantic Scholar**: `openAccessPdf` = the same blocked SD URL; paper `d77f90cf…`;
   citation-contexts endpoint returned no theorem text from the 1996 body (saved `s2-citations.json`).
7. **Scite**: 404 (no record).
8. **Internet Archive / Wayback** (intermittently offline this session; retried until clean):
   CDX for the exact article page URL and the exact PDF URL both returned **HTTP 200 with zero
   records** (`cdx-articlepage.txt`, `cdx-articlepdf.txt`). No captures of the old-style
   `science?_ob=ArticleURL&_udi=S0022247X9690195X` URL either. Fatcat API and scholar.archive.org:
   connection timeout (IA outage).
9. **Google Scholar** (real browser): the paper is result #1 (cluster 1984161048718086377) with
   "[PDF] sciencedirect.com" as the only PDF link; "All 4 versions" are citation-only entries
   (Pascal-Francis INIST, Web of Science). GS **"Quick read"** (article view
   `?output=aa&q=info:6RACFvYniRsJ`) loads only a title stub with no extractable text.
10. **OpenAIRE API**: no repository instance; all links are DOI/zbMATH (`openaire.xml`).
11. **CORE**: Cloudflare 403 on search UI.
12. **Search engines** (Google Scholar, Bing incl. real browser, DuckDuckGo html/lite, Mojeek,
    Ecosia, Yandex, Jina reader, Exa/DDG via web_search tool): the **only full-text mirror found
    anywhere is doc88.com** (see §2). No scribd/yumpu/vdocuments/other doc-host copy surfaced.
    No author homepage found (PSU personal-page guesses 404/timeout; ResearchGate 403 to agents).
13. **arXiv**: full listing of au:"Horwitz Alan" — no 1995/1996 arXiv version. Downloaded and read
    Horwitz 2000 "Invariant Means" (math/0007095v1, 28 pp., saved PDF+txt): it is about
    invariance of means, cites the 1996 paper as [6], and contains **no restatement of the 1996
    theorems and no closed form for intersection coordinates**.
14. **zbMATH Open API** (`api.zbmath.org/v1/document/_search`, saved `zbmath-api2.json`): full
    review text of Zbl 0848.26011 (see §3).
15. **CAPES portal** (periodicos.capes.gov.br, a legitimate library aggregator): content requires
    Brazilian federation login — private credentials, excluded.
16. **Springer** (Ait-Haddou–Mazure 2016 PDF, Ivan–Neagos 2021): "Client Challenge" bot-block in
    both curl and the real browser. (The preliminary reviewer already read the 2016 paper in full
    via an OA route: blossoming in polynomial Müntz spaces — power functions only; log t outside.)

## 2. The one partial body read: doc88.com page 1

`https://www.doc88.com/p-9922136151694.html` — user upload (ss55863360, 2015-11-03), format PDF,
**23 pages** (matches 126–148 exactly). Its public viewer renders page 1 free of charge; I
extracted that canvas render and read it (`renders/doc88/page1.jpg`, JPEG from the viewer canvas,
NOT a PDF and never claimed to be one). Page 1 verified: exact title, author/affiliation,
"JOURNAL OF MATHEMATICAL ANALYSIS AND APPLICATIONS 200, 126–148 (1996), ARTICLE NO. 0195",
"© 1996 Academic Press, Inc.", received June 9 1995, and the full abstract.

**Content of the actual abstract (transcribed from the render):** defines means in n variables as
the intersection of n osculating hyperplanes to a curve in R^n; "Under certain assumptions on the
component functions x_k(t) of C, the O_k will have a unique point of intersection P=(i_1,…,i_n).
Furthermore, a_1 < x_k^{-1}(i_k) < a_n for k = 1,…,n. This defines n symmetric means M_k";
examples: x_k(t)=t^k ⇒ M_1 = arithmetic, M_n = geometric; x_k(t)=t^{−k} ⇒ M_1 = harmonic;
**x_k(t)=t^k, k=1..n−2, x_{n−1}(t)=log t, x_n(t)=1/t ⇒ M_n = L, Pittenger's logarithmic mean**
(Amer. Math. Monthly 92 (1995) 99–104). **No identric curve and no closed form appears.**

Pages 2–23 (theorems, proofs, remarks, final section) are gated by an explicit
`safe-captcha` slider ("请拖动滑块继续阅读") and download needs 2000 points/login. **I did not
bypass the captcha, the points system, or any credentials.** doc88 is also not a publisher/author/
library copy; it is recorded as existence-and-page-1 evidence only.

## 3. What legitimate secondary evidence says about the 1996 body

- **zbMATH review (Zbl 0848.26011, J. Aczél), full text obtained:** the paper offers "a new mean
  value theorem for functional determinants of extended complete Chebyshev systems" and "a result
  stating essentially that under certain assumptions the n osculating hyperplanes … intersect in a
  single point. This defines n mean values which generalize several known ones (arithmetic,
  geometric, harmonic, logarithmic, etc.)". **No closed form mentioned.**
- **Author's own 2014 account** (JCA 4(1) 41–61, stored by parent; re-checked in `osculating-published.txt`
  lines 37–95): restates 1996 Theorem 1 as existence + uniqueness + internality of the intersection
  and defines M_k = x_k^{−1}(i_k); the only logarithmic example attributed to 1996 is the Pittenger
  curve (t^k, k=1..n−2; log t; 1/t) ⇒ M_n = L; and "At the end of [1] we stated that perhaps
  another interesting generalization … would be M_1 … where x_k(t) = t^{k−1} log t … We never
  pursued that". No closed form is attributed to [1] anywhere in the 2014 paper.
- **Page-1 abstract (actual 1996 paper, read):** same shape; all worked examples are monomial,
  reciprocal-monomial, or the Pittenger curve; the identric curve (t, t², …, t^{n−1}, log t) is
  absent from the abstract and (per the 2014 account and the "we never pursued that" remark) from
  the paper's stated examples.

## 4. Theorem-page assessment (conditional on body remaining unread)

**Strongest objection to novelty.** The title's "generalized divided differences" is the
Mühlbach-type ECC machinery. If the 1996 body contains a determinant-ratio representation of the
intersection coordinates — e.g. i_k expressed as a Wronskian/Vandermonde ratio of the component
functions (a "generalized divided difference of x_k" over the nodes), which is the natural companion
to its mean-value theorem — then for the curve (t, t², …, t^{n−1}, log t) the last coordinate could
be an immediate evaluation of that formula (reducing to the same Vandermonde quotient
Σ_i a_i^{n−1} log a_i / ∏_{k≠i}(a_i−a_k)), and the candidate would be an excluded immediate
specialization (tool, not theorem). Additionally, a closing remark of [1] proposes the curve
x_k(t)=t^{k−1} log t (per the 2014 account), so the body may contain further unexplored curve
remarks adjacent to ours.

**Counterpoints actually read.** (a) The actual page-1 abstract presents the paper's outcome as
existence/uniqueness/internality plus worked monomial/Pittenger examples — no closed form, no
identric curve. (b) The zbMATH review describes exactly that and nothing more. (c) The author's own
2014 paper, which needs the IZ identification, still poses it as a conjecture and attributes to [1]
only Theorem 1 (existence/uniqueness/internality) and the Pittenger example. If a closed form for
the intersection coordinates had been available in [1], the 2014 paper's display of IZ for the
n=3 case (credited to Stolarsky) and its conjecture would be hard to explain.

**Net:** the probability that the 1996 body subsumes the candidate is now low, but the theorem
bodies, section examples, and final remarks (pp. 127–148) remain unread, and the task standard
forbids counting on abstracts/reviews/author accounts. **Novelty HOLD must be retained.**

## 5. Recommended next routes (for the parent)

1. Human browser session (the operator, not the agent) on ScienceDirect — the article is free
   (bronze OA); any normal browser/persona passes the Cloudflare check. This is the cheapest
   definitive close-out. PDF filename: `1-s2.0-S0022247X9690195X-main.pdf`.
2. A human doc88 session could also read pages 2–23 (drag slider by hand; page 1 is verified to
   match the published paper), though publisher access is preferable.
3. OpenAlex content API (free key) would give GROBID XML of the publisher copy.
4. Any interlibrary-loan / library-proxy copy of JMAA 200(1) (1996) pp. 126–148.

## 6. Integrity

Own lane only; no parent/shared edits, no staging/commits, no counts, no external contact, no
credentials, no captcha bypass, no person contacted. All artifacts in `sources/` and `renders/`;
HTML error bodies are named `*.html`, never `.pdf`. The doc88 render is a JPEG from the public
viewer canvas, labelled as such.
