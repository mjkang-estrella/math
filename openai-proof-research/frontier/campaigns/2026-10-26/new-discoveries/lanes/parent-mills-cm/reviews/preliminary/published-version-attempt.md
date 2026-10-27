# Published-version access attempt (review lane, 2026-10-26)

- Crossref API https://api.crossref.org/works/10.1090/tran/8748 (HTTP 200, archived:
  crossref-10.1090-tran-8748.json): "Convolution of beta prime distribution",
  Trans. Amer. Math. Soc. 376(2), 855-890, online 2022-12-01. Crossref abstract is
  word-identical to the arXiv v2 abstract.
- Crossref lists two PDF links (VOR and accepted-manuscript). Both
  (www.ams.org/tran/2023-376-02/...) return HTTP 200 but serve a cookie-consent
  HTML wrapper, not PDF content (soft publisher block). pubs.ams.org home.html is
  an 11 MB JS shell with no extractable conjecture text.
- Project Euclid full-text URL: 1 KB HTML shell only.
- Conclusion: the published-body comparison remains a MATERIAL LIMIT, same as the
  parent recorded. The arXiv v2 (19 May 2022, "Minor corrections. To appear in
  TAMS") is the latest version; its pp.29-31 were independently rendered and read
  (sources-rendered/page-29..31.png). Conjecture 3 statement, its "for every
  integer n" quantifier (n=0 included), the plain (no sqrt) argument, the CM
  convention on (0,infinity), and the normalization r(x)=e^{x^2/2}\int_x^inf
  e^{-t^2/2}dt with r(0)^2=pi/2 were all verified against the rendered pages.
