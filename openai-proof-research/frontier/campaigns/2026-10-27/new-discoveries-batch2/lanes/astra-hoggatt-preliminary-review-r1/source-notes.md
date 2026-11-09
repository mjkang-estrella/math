# Source and bounded prior-art record

Access/review date: 2026-10-28 UTC. Live requests were read-only. No rate limit,
CAPTCHA, login, or access restriction was bypassed. A 403 and a timeout were
recorded rather than circumvented. Raw live responses are in `sources/` and
hashed in `provenance.json`; cached root sources remain at their frozen paths.

## Exact target and published comparison

* [Fang-Zhang-Zhao v1](https://arxiv.org/html/2505.05873v1): complete definition
  of M(k,l,m;q), H_n^[m], Theorems 1.2, 2.1, 2.2, Corollary 2.1, complete
  Theorem 1.2 induction, and Conjecture 4.1 read. Fresh official arXiv abstract
  and HTML saved. History shows only v1, 9 May 2025. The conjecture is
  positive integer q, m=2,3. The source proves q=1 for all m>=2. The use of
  the SAME G[N,m] in the old induction is substantive prior-art evidence.
* [Published article](https://www.sciencedirect.com/science/article/abs/pii/S0022247X26002271):
  publisher search-indexed introduction and section snippets read; current
  metadata give JMAA 561(1), 130615, 1 September 2026,
  DOI 10.1016/j.jmaa.2026.130615. The conclusion snippet still introduces
  three conjectures and discusses generalized Sturm for m=1, then the
  q=1 theorem. It truncates before the full new conjecture. Direct fetch
  returned 403. No claim of having read the complete printed Conjecture 4.1.
  Evidence: `web-search-bounded.json`, `web-final-primary-search.json`.

## The exact classical inputs

* [Garloff-Wagner original PDF](https://www-home.htwg-konstanz.de/~garloff/Garloff_Wagner_Hadamard_Products.pdf),
  Theorem 4, original p.800: actual indexed statement read in full, including
  both simultaneous exceptions in (c) and the gcd x^r conclusion. It agrees
  with FZZ Theorem 2.1. Direct PDF fetch timed out; no local original PDF
  hash or full-original-proof inspection is claimed. Evidence:
  `web-search-initial.json`, `web-access-failures.json`.
* [Lamprecht v1](https://arxiv.org/html/1210.1102v1): freshly downloaded whole
  primary HTML; Sections 2.1, 3, 5, 6, 7 read at the precise needed
  definitions and theorem/proof portions. Specifically read the definition
  of extremal, Wronskian order preceq, prec_0, the weighted coefficients,
  Equation (29), Theorems 25, 29, 30, and Theorem 30's strictness argument.
  Live history shows v1, 3 October 2012. Published as Adv. Math. 288 (2016),
  426-463, DOI 10.1016/j.aim.2015.10.016 (publisher metadata verified).
  The numbered theorem body used is the accessible arXiv version; a separate
  full published-body comparison was not performed. The decisive new
  review finding is the symbol computation in `classical-subsumption.md`.
* [Leake-Ryder v1](https://arxiv.org/html/1712.02499): cached primary full
  theorem text and proof in Section 3.2 read, especially Theorem 1.7,
  Proposition 3.6, recursive convolution identities, and Corollary 3.5.
  Fresh live history shows only v1, 7 December 2017. The introduction's
  Theorem 1.7 says negative roots whereas the operative Section 3.2 statement
  and proof use positive roots. Do not silently import its signs. The
  direct argument in the review instead uses Lamprecht's unambiguous
  Wronskian definitions and negative-root convention.
* [Martínez-Finkelshtein-Morales-Perales v1](https://arxiv.org/html/2606.15003v1):
  Sections 2.3-2.4, Propositions 3.4-3.5, Corollaries 3.7-3.8, Theorem 3.9,
  and its parameter-concatenation proof read from the frozen primary body.
  Fresh official abstract shows only v1, 12 June 2026; the manuscript body
  separately prints 24 August 2026. Both dates are recorded without assuming
  an unlisted second arXiv revision. The convolution weights and sign rules
  differ from ordinary Hadamard multiplication. Theorem 3.9 alone is not a
  direct strict successive-N theorem for F[N,m]. Corollary 3.7 explicitly
  uses dilation-interlacing to preserve mesh, further showing that this
  invariant mechanism is standard. No exact Hoggatt statement located.

## Original Hoggatt context and current companions

* [Dilks thesis](https://www-users.cse.umn.edu/~reiner/DilksThesis.pdf),
  Section 3.1, Definition 3.1, Section 3.2 Theorem 3.8 and its proof: read
  from the frozen complete PDF with independent text extraction. Printed
  pages 45-46 (PDF pages 53-54) rendered and visually inspected. Theorem 3.8
  states only H_n^[m](1,t) real-rooted for all m. Its shifted/reversed
  ordinary multiplier-sequence proof does not assert q>1 interlacing.
  The PDF hash is the original frozen hash; no new retrieval is claimed.
* [Mao-Shi](https://arxiv.org/html/2607.01582v1), Definition 1.1 and Theorem 2.4
  plus its proof read. The coefficients are determinants of ordinary Pascal
  entries; the theorem gives infinite row/column log-concavity and uses
  q=1 row real-rootedness. Introduction credits FZZ's ordinary interlacing.
  Fresh official history shows v1, 2 July 2026. Not the two-variable Sturm
  endpoint.
* [Liu-Mao](https://arxiv.org/html/2608.22258v1), Section 6.3, Theorems 6.6-6.7
  and definitions/proofs read. The coefficients are
  q^(d k(k-1)/2) prod_j [n+j choose k]_q/[k+j choose k]_q. The theorems
  assert coefficientwise q-log-concavity for fixed n or k, not interlacing
  of row polynomials at fixed q. Fresh history shows v1, 23 August 2026.
* [Chern-Shi strong log-convexity](https://arxiv.org/html/2609.33732v1),
  Theorems 1.1-1.4, definitions, and relevant Schur specialization read.
  In Theorem 1.2, the variable named q is the ordinary row-generating
  variable, not the source's additional area parameter. Theorems 1.3-1.4
  use the same refined coefficients as Liu-Mao and give strong coefficient
  q-log-concavity. These are closely related coefficients, not unrelated
  just because notation differs: with n_source=n+1 and m=d, multiplying
  their kth coefficient by q^(d k) gives the coefficient of the candidate
  H_n_source^[d](q,t). Their stated conclusions still do not supply root
  interlacing. Fresh official history shows v1, 27 September 2026.
* [Chern-Shi Cigler proof](https://arxiv.org/html/2606.26950v1), definition and
  Theorem 1.1 read. It identifies a column generating numerator with a
  rectangular standard-tableau statistic and proves polynomiality,
  nonnegativity, and palindromicity. It solves Cigler's different conjecture,
  not FZZ's row Sturm assertion. Fresh official history shows v1,
  25 June 2026.

## Registries and possible public resolutions

* Fresh [MathDB API record 368343](https://mathdb.com/api/posts/368343) read
  in full; at retrieval it had an open label and empty solution/comment
  arrays. This is an inventory fact, NOT novelty evidence. Its additional
  references 2403.19692 and 2212.10586 were checked from cached actual bodies.
  The former is a general split-polynomial criterion, the latter a different
  Dyck/Narayana refinement. Neither is an earlier statement of this Hoggatt
  conjecture. No downstream claim is based on the record's mistaken 2022
  provenance date.
* The frozen public GitHub issue search returned RealRooted issue 1332.
  I freshly fetched and read all 16 comments, including
  [the full two-sided Jensen comment](https://github.com/PerAlexandersson/RealRooted/issues/1332#issuecomment-6110661167).
  It treats ordinary A056939/Baxter coefficients and mentions higher Hoggatt
  orders as consumers. Its gamma/delta reciprocal-Pochhammer formulas give
  the q=1 specialization. They do not contain the Gaussian q parameter.
  This is not an exact q>1 public resolution. I did not audit every file of
  the repository or certify its Lean claims.
* The frozen formal-conjectures Hoggatt issue search had zero results. A
  zero issue count is NOT evidence that the code corpus lacks a theorem.
* Read the parent and campaign rules, full ledger JSON and prior campaign
  JSON; checked prior accepted titles and relevant old lane notes. There
  is no q-Hoggatt duplicate among the first thirty listed outcomes. Old
  BBK notes concern a different unresolved target and confer no credit here.
* Read-only searches included exact source title, source identifier,
  Hoggatt/Sturm/q/interlacing, Hoggatt/Lamprecht, q-Narayana real roots,
  public GitHub Hoggatt proof and Ideosphere Hoggatt. The saved search
  responses identify positive hits. No earlier explicit full q>1 Hoggatt
  solution was located. Unrelated search results were discarded.

## Limits

This is a bounded public-source check, not a systematic citation-index,
all-language, private-repository, or unpublished-manuscript survey. Full
FZZ journal text and the full original GW proof were inaccessible during
this review. Search indexing can be stale. The absence of an explicit
endpoint in the reviewed corpus is not a worldwide-priority claim.

The substantive recommendation does NOT rest on an empty registry, failed
search, inaccessible source, or a guess from an abstract. It rests on the
exact old-theorem specialization and complete FZZ-induction bridge in the
companion note. The distinction between an apparently new explicit
application and a campaign-eligible nonroutine discovery is left explicit.
