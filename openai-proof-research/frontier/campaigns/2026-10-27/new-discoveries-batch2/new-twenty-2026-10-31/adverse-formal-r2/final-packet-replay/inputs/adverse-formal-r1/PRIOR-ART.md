# Prior-art gate: HOLD, not cleared

Checks performed on 2026-11-02 UTC (2026-11-01 America/Los_Angeles).
No prior refutation was identified in the inspected material. This is not a
claim that none exists. Required body coverage and current registry coverage
remain incomplete. Phase 2 was not started.

## Source fidelity

The hash-bound survey arXiv:1811.05516, section 3, equation (11), defines the
quadratic objective using H = A / (−λmin). Q means α = υ. Section 4 defines
adversity for a graph without isolated vertices, with integral υ and λmin,
and with both unchanged after deletion of every open neighbourhood. Its
Conjecture 4.2 quantifies over all adverse graphs. No connectedness hypothesis
or prohibition on isolated vertices in the deletion is imposed there. In
fact the retained vertex itself is isolated after deletion of its open
neighbourhood. The ambient discussion assumes at least one edge. The
candidate has edges and no isolated vertices. It is connected: row and column
moves connect any two cells (ordinary observation, not a Lean theorem).

The survey's sentence asserting H itself is positive semidefinite after
(11) is inconsistent with its negative eigenvalue; H + I is the positive
semidefinite matrix needed. The formula, rather than that sentence, governs
the intended statement. No change to the formula is proposed.

## Body material retrieved and inspected

1. Cardoso–Luz, CM01/I-17: author-hosted PostScript
   https://sweet.ua.pt/dcardoso/WebReports/CardLuz01.ps . Converted locally to
   PDF and extracted text. The retrieved file is a revised body extending to
   page 21, although the survey describes an 18-page report. Introduction,
   definitions around equations (8)–(11), and conclusions on pages 19–20
   were read. They describe the adverse obstruction and leave the existence
   of an adverse non-Q graph open. This is targeted body reading, not a claim
   to have audited every proof in the report.
2. Cardoso–Luz, J. Combinatorial Optimization 31(1) (2016), 311–326:
   https://sweet.ua.pt/dcardoso/WebReports/CardosoLuz_JOCO2014.pdf . Author
   manuscript, 16 pages. Definitions 1–2, the quadratic program, section 4,
   Proposition 1, the star-solution results, computational Table 1, and
   conclusions were inspected. Section 4 and the conclusions retain the
   adverse-implies-Q conjecture. The tested graphs in Table 1 are all Q.
   No Latin-square counterexample was found in these inspected passages.
3. Cardoso–Lozin hereditary-properties paper:
   https://sweet.ua.pt/dcardoso/WebReports/LozinCard99.pdf . This is a 1999
   report version, not independently verified identical to the 2012 journal
   article. Its body was read: it characterizes a maximal hereditary subclass
   through P4 and Paw, and supplies examples outside Q. Those examples are
   not asserted to be adverse. It does not clear the journal version.
4. Cardoso–Lozin–Luz–Pacheco, Efficient domination through eigenvalues:
   https://sweet.ua.pt/dcardoso/WebReports/EfficientDomination.pdf . Body
   downloaded and targeted passages on regular sets, star complements and
   cited QP results screened. This author file contains unresolved draft
   cross-references. It is not a substitute for complete later-literature
   coverage or a verified final published body.
5. Cardoso's 17 May 2024 seminar announcement:
   https://api-portal.ua.pt/api/v1/file/79665 . One-page body read. It still
   describes the Q-graphs conjecture as open. Its displayed QP sign and bound
   inequality have apparent typographical errors compared with the survey.
   Use it only as dated evidence of the author's reported open status, not
   as the formal statement or a proof of novelty in November 2026.

## Material not cleared

- Luz 1995, DOI 10.1016/0167-6377(95)00042-9: no lawful full body located.
  OpenAlex reports closed access and no full-text repository. This metadata
  does not establish the contents of the paper.
- Cardoso 2001, DOI 10.1023/A:1011276123981: same full-body gap.
- Cardoso 2003: author PDF retrieved from
  https://sweet.ua.pt/dcardoso/WebReports/MatContempor%E2nea25_2%282003%299-24.pdf .
  Text extraction is severely corrupted (3,606 unexpected control characters).
  The body is NOT marked read. The survey's bibliography gives volume 21;
  the author's publication list gives volume 25. Preserve this discrepancy.
- Pacheco–Cardoso 2009, Recognition of Graphs with Convex Quadratic Stability
  Number: repository download returned 403. No retry. Search output exposes
  initial body text but that is not full-body clearance.
- **Material later source:** Luz, New results for recognizing convex-QP
  adverse graphs, DOI 10.1080/02331934.2018.1556664, online 2019, Optimization
  69(1). Publisher body route returned 403. No retry. OpenAlex reports no
  repository full text. The abstract is insufficient to exclude an earlier
  adverse non-Q construction or a directly subsuming criterion.

## Citation and counterexample searches

Queries included adverse graphs with counterexample, refuted, false, Latin,
strongly regular, and the Cardoso/Luz names; exact survey title and arXiv ID;
convex-QP with counterexample; and later Pacheco/Luz recognition papers.
Search outputs retained in logs are discovery aids, not body evidence.
No positive refutation hit was identified. The search is bounded and noisy.

OpenAlex exact-title lookup returned two survey records, each reporting zero
citing works. A direct cites query for W2893291471 likewise returned zero.
That index result does not prove the absence of citing works. The 2020 special
issue editorial was identified as discussing the survey and Luz's later
paper. Its PDF route returned 403; no retry. Full citation coverage therefore
remains unresolved. No Crossref, Semantic Scholar, arXiv search API, MathDB,
Palomar or previously denied ScienceDirect route was requested.

## Registry checks and limits

Only /commits/HEAD was requested from each GitHub registry. Receipts preserve
responses and hashes. openai/math current HEAD agrees with the assignment:
4eaee87548250b2682affda7d05d947c05554bae. Omega current HEAD is
78ddfa99b47453f621206e8077527819f2db78a7, newer than the supplied
 e26965e84ef74f66ce64631e23f293569195a4c1 snapshot.

Complete cached Omega D5 and Problems lists at the inherited snapshot were
screened (13,418 and 1,643 entries; neither marked truncated). Hits and blob
identities are in receipts/registry-path-screen.json. Latin/tableaux and
Latin-Eulerian paths occur; no adverse/Cardoso/QP path was found. Path hits
are not body clearance. The cached OpenAI preprint list has 13,223 entries,
untruncated, but the ancestor upstream.json binds it to the older
fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb context. It is NOT certified current.
The broad substring Latin also matches Simulating; those are false positives.

The commits/HEAD-only restriction was interpreted literally: no tree or raw
body requests were made to these registries. Consequently no complete CURRENT
D5/Problems/preprints screen can be certified from these responses. This is
an explicit unresolved gate requirement, not a clean novelty result.
