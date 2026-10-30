# Astra analysis r2: no eligible new outcome

**Disposition: 0 new outcomes; no acceptance requested.** All writes stayed in this lane. No child agents, git operations, shared-ledger changes, external messages, accounts, or postings.

## Main deep attack: Kellner370182 — EXCLUDE

Actual primary source: Kellner, *Wilson's theorem modulo higher prime powers I: Fermat and Wilson quotients*, arXiv2509.05235v1. Read the exact Theorem4.1 recurrence, Remark4.5, Conjecture4.6, and source polynomial tables.

Independently derived a complete all-variable formula, before locating the successor:

    sum_{n>=1} psi_n(X) t^n/n!
      = 1-exp(-(sum_{j>=1}(-1)^(j+1) X_j t^j/j)/(1-t)).

For multiplicities m with d=sum m_j>0 and w=sum j*m_j<=n, the coefficient is

    (-1)^(w+1) n! binom(n-w+d-1,d-1) / product(j^m_j m_j!).

This proves the specializations, full partition support, and the weight/noncancellation assertions. Full ordinary proof in PROOF.md, including exact source recurrence resummation and all quantifiers. Direct symbolic comparison with the source's independently implemented double Stirling–Bell recurrence passes n1..8; every monomial coefficient and the support count also checked exactly. These finite checks supplement, not replace, the ordinary proof.

**Decisive prior art:** Yutaro Matsuno, *A resolution of Kellner's conjectures on Wilson quotients*, arXiv2607.10106v1, submitted11July2026. Actual complete theorem/proof body read; PDFpp2--3 inspected visually. Theorem1.3 states exactly the same full multivariate Bell formula AND every-monomial formula. Corollary1.7 identifies these with Kellner's polynomials; Corollary3.1 proves both specializations and exact partition support. The remaining Remark4.5 deductions are immediate consequences of that complete prior formula. Alternate recurrence resummation earns no new-result credit. No salvage as separate support, coefficient, weight, specialization, or helper outcome.

Relevant sources are saved as sources/psi.html, psi-pdf.pdf, psi2.html, psi3.html, matsuno.html, matsuno-pdf.pdf, matsuno.txt. Exact URLs, retrieval statuses and SHA256 hashes are in provenance.json and sources/fetch-log*.json.

## Other screened targets

- **368201 Laguerre divisibility: EXCLUDE.** Actual current source2504.20324v2, revised16September2026, Theorem3 states L_k divides L_n^(m) implies n=k,m=0, exactly the target. Theorem statement and Section6.6 proof inspected. This is an exclusion of already posted work; no claim of external Lean verification.
- **357703 VG median: EXCLUDE.** Actual Gaunt–Ouimet2609.20212v1 Corollary2.3 equations2.6--2.7 gives the exact bounds with location0; translation restores mu. Read the exact statement and Section4.3 concluding derivation. No claim to have independently certified the whole probability proof.
- **372545 Henry: duplicate prior exclusion.** Same Gao–Guo2601.09276 source family as prior372380; not pursued as a new target.
- **376978/376979 Horwitz: unresolved, no result.** Exact sourceConj15--16 inspected; repeated-input reduction to a single scalar logarithmic residual and its equality for both directions saved in HORWITZ-GAP.md. No global sign proof. Exploratory500-point precision80 tests found no violation. Published source request403 respected; this is a material source/prior-art gap.
- **365327,379441,379442:** records inspected only; no proof, exclusion, or novelty conclusion asserted. Mittag published PDF retrieved but not fully analyzed.

## Formal result and exact limits

formal/ExclusionCore.lean compiles with the requested Lean4.34.1 binary and supplied mathlib libraries. The public types and actual axiom sets are recorded in formal/ExclusionCore.log; all four elementary results use only subsets of the standard three. This is an initial partial module for an EXCLUDED lead. It does NOT prove the literal all-degree source endpoint. formal/README.md names every missing bridge. No helpers are counted. No paper, packet, or extracted-replay acceptance claim.

## Bounded prior screen

Read actual original and two Kellner companion bodies, then the decisive Matsuno successor. OEISA347978/A073478 full internal records give known generating functions and cite Kellner, but were not treated alone as source-polynomial proofs. Inspected current author publication page (appears incomplete, stops listing publications at2024). SemanticScholar citation request429 was not retried. Saved Ideosphere homepage and current public formal-conjectures/trureturing tree snapshots; literal Horwitz/Stolarsky/Kellner/target-ID searches gave no matching entries. These are limited index/filename screens, not exhaustive full-code searches. Web searches were incomplete initially and only a later exact arXiv-ID query found Matsuno. No universal priority certification.

## Next useful work

Do not re-formalize or recount Kellner. If continuing Horwitz, first reconcile the actual2002 published body and closest comparison literature, then attack the exact scalar residual or full two-parameter pairwise inequality. A negative certified residual would refuteConj16, but not automaticallyConj15. All precise remaining gaps are documented rather than asserted solved.
