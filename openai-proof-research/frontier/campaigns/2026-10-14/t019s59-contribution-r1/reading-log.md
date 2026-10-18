# T019S59 contribution review r1 — exact reading log and limits

Distinction: "read" below means I read the actual statement/proof body in the
retained private copy during this review. "Credited, not audited" means the
result is used as a paid boundary input whose proof I did not examine.
Reviewing the author's r59/r60 reading claims is out of scope; this log records
only my own reading.

## Author packet (public files, all read in full)

`original-scope.md`, `candidate-proof.md`, `cyclic-collars.md`, `comparison.md`,
`reading-limits.md`, `checkpoint.md`, `verify.py` (read before execution),
`primary-identities.json`, plus hash-level checks of `manifest.json`,
`source-identities.json`, `source-family-inventory.json` (schema and anchor
fields inspected; the 32-blob/47-entry completeness cross-check was executed by
the packet verifier, not recomputed entry by entry by me).

Historical author context read in full: r59 `proof-attempts.md` (equivariant
patching, Brauer repair, restricted Pop-Stix plan, conditional endgame). r59
scope read via the byte-identical r60 copy (anchor match).

## Source manuscripts (pinned fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, stipulated true)

- The-p-adic-section-conjecture-October-6-2026: sections 01 (introduction), 02
  (preliminaries), 03 (patching: local normal form, prop:patching,
  point-transfer, horizontal-closure), 04 (tame-roots: annular-unit,
  stable-edge-root, etale-collars, first stage), 05 (arbitrary-roots:
  division-roots, auxiliary cover), 06 (realization: full completion proof), 07
  (sections: decomposition comparison, no-rank-one-section, surjectivity,
  injectivity) — all read in full. Section 08 (global consequences) NOT read
  (declared non-operative by the author; consistent with the local target).
  Figures, main.tex, README, references.bib not read (non-mathematical for this
  review).
- The-p-adic-section-conjecture-September-24-2026: not separately read. The
  author's byte-identity claim for its sections against October 6 was not
  re-verified by me and is not load-bearing for this review (the October 6 body
  is the operative interface I read).
- Etale-covers-with-a-prescribed-exterior-sheet-September-24-2026: section 01
  (statement) read in full; sections 02-04 NOT read. Non-operative: r59
  determined the solvable exterior-monodromy exploration is already paid and it
  is excluded from the claimed contribution.
- sources upstream.json / CONTENTS.md / preprints-tree.json: inspected at the
  packet's private copies for the verifier's pin/tree checks; I did not
  independently re-enumerate the 13223-entry canonical tree.

## Primary bodies (private copies; statements read as indicated)

- Mochizuki, Comments on a Combinatorial Version of the Section Conjecture and
  the Main Theorem of Pop-Stix (March 3, 2011): full 301-line extraction, all
  of (1)-(5) and bibliography. Read in full.
- Mochizuki, Comments on Valuations Associated to Systems of Vertices/Edges and
  the Main Theorem of Pop-Stix (May 2, 2011): full 187-line extraction,
  including the complete (*val) proof (1)-(2). Read in full.
- Pop, MPIM 2007/102: extracted lines ~120-259 — introduction, Theorem A,
  Theorem B, section 2(A) functoriality, Lemma 2.1. Read; the proofs of
  Theorems A/B were NOT read (credited input). No comparison with the
  Compositio 146 (2010) publisher version was made by me.
- ABBR I, arXiv:1303.4812v3: lines 2158-2242 (Theorem 6.18 statement, Lemma
  6.19, start of 6.18's proof) and 2435-2604 (sections 7.1-7.4, Theorem 7.4
  with full proof, Remark 7.5, Theorem 7.7 with full proof, Example 7.8
  header). Read. Corollary 6.21 was seen in use at 7.3; its statement lines
  (~2400-2433) were skimmed, not fully read. The remainder of the paper,
  including the full 6.18 proof and SGA inputs, NOT read (credited).
- Mochizuki, The Local Pro-p Anabelian Geometry of Curves: introduction
  notation and Theorem C (lines ~74-86, 205-217), Section 19 in full (lines
  5195-5314: Theorem 19.1 statement, complete proof, remarks). Read. Theorem A
  and sections 1-18 NOT read (credited; 19.1's proof invokes the earlier
  anabelian isomorphism [Mzk2]/Theorem A as a black box, as it states).
- Mochizuki-Tsujimura RNS (revised March 30, 2024): lines 118-187 (Sigma-RNS
  definition context, alternative formulation, Theorem A statement) and
  3838-3882 (Theorem 2.17 statement and its proof). Read. Proposition 2.4(iv),
  2.6 and the model-domination proof bodies NOT read by me; they are the
  source's paid interface.
- Saidi, Further Examples of Non-geometric Sections (Publ. RIMS 59, 2023):
  lines 1-90 (abstract, introduction, main-result context). Read to confirm the
  quotient comparison (metabelian / nilpotent-by-abelian, not Pi_X^Sigma).
  Proofs not read; not operative.
- Hoshi, Existence of Nongeometric Pro-p Galois Sections (RIMS1689 revised):
  abstract/claims confirmed via the retained PDF identity and bounded web
  search; body NOT read by me. Used only for the landscape statement that
  pro-p surjectivity fails; no inferential use against or for the pro-{p,ell}
  target.
- Pop-Stix arXiv:1111.1354v1, Stix period-index, Mochizuki November 15, 2010
  comments, Mochizuki Topics (Theorem 4.12 region): NOT read by me. Superseded
  or non-operative inputs for the r60 chain (the r60 proof uses March/May 2011,
  not Pop-Stix Theorem 25-27, and uses Local Pro-p 19.1, not Topics 4.12).

## Campaign records

- NEW-TEN-2026-10-14.md and AGENTS.md: read (the campaign file in large part;
  the T019S59 candidate is not yet recorded there as accepted).
- t019s59-parent/: contribution-r1-brief.txt (my brief), intake.json,
  dispatch-r1.json read. These are parent dispatch/intake records. The parallel
  proof review is recorded as running with null summary; I have read no proof
  review output and no verdict, and no proof-review directory was present in
  the campaign tree at review time.
- fresh-arithmetic-discovery-r58/original-scope.md: read (confirms a different
  target, T001U58; no contribution overlap).
- git log: two-prime lineage commits d02ca819, 049dfabf, 33052d41, 3acc119c;
  no earlier acceptance or parallel nomination of this target.
- fresh-arithmetic-discovery-r61 and other live discovery directories: not
  read; irrelevant to this review and possibly parallel work.

## Bounded primary-literature search (2026-10-18, three queries, not exhaustive)

1. "pro-Sigma section conjecture p-adic hyperbolic curve geometrically
   pro-Sigma fundamental group surjectivity" — returned Pop-Stix, Stix survey,
   toric section conjecture, a conditional Journal of Algebra result; no
   pro-{p,ell} bijectivity theorem.
2. "Hoshi nongeometric pro-p Galois sections ..." — confirmed Hoshi's negative
   pro-p answer (Publ. RIMS; RIMS1689) and its context.
3. "section conjecture geometrically pro-nilpotent OR metabelian OR two primes
   quotient ..." — confirmed nongeometric-section examples for
   metabelian/nilpotent-by-abelian quotients (Saidi et al.); no pro-{p,ell}
   bijectivity theorem.

Limits: three queries, first-page results only, no MathSciNet/zbMATH access,
no systematic arXiv listing scan. No worldwide priority or novelty conclusion
is drawn; the absence of a matching theorem in this bounded search is not
evidence of absence in the literature.

## Web/independence notes

No nested agents were started. No shared indexes, staging, commits, uploads or
publication actions. Scratch use is limited to /var/tmp for post-seal verifier
controls. Third-party bodies remain private; nothing from them is copied into
this directory.
