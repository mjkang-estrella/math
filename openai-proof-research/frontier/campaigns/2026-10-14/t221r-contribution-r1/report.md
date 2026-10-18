# T221R independent contribution/eligibility review r1

Reviewer role: independent contribution and eligibility review of the full
frozen T221R candidate. MIT for this file. No third-party text is copied;
locators point to the private bodies inside the frozen author packet.

## Verdict

**TECHNICAL.** T221R does not count toward NEW-TEN. No scope shrink is
proposed, and no shrunken statement would count.

The verdict assumes the author proof is correct. It is not a proof review.
It does not use, and was written without reading, the parallel proof
review `t221r-proof-r1/`. The 13/20 target gave no presumption either way.

## Frozen object reviewed

Packet: `frontier/campaigns/2026-10-14/fresh-analytic-discovery-r44/`
(unchanged before and after this review).

| File | SHA256 |
|---|---|
| manifest.json | c288940c8c88f67a7374d998a7c49d822f64000abb981517303f1bf4af9739c6 |
| verify.py | 22bc163b277aa160698b01a7d3a4104e3025c7a17cdd51274ddbbb59f2c38b82 |
| controls.py | 93425bee00ffa83114837541a0961c7adc7c6dd7c24781b6f17c226539d51583 |
| proof.md | c2d6631489bc3e2c31dfd2eb986a1987ff477b55c3a837556e3a0923a67fefa0 |
| original-scope.txt | 26312b8fd6fb6a4bacb27085f0b46b760cc8f884754bed03e937c1b40328693c |
| reading-and-comparison.md | 11d63dd5cfbf1a6b63a0fdbcadc7dda31a4f0c933c0ea3462d4843678ddebc1d |
| sources/preprints-tree.json | eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b |

Identity results (byte identity only, recorded in
`review-checks-result.json`): author verifier PASS_INTEGRITY_ONLY with 62
files, 10 directories, 26 pinned blobs and 6 primary pairs; wrong anchor
rejected. Independently of the author receipts, all 16 copied family-221
files and all 10 copied Solomon–Yau files have the canonical Git blob SHA of
the complete pinned tree (`truncated: false`); only each family's
`paper.pdf` is not copied; there are no extra local files. The author's 13
controls were also replayed earlier on an owned copy (all PASS). The
copied controls in this packet add real source and primary mutations,
including resealed manifests, which the author verifier rejects through the
Git-blob and primary-receipt checks.

Target (original-scope.txt): for d≥3, β>0, symmetric integrable J,
integrable H, uniform simple d-regular graphs, n⁻¹E log Z_n converges to the
infimum over all finite depths of the family-221 hierarchy functional with
site count d and edge coefficient d/2.

## Theorem-level position

- **Family 221** (pinned): proves the finite-hierarchy formula for its
  Poisson-type diluted models. Its introduction (introduction.tex l.40–62)
  cites Coja-Oghlan–Perkins for regular graphs as a different
  (kernel) description and Concetti's regular-graph bound as conjectural
  equality. It makes no regular-graph claim. T221R is therefore not a
  pinned-source duplicate.
- **Coja-Oghlan–Perkins, arXiv:1808.03440v1**: exact pressure for random
  regular factor graphs as a variational formula over kernels; its lower
  bound (§6, l.2282) does not need POS. Different description of the
  state; it does not give the finite hierarchy.
- **Lelarge–Oulamara, arXiv:1708.02457v2**: the regular finite-depth upper
  bound (Theorem 3). Tightness is called a challenging open problem
  (l.97–100, stated in their independent-set application).
- **Concetti, arXiv:2508.17049v1**: for the zero-field Rademacher model on
  regular graphs, whether finite-K equality holds is open (l.180–181); the
  full-RSB principle is the main conjecture (l.270–275).

So, if correct, the theorem is new to this project and answers a question
the comparators describe as open. That is a statement about the
conclusion. Under the NEW-TEN criteria, credit depends on whether new
operations beyond routine transfer were needed. The ledger below finds
that every load-bearing operation is paid by the pinned source or by a
named antecedent. The residual is mesoscopic bookkeeping and elementary
estimates.

No worldwide novelty is claimed or refuted. No external literature search
was run in this review (see reading-limits.md).

## Operation-by-operation credit ledger

Locators: source = pinned family 221 `build/sections/*.tex`; COP, LO,
Concetti, FLT, Janson = `private/primary/*.txt` line numbers in the frozen
packet; proof = proof.md sections.

| # | Operation (proof locus) | Paid by | Locator | Residual |
|---|---|---|---|---|
| 1 | Regular finite-depth upper bound (§1) | LO | Theorem 3 and its §§4–6 | none |
| 2 | Configuration model with a pool of holes; uniform matching deletion; (2.1) comparison with the full graph (§2) | COP cavity reservoir; standard matching facts | COP §6.1–6.2, Lemma 6.4 l.2377ff, (6.2) l.2397 | pool size q grows with n instead of fixed ω: parameter change |
| 3 | Var X₀ ≤ C(n+s) by exposure martingale and Efron–Stein (§2, (2.2)) | standard | — | routine |
| 4 | Bond completion as a tilted law, W = M_d/E M_d (§3, (3.1)) | COP recognizes the completion law as tilted by the number of extensions | COP l.2465–2468 | explicit inverse-history count: small |
| 5 | Var W = O((q+1)/n²) by counting (3.2)–(3.4); Cauchy–Schwarz (3.5); exact E M_d (3.6, parent-side) | elementary second moments; COP controls the same tilt by total variation at fixed ω | COP Lemma 6.7 l.2667 | covariance bound in place of TV×n: technical, elementary |
| 6 | Star completion, exact conditional resampling coupling with O(q/n) expected edits (§4) | COP star completion and a coupling differing in at most 2d constraints; switchings are standard | COP Lemma 6.4 l.2370–2380 and its proof | exactness of the switch with growing q: technical |
| 7 | Perturbation repair by Poisson thinning (§4, (4.1)) | FLT puts the perturbations on degree-deficient sites; thinning standard | FLT l.817–820, l.943–945 | routine |
| 8 | Increment formula (4.2); insertion recursion; collision O(1/q) | source tree:insertion; COP collision bound | trees.tex l.84; COP l.2576–2578 | routine |
| 9 | Bad indices from q-jumps; parity classes; telescoping (§4, §6) | elementary | — | bookkeeping |
| 10 | Score concentration with s_n=n^{3/4}, ρ=n^{−1/8} (§5, (5.2)) | source pert:concentration | perturbations.tex l.96–100 | exponent choice |
| 11 | Palm/prescribed-tree identities averaged over the pool I (§5, (5.1)) | source pert:palm; FLT multi-overlap identities over cavity-weighted coordinates on regular graphs | perturbations.tex l.350ff; FLT §VI, l.817–820 | notation: the source proofs are site-agnostic |
| 12 | Decorrelation in R^I (§5, (5.3)) | source states it uses only the identities and tree sampling rules | decorrelation.tex l.5–10, decor:overlap-concentration l.64 | none |
| 13 | Parameter selection with low increments (§6) | source selection argument | comparison.tex l.13 (comp:low-increments) | sparse bad-index adjustment only |
| 14 | Encoding, pattern comparison, insertion comparison, log expansion, regular shapes (§7) | source | comparison.tex l.19, l.87, l.160; trees.tex l.224, l.469 | none |
| 15 | Simple graphs (§8) | Janson Theorem 7.1; Cauchy–Schwarz | Janson Thm 7.1 | none |
| 16 | Integrable disorder by truncation (§8, (8.1)) | source stability lemma pattern | reduction.tex l.9–22 | none |

## Author residual and why it is TECHNICAL

The author-added material (proof.md §9) is: a mesoscopic pool
q = n^{0.9} with perturbation intensity s = n^{0.75}; the explicit tilt W and
its variance bound; the exact star resampling coupling; perturbation
repair; and sparse q-jump and parity bookkeeping.

1. The idea of opening a cavity reservoir in a regular graph, filling it by
   bonds or stars, and coupling the two with bounded edits is COP §6. COP
   already identifies the tilted completion law.
2. The idea of placing the perturbations on the degree-deficient sites, so
   that the overlap identities hold over cavity-weighted coordinates, is
   FLT §VI.
3. The source's decorrelation and comparison steps are explicitly stated
   to depend only on the identities and the tree rules
   (decorrelation.tex l.8–9). Moving them from all N sites to the pool I is
   the substitution the source's own abstraction permits.
4. What remains is a choice of growth rates for q and s that lets one
   sequence satisfy the source's selection argument, rather than COP's
   order of limits (n first, then ω). The estimates needed for that choice
   are elementary second-moment counts and couplings.

The combination does not appear in any body read for this review, and the
fit is careful. But each component operation is paid, and the residual is
routine matching-and-variance work. That is the definition of TECHNICAL
used by this project, not SUBSTANTIAL.

Not DUPLICATE: no pinned manuscript, companion, or project record claims
the regular-graph finite-hierarchy formula (see reading-limits.md).
Not INELIGIBLE: the scope was frozen before the full proof was assembled,
and parent assistance (the exact E M_d normalization, commit 3310a376) is
disclosed in proof.md §3.
Not BLOCKED: every load-bearing body needed for the ledger was available
and read at the operative locators.

## Required objections

R1. The author contribution statement (proof.md §9) credits the
mesoscopic pool and the localized perturbation interface to the author. Any
record must also credit FLT §VI (perturbations on degree-deficient sites
with cavity-weighted overlap identities, l.817–820) as the antecedent of
the localized interface, and COP l.2465–2468 for recognizing the tilted
completion law. reading-and-comparison.md cites neither precisely.

R2. Any record must label T221R TECHNICAL with no NEW-TEN count, and must
not call it new to the literature. Absence of search hits is not novelty.

R3. Consequences beyond the frozen scope are not credited. In particular
Concetti's §10 relation between the full-RSB functional and the
finite-level infimum ((10.64)–(10.65)) was noted but not checked here. A
claim that T221R implies Concetti's conjecture (1.26) for his model needs
its own scope and review.

R4. This verdict assumes proof correctness and does not replace the
separate proof review gate.

## Optional objections

O1. The author verifier does not reject a symlinked ancestor of the packet
root. The copied control `ancestor_symlink_observed` shows it accepts one.
It does reject a symlinked root.

O2. The author `controls.py` creates its temporary copies inside the
packet root. An interrupted run leaves a `.controls-*` directory that
breaks the inventory. Its controls do not mutate source or primary files;
the controls here do.

O3. In the author verifier, a receipt path absent from the tree raises
KeyError, which escapes the caught exception list. The exit code is still
nonzero, so this is cosmetic.

O4. LO's open-problem sentence (l.97–100) is made in their
independent-set application. A citation should state that context.

O5. The packet includes `nifa2026` and Solomon–Yau files that belong to the
unrelated screen-349. They do not affect T221R but enlarge the packet.

## Scope-shrink statement

None proposed. The bounded-disorder configuration-model case uses the same
operations 1–14, and each author-residual estimate on its own is a
routine lemma. No smaller statement would count.

## Packet

Files: report.md, reading-limits.md, review-checks.py,
review-checks-result.json, verify.py, manifest.json. The verifier needs
external anchors for manifest.json and verify.py, rejects symlinks
(payload, root and ancestors), hardlinks and nonregular files, and with
`--repo` rechecks the author anchors and the canonical family-221 blob
inventory. `review-checks.py --own` runs copied mutation controls against
this verifier.
