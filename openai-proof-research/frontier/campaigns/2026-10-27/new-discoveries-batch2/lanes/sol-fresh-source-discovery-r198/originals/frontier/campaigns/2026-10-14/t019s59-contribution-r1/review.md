# T019S59 contribution review r1 — verdict: TECHNICAL

Role: contribution/eligibility review of the frozen author packet
`frontier/campaigns/2026-10-14/fresh-arithmetic-discovery-r60/`, conditional on
correctness. The separate proof gate is running in parallel; I have not seen its
output or any parallel review directory, and this verdict does not depend on it.
Correctness is assumed only for the purpose of this classification; nothing here
is a proof PASS.

Verdict: **TECHNICAL** for the full unchanged target (every prime p, every odd
prime ell != p, every finite k/Q_p, every smooth proper geometrically connected
X/k of genus >= 2; bijectivity of X(k) with continuous sections of the
geometrically pro-{p,ell} quotient Pi_X^Sigma -> G_k modulo Delta^Sigma, full
arithmetic G_k retained). Not SUBSTANTIAL, not DUPLICATE, not INELIGIBLE, not
BLOCKED. If the proof gate fails, this classification is moot; if it passes, the
result should be retained as technical research support, not counted as a
frontier result.

## Packet authentication (identity only, not mathematics)

All seven brief-supplied external anchors reproduced exactly by local SHA256:
manifest.json `6aa7aecf500b89cdeedd085202543c7170f40b125dcb29f6ffa1462499c75e0b`,
original-scope.md `22e7466e2699457a0ee39e31f5ac1b982527f1a7b9115b2fa1c3bc7377a73d95`,
candidate-proof.md `49d0bb4e17ec22ae667f889dcc60db10615d25c906a2a1421e85fd33e960aab5`,
cyclic-collars.md `1e54265525bc8675f38e131bdbd0d3246aa86aad50daf13583dd8c2b093f986b`,
comparison.md `c89f87343b4e2566e33754108cfee52ee604ff92fe72da69c98c4d95ed62ed6a`,
reading-limits.md `5dc4094d47368fdb9b1aa017055e7d53ce4095a3ba1a67176bdc18349021a412`,
canonical preprints-tree `eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b`
(13223 entries, truncated=false). The packet verifier, read before execution, ran
as `python3 -I verify.py 6aa7aecf...c75e0b` and returned
PASS_EXACT_INVENTORY (72 files, 17 directories, 47 family entries, 32 source
blobs, 12 primary bodies). The five remaining public files hash-match the parent
intake record. These are byte-identity checks only.

## What I independently read (operative interfaces)

- Source manuscript (October 6, 2026), sections 01-07 in full: the completion
  theorem (K^sep inside the completion of the full etale tower), patching
  proposition and point-transfer/horizontal-closure lemmas, stable-edge-root and
  etale-collars lemmas, arbitrary-roots proposition, realization proof, and the
  full-section endgame (decomposition-group comparison, no-rank-one-section
  lemma, type-2h analysis, Jacobian Kummer injectivity).
- Exterior-sheet companion (September 24): section 01 statement in full
  (sections 02-04 not read; non-operative here).
- Mochizuki, March 3, 2011 note: full 6-page body, including (*CSC), (*LSC),
  the pro-Sigma tempered/profinite comparison (*PTS), and (5) systems of
  section-fixed vertices/edges. It explicitly records as open (Q1)/(Q2) whether
  this yields Pop-Stix-strength conclusions.
- Mochizuki, May 2, 2011 note: full 4-page body; (*val) constructs compatible
  Im(s)-invariant valuations from such systems, with the smooth-point limit
  valuation and irrational P-ray cases read in the actual proof.
- Pop, MPIM 2007/102: introduction, Theorems A and B statements, and section
  2(A) Z/p-derived-series functoriality (extracted lines ~120-259). Theorem A:
  for finite k/Q_p containing mu_p and a complete smooth geometrically integral
  curve, liftable sections of the elementary p-abelian quotient are exactly the
  bouquets of point sections, with uniqueness. Its proof was not audited.
- ABBR I (arXiv:1303.4812v3): Theorem 6.18 statement, Corollary 6.21 in use,
  sections 7.1-7.4 including Theorem 7.4 with full proof and Remark 7.5, and
  Theorem 7.7 with its loop-subdivision proof. Confirmed: 7.4(2) identifies the
  X-automorphism group of a lift with the stabilizer of the gluing datum under
  the conjugation action (7.3.1), and Remark 7.5/Example 7.8 confirm
  automorphisms do not lift automatically.
- Mochizuki, Local Pro-p: Theorem C statement (= Theorem 19.1; sub-p-adic K,
  hyperbolic curve, injectivity of K-points into pro-p section classes, full
  Gamma_K retained) and the entire Section 19 proof (diagonal-complement family
  and pro-p anabelian isomorphism), including the remark that a Jacobian Kummer
  argument suffices for the profinite version. Theorem A's ~100-page proof not
  audited.
- Mochizuki-Tsujimura RNS (revised March 30, 2024): introduction definitions
  and Theorem A statement, and Theorem 2.17 statement with its short proof.
  Confirmed the printed hypothesis: Sigma of cardinality >= 2 containing p.
  Hence Sigma={p,ell} is a permitted parameter choice, not a new input.
- r59 historical packet (author checkpoint): proof-attempts.md in full,
  including the Brauer repair and the restricted Pop-Stix adaptation plan, both
  explicitly unused in r60.
- Saidi 2023 (Publ. RIMS 59): introduction/statement (nongeometric sections
  for geometrically metabelian and nilpotent-by-abelian quotients). Confirmed
  these quotients are not Pi_X^Sigma.
- Campaign records: r58 scope (different target, T001U58), parent
  intake/dispatch/contribution-brief for t019s59 (dispatch records, not review
  verdicts), git history of the two-prime lineage (four commits, r59 -> r60;
  no prior campaign acceptance or parallel nomination of this target).

Exact reading limits, including unread dependencies, are in `reading-log.md`.

## The contribution question

The brief asks whether the fixed-gluing/torsor normal-closure control is a new
substantial mechanism or an elementary robust transfer once the stronger ABBR
classification and the Mochizuki/Pop primary results are credited. I read the
operative source operations and the closest primary results to answer this
directly.

Findings on the boundary of what is paid:

1. The source's completion theorem is proved for the FULL etale tower. Its
   Sigma-restriction (B inside the completion of E_X) is NOT a formal
   consequence: the restricted tower is smaller, so every cover constructed in
   the source's two collar stages must be re-shown to have Sigma-group normal
   closure. This rerun is the candidate's core residual work. Conversely, the
   source's full section theorem does not cover quotient sections (a
   Pi_X^Sigma-section need not lift to pi_1(X)); the packet never claims
   otherwise.
2. Every analytic input in that rerun is source-paid at its printed interface:
   local normal form, all-sheet patching, point transfer, horizontal-closure,
   annular-unit factorization, slope-one character, period-coset gluing,
   log/exp margins with D > v_p(m) + 1/(p-1), irrational-level and
   compact-complement arguments. No new estimate appears anywhere in the
   candidate.
3. The two genuinely candidate-side geometric facts are: (a) the source's
   degree-ell tame covering of a metrized complex can be built carrying a
   cyclic C_ell action whose gluing datum is fixed, so that ABBR 7.4(2) makes
   the lifted cover C_ell-Galois; (b) every subsequent cover in the pipeline
   (patched Gamma-torsor components, Jacobian [m_b]-torsor components with m_b
   a Sigma-integer, composita, normal closures) stays a Sigma-group by
   subgroup/product/extension closure.

Assessment of (a): the construction reuses the source's own residue covers
(y^ell = f with divisor P - Q + ell E) with a coherent circuit orientation; the
fixed-gluing check is the inverse-tangent-character observation at the two
circuit marks, the annular identification v = b/u commuting with the action,
transport on free edge orbits, and compatibility with 7.7's own P1 loop
subdivision. Each step is elementary, and the classification theorem used is
designed precisely to reduce automorphism lifting to such a stabilizer check.
This is exactly the "stronger ABBR interface credited, elementary transfer
remaining" pattern named in the brief. The author's own note agrees ("the
action compatibility is elementary once ABBR's stronger classification theorem
is used").

Assessment of (b): closure of finite Sigma-groups under subgroups, products and
extensions, plus the standard fact that a connected component of a Gamma-torsor
is Galois with subgroup monodromy. First-course profinite group theory, applied
carefully. The packet's discipline of never inferring normal-closure control
from degree alone is care, not a new mechanism.

## Operation-level reduction (TECHNICAL justification, all quantifiers retained)

For every p, every odd ell != p, every finite k/Q_p, every genus >= 2 X/k:

1. Sigma-bookkeeping (candidate section 1): subgroup/product/extension closure
   of finite Sigma-groups; open geometric subgroups of Pi_X^Sigma are pro-Sigma
   completed towers (finite conjugate-kernel intersection). Elementary; no
   quantifier lost (used for all section neighborhoods Y, which retain
   genus >= 2 by etale Riemann-Hurwitz).
2. Cyclic collars: source lem:stable-edge-root construction + ABBR 7.7
   existence + 7.4(2) stabilizer = Galois control; residual work is the
   character/orientation bookkeeping above. ell odd >= 3 matches the source's
   stability needs; tame degree ell avoids p; finitely many annuli by the
   source's fibre-product argument.
3. Disk-to-stable collars: RNS Theorem A/2.17 with Sigma={p,ell} (hypotheses
   verified: cardinality >= 2, p in Sigma) through the source's model-domination
   interface; irrational-level/compact-complement argument unchanged. Residual
   work: choosing Sigma.
4. First-stage patching: source prop:patching/point-transfer/horizontal-closure
   at printed interfaces, with Gamma a Sigma-group; residual work is
   equivariant trivialization and the row-1 closure checks.
5. Arbitrary branch orders: every m_b is automatically a Sigma-integer
   (e_c divides |Gamma|); source prop:arbitrary-roots applies for every such
   m_b (no prime-to-p condition, D_b > v_p(m_b) + 1/(p-1)); the auxiliary
   cover's normal closure is a Sigma-group because J_Z[m_b] is an abelian
   Sigma-group and the Z-cover is cyclic of degree ell. Horizontal indices
   dividing ell are the source's own conclusion.
6. B inside H and D(B/K) = D(E_X/K): the source's realization proof and its
   decomposition-group corollary rerun verbatim on the restricted tower once
   rows 2-5 supply membership; prolongation transitivity and the
   dense-subfield continuity argument need no change.
7. Quotient localization: Mochizuki March (4)-(5) and May (*val) are stated for
   exactly this quotient (arbitrary mixed-characteristic CDVF, Sigma containing
   ell != p, proper hyperbolic curve, geometrically pro-Sigma tower). Residual
   work: ell-cyclotomic fullness of finite k/Q_p (Frobenius q > 1 has nonzero
   ell-adic logarithm after a finite power) — a textbook computation.
8. Rank-one alternative: row 6 lifts the section to G_B; no new content.
9. Birational point: over k' = k(mu_p), K'_2 lies in B (pro-p geometric
   groups), so the kernel of G_{K'} -> Gal(B/K') lies in the second closed
   elementary p-derived subgroup; Pop section 2(A) functoriality (read at the
   primary) makes the restricted section a liftable elementary p-abelian
   section; Pop Theorem A (mu_p in k', smooth proper geometrically integral
   curve — hypotheses match, p = 2 included in the retained statement) gives a
   unique k'-point; semilinear conjugation plus uniqueness descends it to k.
   Residual work: elementary derived-series bookkeeping and a standard descent.
10. All sections geometric: classical finite-neighborhood compactness over the
    compact p-adic X(k), the same criterion used by the source and Stix;
    residual work is spelling out finite compatible fibers.
11. Injectivity: project Sigma-section classes to the geometrically pro-p
    quotient and cite Theorem C/19.1 (sub-p-adic hypothesis holds for finite
    k/Q_p). One-line reduction; the actual 19.1 proof read uses the
    diagonal-complement family, so the candidate correctly avoids restricting
    the source's all-n Jacobian test to Sigma.

Every row is a paid interface, a textbook check, or elementary bookkeeping. No
row changes a quantifier, adds a hypothesis (no rational point, good reduction,
genus choice, constant extension, or full-tower lift is assumed), or
substitutes a subclass theorem. The assembly is long and coherent, but length
and theorem strength are not substantiality.

## DUPLICATE / INELIGIBLE / BLOCKED screening

- Not DUPLICATE within the campaign: the two-prime lineage is r59 -> r60 only;
  no accepted result (R023-R039) or other active candidate covers this target;
  the r58 round was a different target. No self-awarded novelty or priority
  claim appears in the packet; comparison.md already disclaims substantiality.
- Not DUPLICATE against bounded literature: the March 2011 note states the
  vertex/edge localization and explicitly leaves Pop-Stix-strength conclusions
  open ((Q1)/(Q2)); the May 2011 note produces the valuations and stops; Pop's
  Theorem A is birational, liftable-sections-only; the source's full section
  theorem does not formally imply the quotient version. Bounded web searches
  (2026-10-18: pro-Sigma section conjecture surjectivity; Hoshi nongeometric
  pro-p sections; metabelian/nilpotent quotient sections) found no published
  bijectivity theorem for the geometrically pro-{p,ell} quotient with full G_k.
  This is a bounded search, not a priority certification; a matching theorem
  elsewhere would take precedence.
- No conflict with known counterexamples: Hoshi's nongeometric pro-p sections
  and Saidi's nongeometric metabelian/prime-to-p sections concern quotients
  that are not Pi_X^Sigma (a pro-p section does not pull back to a
  pro-{p,ell} section; the maps go the other way). The candidate's claim is
  not refuted by them, and I make no such confusion in either direction.
- Not INELIGIBLE: the packet addresses the full unchanged scope with honest
  credit boundaries and explicit reading limits.
- Not BLOCKED: all operative interfaces were available and read.

## REQUIRED objections

None against the packet's claims as written: the packet claims no substantiality,
no novelty, no priority, and no acceptance, and its credit boundaries match what
I read at the primaries. The following are REQUIRED conditions on any downstream
disposition, not objections to the text:

R1. Do not count or accept T019S59 as a campaign frontier result on the basis
    of this packet, regardless of the proof-gate outcome; the contribution is
    TECHNICAL for the full unchanged target.
R2. Any retained manuscript or summary must keep the paid boundaries exactly:
    all analytic estimates and both collar stages to the pinned source;
    Sigma-RNS as a parameter choice inside Mochizuki-Tsujimura Theorem A/2.17;
    automorphism lifting as the ABBR I 7.4(2) stabilizer criterion (not
    automatic lifting); quotient localization to the March 3, 2011 (4)-(5) and
    May 2, 2011 (*val) notes; the rational-point criterion to Pop MPIM
    2007/102 Theorem A; injectivity to Mochizuki Theorem C/19.1; neighborhood
    compactness as classical. The r59 Brauer repair and restricted Pop-Stix
    adaptation remain unused and earn no credit, as the packet already states.
R3. Retain the version caveat: the Pop input is the retained MPIM 2007/102
    body; equivalence with the Compositio 2010 publisher version was not
    verified by the author and was not verified here.
R4. No worldwide novelty or priority inference from the bounded searches
    recorded here or in the packet.

## Optional items

O1. The equivariant-gluing passage (fixed gluing datum under the conjugation
    action (7.3.1)) is a clean worked example of ABBR 7.4(2) usage and could
    have expository value; that is presentation, not contribution.
O2. If the proof gate passes, the theorem would be a genuine new-to-bounded-
    literature statement sitting strictly between quotients where the section
    conjecture fails (pro-p; metabelian; prime-to-p) and the stipulated full
    theorem; that observation concerns the statement's interest, not the
    contribution class.
O3. The candidate's theorem, if correct, implies Hoshi-type nongeometric pro-p
    sections never lift to pro-{p,ell} sections; worth one remark in any
    manuscript, as context only.

## Seal

This review directory (`review.md`, `reading-log.md`, `verify.py`,
`manifest.json`) is sealed by an externally supplied SHA256 of manifest.json;
`verify.py` (adapted from the credited r40/r58/r59 audited helper lineage)
walks the directory read-only, rejects symlinks, hardlinks and other nonregular
entries, rejects nested manifests, and requires an exact file and directory
inventory match against the externally hashed manifest. Positive and negative
controls (positive copy, wrong anchor, malformed anchor, changed file, extra
entry, symlink) are run on a copy under /var/tmp after sealing so the sealed
payload is not mutated by its own receipt; control outcomes and the external
seal hash are reported in my final message to the parent.
