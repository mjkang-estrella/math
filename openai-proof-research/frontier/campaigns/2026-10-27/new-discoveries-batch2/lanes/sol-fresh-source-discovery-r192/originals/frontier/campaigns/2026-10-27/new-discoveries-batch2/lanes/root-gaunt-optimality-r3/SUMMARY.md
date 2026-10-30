# Full Gaunt tail classification: formal completion, credit 0

28 October 2026. **UNACCEPTED.** This lane completes both directions of the
ordinary candidate root-gaunt-integral-r16. The independent preliminary
review remains bound to its older frozen bytes. No independent integrated
review, published-body clearance, novelty clearance, substantive eligibility
decision, acceptance, or public submission is asserted.

## Exact claim

For every real n<1 and ν≥1−n+sqrt(2(1−n)), let
δ=sqrt((ν+n)²−2ν−1). For every real order r,

    [∀ x>0, x^(-ν)K_r(x) < ∫_(t>x) t^(-ν)K_(ν+n)(t)dt]
        iff |r|≤δ.

Every larger absolute order fails for all sufficiently large x. The strict
lower bound includes the threshold equality δ=0, negative n and real n.
The closed Lean endpoint is
`GauntIntegral.source_full_classification_339406 : SourceClaim339406Full`.
Its type has no residual analytic, frame, asymptotic or existence premise.

K is defined by its actual classical representation
∫_(u>0) exp(-x cosh u)cosh(ru)du, as in the actual DLMF10.32.9 body read and
archived here. Convergence and all special-function properties used in the
proof are proved from that integral. No second implementation of K is used
or equated silently.

## What changed since the 56-declaration checkpoint

The earlier eight modules are byte-identical. Six new modules add:

1. A twice-differentiable local-sign argument from a negative second jet.
2. A complete Laplace domination estimate, including both integration tails.
3. The literal three-cosh kernel, its genuine derivatives and exact negative
   second jet whenever r>δ.
4. Eventual negativity of the actual Bessel differential comparison.
5. Integration to infinity of that signed comparison and the eventual strict
   failure at larger orders.
6. Monotonicity in absolute order and the full literal iff classification.

The ordinary alternative proof is in OPTIMALITY-ROUTE.md. Unlike the
historical ordinary proof, the certificate assumes no fixed-order Bessel
asymptotic formula. All auxiliary tools remain uncredited classical analysis.
This is one prospective family, never separate credits for the bound,
optimality, parameter values or helper lemmas.

## Verification and manuscript

    python3 verify_candidate.py

Fresh source-only replay **PASS:14 modules/80 declarations**, with warnings as
errors, all module logs empty and only propext/Classical.choice/Quot.sound.
The absolute Lean binary SHA/version, eight package revisions and clean
dependency trees are asserted. No local prebuilt artifacts are copied into
the replay. Root read all 80 actual type/axiom reports; the first 56 are
byte-identical to the already inspected checkpoint reports. Checks.log SHA:
`efe7eb6d6b9b8e91b0fd79d25a89cd55e53ae52d004a29fed1264affef2a8e30`.

The three-page manuscript main.tex/paper.pdf states exactly this theorem and
the eventual strict converse. All three rendered pages were read; no
overfull/underfull boxes, undefined references or clipping were found. The
paper explicitly retains pending source/novelty/independent-review status.
Its source statement is Gaunt1806.00524v2 Conjecture2.4/Remark2.5, not an
unread claim that the journal body was checked. See paper-qa.json.

## Remaining acceptance gates

The original source journal-body and classical-subsumption/novelty questions
are open. In particular, a pre-existing squared-order convexity theorem or a
same-shape Bessel inequality might make the result a routine corollary. That
objection is not cleared by Lean success, the short proof or an open MathDB
label. A new integrated independent review must inspect the actual final
sources, manuscript and extracted packet before acceptance. Any packet built
in this lane is an unaccepted review artifact, not a public submission.

Accepted tally remains 2/30 additional, 32/60 total. No external action.
