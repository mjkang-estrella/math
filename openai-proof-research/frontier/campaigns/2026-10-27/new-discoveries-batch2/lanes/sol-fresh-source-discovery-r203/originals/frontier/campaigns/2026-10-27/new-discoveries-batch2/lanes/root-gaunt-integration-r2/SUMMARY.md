# Gaunt lower bound: closed source endpoint, not accepted

28 October 2026. **Credit 0.** This new lane leaves the ordinary candidate and
the earlier supporting checkpoint unchanged. The independent preliminary
review remains bound to its original frozen files; it has not reviewed these
new modules. No paper, discovery packet, independent formal PASS, optimality
certificate, novelty clearance, or acceptance is claimed here.

## Exact formal endpoint

`GauntIntegral.source_conjecture_339406_lower` proves, for real n<1,
ν≥1−n+sqrt(2(1−n)) and x>0,

    x^(-ν) K_sqrt((ν+n)²−2ν−1)(x)
      < integral_(t>x) t^(-ν) K_(ν+n)(t) dt.

The statement includes the threshold equality and zero-order boundary,
negative n and arbitrary real orders. There is no residual integrability,
convexity, recurrence, derivative, or parameter-geometry hypothesis.
`besselK` is the actual classical integral

    integral_(u>0) exp(-x cosh u) cosh(νu) du,

with convergence proved. It is not an abstract function given assumed Bessel
properties. Mathlib has no canonical K used here; identification with this
standard representation is the ordinary mathematical source interpretation,
not a new Lean theorem equating two alternative implementations.

## New proved bridges

- `Recurrence`: integration by parts for exp(-x cosh u)sinh(νu), with a proved
  zero boundary at infinity, gives K_(ν+1)−K_(ν−1)=2νK_ν/x.
- `ZeroOrder`: genuine polynomial-Gaussian domination and integration by
  parts for u exp(-x cosh u) give integral u sinh(u)exp(-x cosh u)=K_0/x.
  Integrating the strict squared-order tangent gives the boundary comparison.
- `ArgumentDerivative`: differentiation under the integral has an explicit
  neighborhood-wide integrable majorant at x/2. This proves both adjacent-
  order forms of K's argument derivative.
- `TailBounds`: an exponential bound for every positive lower endpoint
  proves weighted-tail integrability and the zero boundary at infinity.
- `WeightedComparison`: the positive-order chord and zero-order tangent are
  assembled, the genuine derivative integrated by FTC, and strictness is
  witnessed on an interval of positive measure.
- `SourceEndpoint`: the inclusive literal source threshold implies all
  comparison premises, internally and without narrowing n's real domain.

The two starting modules were copied byte-for-byte from root-gaunt-formal-r1.
All new analysis concerns the same prospective outcome; helpers receive no
separate credit.

## Fresh verification actually performed

    python3 verify_component.py

**PASS: 8 modules / 56 declarations**, warnings as errors; all eight module
logs are empty. The verifier asserts the absolute Lean 4.34.1 binary hash and
version, all eight package revisions and clean dependency trees. It copies
only source files into a fresh temporary directory and consumes no local
prebuilt artifacts. All 56 actual type and axiom reports in
`verification/Checks.log` were read by root. They use only propext,
Classical.choice and Quot.sound. Forbidden proof shortcuts are absent.

Receipt: `verification/audit.json`; Checks.log SHA-256:
`5662d5947b6ae4fd0766f0edc981f11e3b41f3093fca6989d699ba5906dfb1be`.
This is a source-copy component replay, not a final discovery archive replay.

## Remaining gates

The ordinary proof also claims optimality of the absolute order. **Its
converse is not in this Lean certificate.** A full classification must not be
advertised as formalized. The lower-bound theorem is complete in the scope
printed above. Source journal-body comparison, classical squared-order
convexity subsumption and substantive eligibility remain with the independent
review. If those gates survive, root must decide the final certified scope,
obtain an independent review of the actual integrated bytes, prepare the
paper and deterministic packet, and replay the final extraction before credit.

Accepted count remains 2/30 additional, 32/60 total. No external action.
