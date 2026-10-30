# Candidate: full surviving arcsinh parameter-concavity conjecture

Credit0. Complete ordinary proof in PROOF.md; exact source: Yin–Huang–Wang–Lin
JMI13(3)(2019) Conjecture5.1, printed847. It asks p>1, 0<x<1, and is distinct
from merely refuting the original all-p>0 wording of MathDB325512. The old
small-p witness stays uncredited. At most ONE combined family.

The pointwise diagonal-parameter kernel proof uses the classical binary
entropy bound H<=log2. It gives strict concavity on p>log2/2 for every x>0.
Neither entropy, derivative helpers, extension to x>1 nor Turan consequence
gets separate credit. The strongest objection is possible routine generic
reciprocal-lp-norm subsumption; independent eligibility review is required.

Lean full-source endpoint: ArcsinhPositive.source_conjecture :
ArcsinhPositive.SourceConjecture, closed. Stronger endpoint:
sourceArcsinh_strictConcaveOn (hx:0<x), literal interval integral and real
powers, p>log2/2. Five modules/19 declarations, warningsAsError; all axiom
reports standard3. Fresh isolated replay via python3 verify_candidate.py
PASS; all actual reports personally inspected by root. No paper or packet.

Exact symbolic identities:3; numerical derivative diagnostics:36 and actual
integral midpoint diagnostics:18 pass. One transient numerical-check failure
was Python int-to-float power evaluation in ff(1,2), fixed by converting all
inputs to mpmath values before evaluation; the symbolic identity was zero
throughout. No numerical conclusion is used in the universal proof.

Source PDF refetched byte-identically and root visually read published
Conjecture5.1 (PDF15). Eq1.14 was read in text and separately rendered on
PDF2. Karp2024 journal bodies read at the relevant corollaries and Theorem4:
forward separate-parameter functions, not the inverse diagonal integral.
18 OpenAlex citing records retained; not all bodies read. RACSAM2025 full
body unread (subscription content), and2026 successor body unread, though
source-author attribution and successor abstract indicate sine/tangent
Wilker-type question. No acceptance-grade novelty clearance claimed.

Await independent review before manuscript investment or counting.
