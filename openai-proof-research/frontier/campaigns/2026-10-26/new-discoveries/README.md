# Thirty new mathematical discoveries

Strict accepted tally: **3/30**. Earlier thirty formalization outcomes remain preserved and receive no discovery credit here.

The first accepted result resolves Gerhold–Simon Conjecture 3.2 / MathDB 352508: the sharp converse fractional-binomial inequality for all real exponents above 2. Its four-page paper, seven Lean modules with 67 declarations, stronger biased bound, coefficient optimality, independent source/mathematical/formal review and documented prior-art search are in `candidates/fractional-binomial/`. The reproducible ZIP passes byte readback, manifest checks and a fresh isolated Lean replay after extraction. Classical Gamma-ratio convexity is credited; no prior full sharp finite-sum resolution was found. The inaccessible Alzer article and the limits of priority searches are explicitly documented. All corollaries and helpers are one combined outcome.

The second accepted result proves nonconvergence for every nonempty finite all-odd randomized subtraction set, an explicitly open assertion in the source attached to MathDB 363319. Its three-page paper, actual recursively defined game, positive invariant, 37-declaration Lean certificate, independent review and extracted proof packet are in `candidates/odd-subtraction/`. The MathDB record's separate root-simplicity conjecture remains open; it is bypassed and not claimed proved. This is one combined source-question resolution.

The third accepted result refutes Kovalev's trigonometric-positivity Conjecture 1.3 / MathDB 369172 with the exact witness d=49, n=949 and t=arccos(523/527). Its three-page paper, 55-declaration complete Lean certificate, exact integer data, reproducible generator and independent review are in `candidates/trig-counterexample/`. The actual 2026 publisher PDF retains the conjecture. The different zero-free conjecture is not refuted.

The additive-minimum-side taxicab refinement (MathDB 341671) remains a separate candidate with complete proof, 68 Lean declarations, a five-page paper and independent mathematical/source/formal review. Novelty is on HOLD for the closest 2018 comparison. The earlier base-bound version and this refinement are the same candidate, never counted twice.

The complete Vandermonde proof and newer coefficient-positivity connection remain uncounted because stronger existing theorems already imply them. Known results, wording corrections, boundary cases and enumeration-only leads do not add to the tally.

Count only substantive new mathematical results after exact primary-source validation, full proof, complete Lean verification, independent adversarial review, serious documented prior-art investigation and a reproducible paper/proof packet. Never infer absolute worldwide priority from an empty search. Criteria and exclusions are in `ledger.json`; ongoing directions are in `NEXT.md`.

Research uses standard/default speed, parallel native workers and Pi GLM as requested. Agents own separate lanes; the parent integrates and accepts results. No external posting, publication or push is authorized. Upstream openai/math is pinned at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb; current accepted proof does not rely on an upstream theorem. Lean 4.34.1 and exact dependency revisions are in `pins.json`. The PDF authoring marker ran once for the thirty-paper campaign before its first manuscript.
